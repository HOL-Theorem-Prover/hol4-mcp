#!/usr/bin/env python3
"""HOL4 MCP Server - provides theorem prover interaction tools.

Sessions are in-memory only. They survive within a single MCP server lifetime
(including across Claude context handoffs) but not across server restarts.
"""

import asyncio
import atexit
import hashlib
import inspect
import json
import os
import re
import signal
import sys
import time
from dataclasses import dataclass, field
from contextlib import asynccontextmanager
from datetime import datetime
from functools import wraps
from pathlib import Path
from typing import Optional
from weakref import WeakValueDictionary

import anyio

from .build_coordination import build_claims, claim_from_graph

from . import _mcp_cancel_patch  # noqa: F401 — patches mcp SDK on import
from fastmcp import FastMCP

from .hol_session import HOLSession, HOLDIR, escape_sml_string
from .hol_cursor import FileProofCursor, StateAtResult, _try_find_json_line
from .hol_file_parser import (
    step_line_numbers, format_steps, format_step_context,
    step_text_start, elide_long_text, suspension_base, resume_header_problems,
)
from .quote_check import quote_diagnosis_lines
from .build_evidence import traced_build, build_failure_heading
from . import build_coordination as coordination
from . import budgets


DEFAULT_MAX_OUTPUT = 4096

# main() may override the first two from the CLI.
TACTIC_TIMEOUT = budgets.TACTIC_TIMEOUT
STATE_AT_TIMEOUT = budgets.STATE_AT_TIMEOUT
MAX_STATE_AT_TIMEOUT = budgets.MAX_STATE_AT_TIMEOUT


def _budget_doc(function):
    """Fill the `{NAME}` budget placeholders of a tool docstring."""
    doc = function.__doc__
    for name in ("STATE_AT_TIMEOUT", "HOLMAKE_TIMEOUT", "MAX_HOLMAKE_TIMEOUT",
                 "DETACHED_DISCOVERY_TIMEOUT"):
        doc = doc.replace("{" + name + "}", f"{getattr(budgets, name):g}")
    function.__doc__ = doc
    return function


class _SessionOperation:
    def __init__(self):
        self.lock = asyncio.Lock()
        self.owner = None
        self.tool = None    # the holder's tool name
        # Why a control tool cancelled the holder: "interrupt", "stop" or
        # "restart"; None for no cancel or a client's own.
        self.intent = None
        # The holder is in its shielded recovery: another cancel would be
        # thrown into it, so a control tool only waits.
        self.recovering = False


class _Interrupted(Exception):
    """A guarded call that a control tool cancelled. ``state`` is what its
    recovery left: "recovered", "busy" or "stopped"."""

    def __init__(self, state: str, intent: str):
        super().__init__(state, intent)
        self.state = state
        self.intent = intent


def _cancelled_call_text(tool: str, state: str, intent: str) -> str:
    """What a call cancelled by hol_interrupt / hol_stop / hol_restart returns."""
    rerun = "This is not a HOL verdict: re-run the call once the cause is fixed."
    if intent in ("stop", "restart"):
        return (f"STOPPED: hol_{intent} ended the session under this {tool} call; "
                f"the next call restarts HOL and reloads the prefix. {rerun}")
    if state == "busy":
        return (f"INTERRUPTED: hol_interrupt cancelled this {tool} call, but HOL "
                f"ignores SIGINT and is still running its command; nothing more "
                f"is sent to it until it stops. hol_stop ends the session (the "
                f"next call restarts HOL and reloads the prefix). {rerun}")
    if state == "stopped":
        return (f"INTERRUPTED: hol_interrupt cancelled this {tool} call; HOL did "
                f"not answer, so the session was stopped and the next call "
                f"restarts it and reloads the prefix. {rerun}")
    if state == "gone":
        return (f"INTERRUPTED: hol_interrupt cancelled this {tool} call while no "
                f"HOL was running for it (it was being started, stopped or "
                f"replaced); the next call starts HOL and loads the prefix. {rerun}")
    return (f"INTERRUPTED: hol_interrupt cancelled this {tool} call before it "
            f"finished; HOL is back at its prompt, and the next navigation "
            f"replays from a clean position. {rerun}")


async def _preempt(key, intent: str, wait: float, holder=None):
    """Cancel the call holding `key`'s guard, as `intent`, and wait up to
    `wait` seconds for it to return. Its tool name, or None when no other
    call holds the guard (or, given `holder`, when that task no longer
    does). A stop or restart overrides an interrupt already under way; any
    cancel is sent once, since a second would outlive the recovery's
    uncancel and end the call with no reply. A call a client's own cancel
    is already unwinding is only waited for, and None returned: it ends
    with no reply, whatever the control tool does."""
    operation = _session_operations.get(key)
    owner = operation.owner if operation is not None else None
    if holder is not None and owner is not holder:
        return None
    if owner is None or owner.done() or owner is asyncio.current_task():
        return None
    if operation.recovering and operation.intent is None:
        await asyncio.wait({owner}, timeout=wait)
        return None
    tool = operation.tool or "running"
    if operation.intent is None:
        operation.intent = intent
        owner.cancel()
    elif operation.intent is not None and intent != "interrupt":
        operation.intent = intent
    await asyncio.wait({owner}, timeout=wait)
    return tool


# A strong reference lives with every holder/waiter. Idle names disappear,
# avoiding retained sessions and locks bound to a defunct event loop.
_session_operations = WeakValueDictionary()
_startup_operation = object()


@asynccontextmanager
async def _session_operation(key, tool=None):
    operation = _session_operations.get(key)
    if operation is None:
        operation = _SessionOperation()
        _session_operations[key] = operation
    task = asyncio.current_task()
    if operation.owner is task:
        # Auto-init and restart call other server helpers in the same task.
        yield
        return
    async with operation.lock:
        operation.owner = task
        operation.tool = tool
        try:
            yield
        except asyncio.CancelledError:
            # Only the holder recovers. Cancelling a waiter must not interrupt
            # the operation it was waiting for. Shield MCP cancel scopes so
            # pipe recovery finishes before another request takes the lock.
            operation.recovering = True
            with anyio.CancelScope(shield=True):
                state = await _recover_cancelled_operation(key, operation.intent)
            if operation.intent and task.cancelling():
                # A control tool's own cancel: the call answers instead of
                # vanishing. Any other pending cancel still propagates.
                task.uncancel()
                if not task.cancelling():
                    raise _Interrupted(state, operation.intent) from None
            raise
        finally:
            operation.owner = None
            operation.tool = None
            operation.intent = None
            operation.recovering = False


async def _recover_cancelled_operation(key, intent=None) -> str:
    """Bring HOL back after a guarded call was cancelled; "recovered",
    "busy", "stopped", or "gone" when no HOL was running to bring back.

    "interrupt" (hol_interrupt) never kills: HOL that ignores SIGINT is left
    running and marked busy. "stop"/"restart" end the session. A client's
    own cancel (None) stops the session when HOL does not answer in 30s,
    since no caller is left to be told it is busy."""
    entry = _sessions.get(key)
    if entry is None or (intent == "interrupt" and not entry.session.is_running):
        # No session (it was being started or replaced) or no process:
        # nothing to bring back, and nothing at a prompt either.
        return "gone"
    if intent in ("stop", "restart"):
        state = "stopped"
        try:
            await entry.session.stop()
        except Exception:
            pass
    elif intent == "interrupt":
        try:
            recovered = await entry.session.interrupt_and_realign()
        except Exception:
            recovered = False
        state = ("recovered" if recovered else
                 "busy" if entry.session.is_running else "gone")
    else:
        try:
            entry.session.interrupt()
            recovered = await entry.session.resync()
        except Exception:
            recovered = False
        state = "recovered" if recovered else "stopped"
        if not recovered:
            # A pipe that could not be aligned must not serve another request.
            try:
                await entry.session.stop()
            except Exception:
                pass
    if entry.cursor:
        entry.cursor.mark_interrupted()
        if state in ("stopped", "gone"):
            entry.cursor._schedule_full_reinit("cancelled request ended the session")
    return state


def _serialized_session(parameter="session"):
    """Serialize a complete request, including init/restart and presentation.

    Session names survive cursor/process replacement. Interrupt and stop are
    deliberately outside this guard so they can abort a running operation.
    None selects the shared startup guard for the single-session policy.
    """
    def decorate(function):
        signature = inspect.signature(function)

        @wraps(function)
        async def serialized(*args, **kwargs):
            key = _startup_operation
            if parameter is not None:
                arguments = signature.bind(*args, **kwargs).arguments
                key = arguments.get(parameter, signature.parameters[parameter].default)
            try:
                async with _session_operation(key, function.__name__):
                    return await function(*args, **kwargs)
            except _Interrupted as cancelled:
                return _cancelled_call_text(function.__name__, cancelled.state,
                                            cancelled.intent)
            finally:
                # A session is idle from the END of its last call: a long
                # call is activity, not idleness (_prune_idle_sessions).
                entry = _sessions.get(key)
                if entry is not None:
                    entry.last_used = time.time()
        return serialized
    return decorate


def _timeout_arg_error(timeout: float | None) -> str | None:
    """Error text for a timeout= argument that cannot be a budget in seconds."""
    if timeout is None or timeout <= MAX_STATE_AT_TIMEOUT:
        return None
    return (
        f"ERROR: timeout={timeout:g} exceeds the maximum {MAX_STATE_AT_TIMEOUT:.0f}s. "
        f"The unit is seconds ({timeout / 3600:.1f} h requested). Pass e.g. "
        f"timeout={2 * STATE_AT_TIMEOUT:g} for a heavy prefix, or timeout=0 "
        f"to disable the bound."
    )


def _nav_lock(cursor) -> asyncio.Lock:
    """The cursor's navigation lock, created on first use.

    `HOLSession._lock` serializes ONE command; a navigation is a sequence of
    them (`drop_all()`, `gf ...`, the replayed steps, `goals_json()`), and two
    of them interleaved leave each caller reading whichever proof won the race.
    """
    lock = getattr(cursor, "_nav_lock", None)
    if lock is None:
        lock = asyncio.Lock()
        cursor._nav_lock = lock
    return lock


async def _state_at_bounded(
    cursor, line: int, col: int = 1, skip_prefix: bool = False,
    timeout: float | None = None,
) -> StateAtResult:
    """Navigate under the cursor's navigation lock and an overall budget."""
    async with _nav_lock(cursor):
        return await _state_at_budgeted(
            cursor, line, col, skip_prefix=skip_prefix, timeout=timeout
        )


async def _state_at_budgeted(
    cursor, line: int, col: int = 1, skip_prefix: bool = False,
    timeout: float | None = None,
) -> StateAtResult:
    """Run cursor.state_at under an overall wall-clock budget.

    On expiry, SIGINT the HOL process, flush the pipe back to a fresh prompt
    (session.resync — the aborted command's reply lands too late for the next
    send's 10 ms drain and would otherwise be read as that send's own reply),
    resync the cursor, then return a TIMEOUT StateAtResult (tactics_total=0
    routes it through the structural-error path). A budget <= 0 (or None when
    STATE_AT_TIMEOUT is disabled) means unbounded.
    """
    budget = STATE_AT_TIMEOUT if timeout is None else timeout
    if budget is not None and budget <= 0:
        budget = None
    if budget is None:
        return await cursor.state_at(line, col, skip_prefix=skip_prefix)
    t_begin = time.perf_counter()
    try:
        return await asyncio.wait_for(
            cursor.state_at(line, col, skip_prefix=skip_prefix),
            timeout=budget,
        )
    except asyncio.TimeoutError:
        # Where the budget went: the prefix (dependency load + earlier
        # theorems) runs until the cursor marks the target's own replay.
        started = getattr(cursor, "_target_replay_started", None)
        prefix_s = min(budget, started - t_begin) if started else budget
        target_s = max(0.0, budget - prefix_s)
        try:
            cursor.session.interrupt()
        except Exception:
            pass
        # Read the aborted command's reply before anything else is written,
        # or it becomes the next command's reply and the pipe stays one frame
        # behind for the rest of the session.
        try:
            recovered = bool(await cursor.session.resync())
        except Exception:
            recovered = False
        try:
            cursor.mark_interrupted()
        except Exception:
            pass
        if not recovered:
            # The aborted reply may still be in the pipe, where the next send
            # would read it as its own; only a fresh process is trusted.
            try:
                cursor._schedule_full_reinit(
                    "HOL did not resynchronise after the budget abort")
            except Exception:
                pass
        return StateAtResult(
            goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
            file_hash="",
            error=_timeout_error_text(budget, prefix_s, target_s,
                                      target_started=started is not None,
                                      phase=(getattr(cursor, "_phase", None)
                                             if getattr(cursor, "_phase", {}).get("interrupted")
                                             else None),
                                      recovered=recovered),
        )


def _timeout_error_text(budget: float, prefix_s: float, target_s: float,
                        target_started: bool, phase: dict | None = None,
                        recovered: bool = True) -> str:
    """The TIMEOUT message, attributed: `prefix=` is dependency load plus the
    theorems before the target, `target=` the target's own tactics."""
    state = ("session recovered" if recovered else
             "session NOT recovered: HOL restarts on the next call")
    head = (
        f"TIMEOUT: state_at exceeded its overall {budget:.0f}s budget and was "
        f"aborted (HOL interrupted; {state}). Spent: prefix={prefix_s:.1f}s "
        f"(dependencies + current-file declarations + earlier theorems), target={target_s:.1f}s (this "
        f"theorem's own tactics). "
    )
    if not target_started:
        detail = _phase_description(phase)
        if phase and phase.get("phase") in {"top-level SML/translation", "local SML block"}:
            return head + detail + (
                " The target tactics have not run. Time was spent executing the "
                "current file's declarations/translation; rebuilding ancestors or "
                "splitting the target proof does not address this phase. Inspect "
                "the named source span and reuse the warm session/checkpoints; "
                "a justified larger timeout may be needed for a cold prefix.")
        if phase and phase.get("phase") == "preceding theorem":
            return head + detail + (
                " The target tactics have not run. Inspect the named preceding "
                "theorem and its replay budget, not the target proof.")
        return head + (
            detail + " The budget went to the PREFIX; target tactics have not run. "
            "Inspect dependency loading versus current-file declarations before "
            "retrying. Build ancestors only if their artifacts are missing/stale; "
            "already-built heavy dependencies may need a preloaded HOLHEAP. "
            "Use a larger timeout only for an identified expensive cold prefix."
        )
    heavy_prefix = ("" if prefix_s <= target_s else
                    " (the prefix took the larger share: if that repeats on a "
                    "passing call's `startup=`, build the ancestors so they load "
                    "from .dat)")
    return head + (
        f"The budget ran out in YOUR tactics{heavy_prefix}: this is almost always "
        "a LOOPING TACTIC you just wrote. Prime suspects: simp/fs/gvs/rw[<recursive_def>] WITHOUT "
        "`Once` (unfolds forever, esp. inside its own induction IH); a GSYM or "
        "symmetric-equality rewrite that oscillates; an unbounded "
        "metis_tac/every_case_tac blowup. DIAGNOSE FIRST: if the frontier sits "
        "inside a `>-`/`THEN1`/`by (...)` chain, SUB-SUSPEND that arm — never "
        "cheat-bisect; only on a FLAT body (no such chain above the frontier) put "
        "a `cheat` before your newest tactic and navigate to it (cheap) to read "
        "the goal. Then fix the loop (simp[Once <def>]; drop the GSYM; narrow "
        "the rewrite set). A long-running but correct tactic needs `>- suspend` "
        "to shrink the lump, or a larger timeout= (seconds)."
    )


def _classify_state_at(result: StateAtResult) -> tuple[bool, bool, bool]:
    """Classify a StateAtResult as (proof_complete, structural_error, broken).

    Every tool that presents these goals must agree on what they mean, so the
    test lives here rather than in each presenter. `broken` means the replay
    stopped BEFORE the requested position: the goals are the failure point's,
    not the position's.
    """
    empty_goal_query_succeeded = not result.error or "no goals" in result.error.lower()
    is_proof_complete = bool(
        empty_goal_query_succeeded
        and result.tactics_replayed == result.tactics_total
        and not result.goals
    )
    is_structural = bool(result.error and result.tactics_total == 0)
    is_broken = bool(
        result.error
        and not is_proof_complete
        and not is_structural
        and result.tactics_replayed < result.tactic_idx
    )
    return is_proof_complete, is_structural, is_broken


async def _state_caveat_lines(
    cursor, result: StateAtResult, active_theorem: str | None,
    thm=None, line: int | None = None,
) -> list[str]:
    """Caveats that must accompany ANY presentation of `result`'s goals.

    Each one qualifies what the goals rest on — an entered-but-not-reached
    step, a cheated target, cheated dependencies, prefix-skip mode. Dropping
    them turns a qualified state into an unqualified one.
    """
    lines: list[str] = []

    # HOL's own diagnostics from this navigation. The same-name/different-type
    # warning in particular is unrecoverable once dropped: the rendered goal
    # prints no types, so the colliding variables look identical.
    if result.warnings:
        lines.append("")
        lines.append("[HOL diagnostics during this navigation:]")
        for w in result.warnings:
            lines.append(f"  {w}")

    # Chain-entry landing: the requested position is strictly inside one
    # opaque step (lumped/parenthesized chain). The state shown is the
    # step's ENTRY, which is easy to misread as the state at that line.
    if (result.inside_step_idx is not None and not result.error
            and thm is not None and thm.proof_body and line is not None):
        k = result.inside_step_idx
        step_plan = cursor._step_plan
        if k < len(step_plan):
            text_start = step_text_start(step_plan, k, thm.proof_body)
            start_line = _file_offset_to_line_col(
                thm.proof_body_offset + text_start, cursor._content)[0]
            end_line = _file_offset_to_line_col(
                thm.proof_body_offset + step_plan[k].end,
                cursor._content)[0]
            if end_line > start_line:
                lines.append("")
                lines.append(
                    f"NOTE: target line {line} is INSIDE step {k} "
                    f"(lumped/parenthesized chain, lines {start_line}-"
                    f"{end_line}); the state shown is this step's ENTRY "
                    f"at line {start_line}, not the state at line {line}. "
                    f"The group is applied to several goals here, so a flat "
                    f"replay inside it would not be the file's state. To "
                    f"navigate inside, split the arm with `>- suspend` into "
                    f"a Resume body."
                )

    # Inside-group landing: the position inside an opaque step was reached by
    # replaying the step's flat sub-plan, sound because every positional
    # group entered received exactly one goal. Say so, and that the position
    # is not cached.
    ig = result.inside_group
    if ig:
        lines.append("")
        if ig.get("error"):
            lines.append(
                f"[inside opaque step {ig['step']} (lines {ig['start_line']}-"
                f"{ig['end_line']}): sub-step {ig['sub_idx']} of {ig['sub_total']} "
                f"FAILED at line {ig['fail_line']}; the goals shown are the state "
                f"it was applied to]"
            )
        else:
            lines.append(
                f"[inside opaque step {ig['step']} (lines {ig['start_line']}-"
                f"{ig['end_line']}): state after sub-step {ig['sub_idx']} of "
                f"{ig['sub_total']} — the group receives exactly one goal here, so "
                f"this flat replay coincides with the file's per-goal application; "
                f"position not cached]"
            )

    # Suggest extracting by/>- subproof into a suspend/Resume block
    if result.inside_by and not result.error:
        lines.append("")
        lines.append("[Inside by/>- subproof. Consider extracting into a suspend/Resume block "
                     "for independent verification and easier editing.]")

    # Smart-quote diagnosis on parse/lex-flavoured errors (the raw replay
    # error may carry lexer text the formatted output above does not show).
    if result.error:
        lines.extend(_quote_diagnosis_if_parse_error(cursor.file, result.error))

    # Lost-suspension diagnosis: a Resume whose label cannot be found usually
    # means an ancestor (dispatcher or earlier Resume) broke during loading.
    if result.error and active_theorem and (
            "No such label" in result.error
            or "Failed to set up Resume goal" in result.error):
        diag = await cursor.diagnose_resume_failure(active_theorem)
        if diag:
            lines.append("")
            lines.append(diag)

    # Refuse a false-green: if the TARGET theorem itself was auto-cheated
    # during load, the goals/"No goals" above rest on its STATEMENT, not its
    # replayed proof — say so loudly instead of letting it read as a pass.
    self_cheat = _target_self_cheated_reason(cursor, active_theorem)
    if self_cheat is not None:
        lines.extend(_target_self_cheated_lines(self_cheat))

    # Name any deps auto-cheated while loading the file prefix (the state
    # shown was computed with those theorems replaced by `cheat`).
    lines.extend(_auto_cheated_deps_lines(cursor, active_theorem))
    lines.extend(_prefix_error_lines(cursor))

    # Notice when prefix-skip navigation deliberately cheated the prefix.
    lines.extend(_prefix_skip_lines(cursor))

    return lines


def _file_offset_to_line_col(file_offset: int, content: str) -> tuple[int, int]:
    """Convert a byte offset in file content to absolute (line, col), both 1-indexed."""
    before = content[:file_offset]
    line = before.count('\n') + 1
    last_nl = before.rfind('\n')
    col = file_offset - last_nl if last_nl >= 0 else file_offset + 1
    return line, col


def _session_notice_lines(cursor) -> list[str]:
    """Session-level events since the last output (ancestor rebuilt and
    reloaded, restart into another workdir), each on its own line."""
    take = getattr(cursor, "take_notices", None)
    notices = take() if take else []
    notices.extend(_failure_evidence_lines(getattr(cursor, "session", None)))
    return [""] + notices if notices else []


def _failure_evidence_lines(session) -> list[str]:
    evidence = getattr(getattr(session, "failure_evidence", None), "latest", None)
    if not evidence:
        return []
    # Clearly history: the current request may have succeeded after a failure.
    if evidence.get("path"):
        return [f"[Latest HOL failure evidence ({evidence['kind']}): {evidence['path']}]"]
    return [f"[HOL failure evidence could not be saved: {evidence.get('log_error', 'unknown')}]"]


def _prefix_error_lines(cursor) -> list[str]:
    """Top-level SML spans of the loaded prefix in which an item raised. The
    raise ends the span: that item (a Definition whose automatic termination
    proof failed defines nothing) and everything after it in the span did
    not run, so their bindings are absent from the heap and a later use of
    one fails or silently refers to something else."""
    errors = getattr(cursor, "_prefix_errors", None)
    if not errors:
        return []
    rendered = "; ".join(f"lines {a}-{b}: {reason}" for a, b, reason in errors)
    return ["", f"[prefix errors (top-level SML that raised; the raising item and "
                f"the rest of its span did not run, so what they define is missing "
                f"from the heap): {rendered}]"]


def _auto_cheated_deps_lines(cursor, target_name: str | None = None) -> list[str]:
    """Context admission history, NOT an established dependency closure.

    Retains the legacy helper name. Backward navigation can leave history from
    later theorems here; only kernel oracle evidence establishes use of an
    admission. Target-self-taint is reported separately and still blocks OK.
    """
    failed = getattr(cursor, "_failed_proofs", None)
    if not failed:
        return []
    deps = {name: reason for name, reason in failed.items() if name != target_name}
    if not deps:
        return []
    rendered = "; ".join(f"{name} ({reason})" for name, reason in deps.items())
    return ["", f"[context admission history (not a dependency list): {rendered}]"]


def _prefix_skip_lines(cursor) -> list[str]:
    """Notice shown when prefix-skip navigation is active.

    In skip_prefix mode every prefix theorem was bound by `cheat` (statement
    only, NOT replayed), so the goal shown rests on those statements. Report a
    concise COUNT (not the full list — it can be hundreds) and tell the reader
    this is a navigation aid, not a verification.
    """
    if not getattr(cursor, "_skip_prefix", False):
        return []
    n = len(getattr(cursor, "_skipped_thms", ()) or ())
    return [
        "",
        f"[prefix-skip mode ON: {n} prefix theorem(s) bound by cheat (statement "
        f"only, NOT replayed)]",
        "  Navigation aid for a cold/unbuilt theory — the target's OWN tactics "
        "still replay, but the goal rests on the skipped statements. This is NOT "
        "a verification; re-run without skip_prefix (or holmake) to truly check.",
    ]


def _target_self_cheated_reason(cursor, target_name: str | None) -> str | None:
    """If the navigation/check TARGET was itself auto-cheated during load,
    return its reason; else None.

    The context has contained an admitted binding for this target. Even if
    its tactics subsequently close, that is not sufficient to certify it:
    revalidate in a fresh context, without the old binding or cached verdicts.
    """
    if not target_name:
        return None
    failed = getattr(cursor, "_failed_proofs", None)
    if not failed:
        return None
    return failed.get(target_name)


_SLOW_NAV_SECS = 120.0
_slow_nav_counts: dict[tuple[str, str, str], tuple[str | None, int]] = {}


def _slow_nav_lines(session: str, file, theorem: str | None,
                    elapsed_secs: float, prefix_secs: float = 0,
                    cause: str | None = None,
                    revision: str | None = None) -> list[str]:
    """Warn when the SAME theorem revision is navigated slowly more than once.

    One slow replay is the unavoidable cold start. Every later one re-pays for a
    replayed unit that should have been shrunk instead. Editing/restructuring the
    theorem starts a new revision: its required final validation is not counted
    as another probe of the old body.

    ``cause`` names what the prefix/setup time was spent on when the cursor
    knows (a cold init, a scheduled session reinit and why); a slow prefix
    with a known cause is attributed to it rather than left to be guessed at.
    """
    if not theorem or elapsed_secs < _SLOW_NAV_SECS:
        return []
    if prefix_secs >= _SLOW_NAV_SECS and elapsed_secs - prefix_secs < _SLOW_NAV_SECS:
        target = max(0, elapsed_secs - prefix_secs)
        if cause:
            return ["", f"[Slow prefix/setup: {prefix_secs:.1f}s — {cause}; "
                    f"target replay {target:.1f}s. The prefix cost belongs to "
                    "that setup, not to this theorem's tactics; this timing "
                    "does not justify splitting the target proof.]"]
        return ["", f"[Slow prefix/setup: {prefix_secs:.1f}s; target replay "
                f"{target:.1f}s. Inspect current-file "
                "translation/dependency loads and checkpoint reuse; this timing "
                "does not justify splitting the target proof.]"]
    key = (session, str(file or ""), theorem)
    previous = _slow_nav_counts.get(key)
    if previous is None or previous[0] != revision:
        n = 1
    else:
        n = previous[1] + 1
    _slow_nav_counts[key] = (revision, n)
    if n < 2:
        return []
    return [
        "",
        f"⛔ SLOW NAVIGATION #{n} into `{theorem}` ({elapsed_secs:.0f}s, over the "
        f"{_SLOW_NAV_SECS:.0f}s threshold) — STOP: THIS IS A PROCESS FAILURE.",
        "   The first slow replay is the cold start; every one after it re-pays for "
        "a replayed",
        "   unit that is too big. Do NOT probe again before shrinking it: put one "
        "`>- suspend",
        "   \"<Case>\"` per arm of a multi-case proof (for a genuine induction that "
        "ladder is the",
        "   COMMITTED form, not scaffolding to inline back), then sub-suspend the "
        "failing arm.",
        "   Minutes-per-probe iteration is never justified by the proof being large.",
    ]


def _timing_lines(result) -> list[str]:
    """The `[Timing: …]` and `[Cache: …]` footer of a navigation: where the
    time went, and what the position cache reused versus replayed. Shared by
    every tool that navigates, so a slow call is attributable from any of
    them."""
    if not result.timings:
        return []
    t = result.timings
    lines = [""]
    method = t.get('strategy', 'replay')
    # asms=N is INFORMATION, not prediction: it lets a reader correlate a
    # slow step with the context it ran in. It implies nothing — fs, gs,
    # gvs, simp and metis_tac can all fail to terminate at any count.
    asms_str = (f", asms={len(result.goals[0].get('asms', []))}"
                if result.goals else "")
    lines.append(f"[Timing: total={t.get('total', 0)*1000:.0f}ms, "
                 f"replay={t.get('replay', 0)*1000:.0f}ms, "
                 f"startup={t.get('startup', 0)*1000:.0f}ms, "
                 f"method={method}{asms_str}]")
    # Cache-state diagnostics: show what _pos was BEFORE the call,
    # the target, and what got reused vs replayed. Useful for
    # reproducing cache bugs.
    before_idx = t.get('pos_before_idx', None)
    if before_idx is not None:
        before_offset = t.get('pos_before_offset', -1)
        before_init = t.get('pos_before_init', 0)
        hash_match = t.get('pos_hash_match', 0)
        target_idx = t.get('target_idx', '?')
        target_partial = t.get('target_partial', 0)
        file_changed = t.get('file_changed', 0)
        offset_str = f",off={before_offset}" if before_offset >= 0 else ""
        init_str = "init" if before_init else "uninit"
        hash_str = "hash=match" if hash_match else "hash=miss"
        partial_str = "partial" if target_partial else "boundary"
        changed_str = "changed" if file_changed else "unchanged"
        parts = [
            f"pos_before=(idx={before_idx}{offset_str},{init_str},{hash_str})",
            f"target=(idx={target_idx},{partial_str})",
            f"file={changed_str}",
            f"reached={result.tactics_replayed}/{result.tactics_total}",
        ]
        if 'incr_first_diff' in t:
            parts.append(
                f"incr=(first_diff={t['incr_first_diff']},"
                f"old_idx={t['incr_old_idx']})"
            )
        if result.inside_by:
            parts.append("inside_by=true")
        lines.append(f"[Cache: {', '.join(parts)}]")
    return lines


def _phase_description(phase: dict | None) -> str:
    if not phase:
        return ""
    span = (f" lines {phase['start_line']}-{phase['end_line']}"
            if phase.get("start_line") else "")
    return (f"Active item: {phase.get('phase', 'unknown')} "
            f"{phase.get('item', '')}{span} "
            f"(command budget {phase.get('budget', '?')}s).")


def _target_self_cheated_lines(reason: str) -> list[str]:
    """Explicit 'this was NOT validated' verdict for a self-cheated target.

    Names the cause (timeout vs error) and points ONLY at in-workflow remedies
    (sub-suspend to shrink replay scope) — never at holmake, which is the
    end-of-file gate, not a per-theorem validation step.
    """
    is_timeout = reason.lstrip().upper().startswith("TIMEOUT") or "timeout" in reason.lower()
    if is_timeout:
        cause = (f"its own proof exceeded the per-theorem replay budget "
                 f"({reason}) and was replaced by `cheat` to load the rest of "
                 f"the file")
        remedy = ("Shrink the replay scope: split a slow arm with `>- suspend "
                  "\"Label\"` + a `Resume` body so only that body replays, then "
                  "re-check the (smaller) target.")
    else:
        cause = (f"its own proof failed during load ({reason}) and was replaced "
                 f"by `cheat`")
        remedy = ("Fix the failing tactic, or isolate the failing arm with "
                  "`>- suspend \"Label\"` + a `Resume` body and re-check that body.")
    return [
        "",
        "⚠ NOT VALIDATED — the result above is NOT a verification of this "
        "theorem.",
        f"  This theorem was auto-cheated: {cause}.",
        "  Completed goals alone do not establish that the old admitted binding was unused.",
        f"  {remedy}",
        "  If the file proof is ready, use hol_check_proof(theorem=..., fresh=True)",
        "  to revalidate in a clean session without the old admitted binding.",
    ]


def _is_raised_exception(err: str | None) -> bool:
    """True iff a replay error string is a RAISED EXCEPTION (HOL_ERR /
    Exception- / 'raised exception') rather than a timeout or a clean
    unsolved-goals failure.

    A raised exception — classically a `qpat_x_assum`/`qmatch_*`/`rename1`
    whose pattern no longer matches — fires from wherever that tactic sits,
    which inside a lumped/opaque step is NOT necessarily the step the replay
    stopped at. So the precise step pin must be softened in this case.
    """
    if not err:
        return False
    low = err.lower()
    if "timed out" in low or err.lstrip().upper().startswith("TIMEOUT"):
        return False
    return ("HOL_ERR" in err or "Exception-" in err or "raised exception" in low)


def _exception_advisory_lines(err: str | None) -> list[str]:
    """Advisory shown when replay stopped on a raised exception: name the
    exception and warn that the pinned step is only where replay STOPPED, the
    true fault may be an earlier match-sensitive tactic."""
    out = [
        "",
        "NOTE: replay stopped on a RAISED EXCEPTION, not an unsolved goal.",
        "  The step/line shown is where replay halted — with a raised exception "
        "(commonly a qpat_x_assum / qmatch_* / rename1 whose pattern no longer "
        "matches) the TRUE fault is often an EARLIER match-sensitive tactic in "
        "this region. Read those first; the pin is an upper bound, not the cause.",
    ]
    if err:
        compact = err.strip().splitlines()[0][:200] if err.strip() else ""
        if compact:
            out.append(f"  Exception: {compact}")
    return out


_RAISED_FAIL_MARKER = (
    "  <-- replay stopped here (raised exception; true fault may be earlier)"
)
_RAISED_FAIL_HEADER = "=== Where replay stopped (raised exception) ==="


def _is_static_error(err: str | None) -> bool:
    """True iff a replay error is a Poly/ML COMPILE error in the step's SML —
    an undeclared name, a type error, a syntax error — so no tactic ran and
    the goal is untouched. Distinct from a tactic that ran and failed."""
    if not err:
        return False
    return ("Static Errors" in err or "has not been declared" in err
            or "poly: : error:" in err.lower())


def _static_error_lines(err: str | None) -> list[str]:
    """The compiler's own diagnostics for a step whose SML did not compile."""
    picked = [ln.strip() for ln in (err or "").splitlines()
              if re.search(r"error:|has not been declared|Static Errors", ln)]
    out = ["  SML compile error — no tactic ran; this is not a logical proof failure:"]
    out.extend(f"    {ln[:200]}" for ln in picked[:4])
    if not picked and err and err.strip():
        out.append(f"    {err.strip().splitlines()[0][:200]}")
    out.append(
        "  An undeclared name is a source error — a missing binding, or a forward "
        "reference to a block that is still below the parked position; a TYPE error "
        "at a line of valid HOL may be a step-realization fault (skill note: Type "
        "error at a replayed step). Sub-suspending cannot localize either.")
    return out


_STATIC_FAIL_MARKER = "  <-- does not compile (no tactic ran)"
_STATIC_FAIL_HEADER = "=== Step whose SML did not compile ==="


_PARSE_ERROR_RE = re.compile(r"parse|unknown character|lex", re.I)


def _quote_diagnosis_if_parse_error(file_path, error_text: str) -> list[str]:
    """On parse-flavoured errors, check the file for unmatched smart quotes.

    Unmatched U+2018/U+2019 (e.g. a pasted right-quote where an ASCII
    apostrophe belongs) are a recurring cause of opaque lexer errors.
    """
    if not error_text or not _PARSE_ERROR_RE.search(error_text):
        return []
    diag = quote_diagnosis_lines(file_path)
    return [""] + diag if diag else []


def _clip(output: str, budget: int) -> str:
    """Fit `output` into `budget` bytes, keeping BOTH ends.

    The head carries the classification and attribution — `PROOF BROKEN at
    ...`, `TIMEOUT: step k (lines A-B)` — which a tail-only cut drops exactly
    when the goal is large enough for the caller to need them.
    """
    if len(output) <= budget:
        return output
    head_budget = min(budget // 3, 1500)
    # The marker's length bounds itself: the elided count has at most as
    # many digits as len(output).
    marker_len = len(f"\n\n[... {len(output)} bytes elided ...]\n\n")
    tail_budget = budget - head_budget - marker_len
    if tail_budget < 100:
        return f"[TRUNCATED: {len(output)} bytes, showing last {budget}]\n\n" + output[-budget:]
    elided = len(output) - head_budget - tail_budget
    marker = f"\n\n[... {elided} bytes elided ...]\n\n"
    return output[:head_budget] + marker + output[-tail_budget:]


def _truncate_output(output: str, max_output: int, footer: str = "") -> str:
    """Truncate output to max_output bytes, keeping the head and the tail.

    If footer is provided, it's appended AFTER truncation so it's never lost.
    """
    if max_output < 1:
        return f"ERROR: max_output must be positive (got {max_output})"
    # Reserve space for footer
    if footer:
        footer = "\n" + footer
        body_budget = max_output - len(footer)
        if body_budget < 100:
            # Not enough room — just show footer
            return footer.lstrip("\n")
        return _clip(output, body_budget) + footer
    return _clip(output, max_output)


@dataclass
class SessionEntry:
    """Registry entry for a HOL session."""
    session: HOLSession
    started: datetime
    workdir: Path
    last_used: float = 0.0  # time.time() of last activity
    cursor: Optional[FileProofCursor] = None
    holmake_env: Optional[dict] = None  # env vars for holmake (auto-captured on success)
    env: Optional[dict] = None  # env vars passed to HOL process

    def __post_init__(self):
        if self.last_used == 0.0:
            self.last_used = time.time()


mcp = FastMCP("hol", instructions="""HOL4 theorem prover - proof development workflow:

1. hol_state_at: Check proof state at cursor position (pass file= to auto-init)
2. Edit file directly, then hol_state_at to see new goals
3. Repeat until proof complete
4. holmake: Only at the end to verify the build

Develop on the FILE, not in the session. hol_send is for SMALL probes only —
never drive a whole proof through it; going deep is suspend/Resume territory.
Prefer hol_search and hol_goals over hol_send probes for information.

Each tool's docstring covers its own params, output markers and guard rails;
read the one you are about to call rather than guessing. Server-enforced
refusals (a second concurrent session, shadow bindings) are policy firing,
not errors to retry.

Record suspected MCP issues and usability rough edges using the Complaint inbox
workflow in ~/hol4-mcp/skills/hol4-proving/notes/reference_hol4_mcp.md.

Do NOT:
- Call hol_restart after file edits (state_at auto-detects changes)
""")
_sessions: dict[str, SessionEntry] = {}


def _sigint_handler(signum, frame):
    """Handle SIGINT by interrupting all HOL sessions.

    Called when pi sends SIGINT (e.g., user pressed ESC during tool execution).
    Runs hol_interrupt on every session with a call or a timed-out command in
    progress, so the waiting call is cancelled and the pipe re-aligned; a
    bare SIGINT would leave that call waiting for a reply that may never
    come. Without a running event loop it falls back to a bare SIGINT.

    Note: Takes a snapshot of sessions to avoid RuntimeError if dict is modified
    concurrently (e.g., session being added/removed when signal arrives).
    """
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        loop = None
    # Snapshot to avoid "dictionary changed size during iteration"
    for name, entry in list(_sessions.items()):
        try:
            if loop is None:
                entry.session.interrupt()
                continue
            operation = _session_operations.get(name)
            if (operation is not None and operation.owner is not None) or entry.session.busy:
                loop.call_soon_threadsafe(_schedule_interrupt, name)
        except Exception:
            pass  # Best effort - signal handlers must not raise


_signal_interrupts: set[asyncio.Task] = set()


def _schedule_interrupt(name: str) -> None:
    task = asyncio.ensure_future(hol_interrupt(session=name))
    _signal_interrupts.add(task)
    task.add_done_callback(_signal_interrupts.discard)


# Install SIGINT handler (replaces default KeyboardInterrupt behavior)
signal.signal(signal.SIGINT, _sigint_handler)


def _kill_all_sessions_sync():
    """Best-effort SIGKILL all HOL process groups. Safe from atexit/signal.

    Covers abnormal shutdown paths where async `hol_stop` won't run:
    - stdio_client's _terminate_process_tree sends SIGTERM to *our* pgid
      but HOL is in its own pgid (start_new_session=True in HOLSession).
    - atexit fires on normal interpreter shutdown.
    Without this, HOL children (multi-GB RSS) get reparented to PID 1 and leak.
    """
    for entry in list(_sessions.values()):
        try:
            entry.session.kill_sync()
        except Exception:
            pass  # best effort


def _sigterm_handler(signum, frame):
    """Kill HOL children, then re-raise default SIGTERM so we actually exit."""
    _kill_all_sessions_sync()
    signal.signal(signum, signal.SIG_DFL)
    os.kill(os.getpid(), signum)


signal.signal(signal.SIGTERM, _sigterm_handler)
atexit.register(_kill_all_sessions_sync)


_SESSION_IDLE_TIMEOUT = 1800  # 30 minutes
_PRUNE_INTERVAL = 300  # Check every 5 minutes at most
_last_prune_time = 0.0

# Per session NAME, not per process: the HOL environment every start of the
# session uses (set by hol_start(env=...) and hol_setenv), and why its last
# process ended, for the notice of the next automatic start.
_session_envs: dict[str, dict[str, str]] = {}
_session_ended: dict[str, str] = {}


def _session_env(env) -> dict[str, str] | str:
    """`env` with every value a string, or an error text. Checked before
    anything is stopped, so a bad value never costs the running session."""
    if not isinstance(env, dict):
        return "ERROR: env must map variable names to values."
    clean = {}
    for key, value in env.items():
        if (not isinstance(key, str) or isinstance(value, bool)
                or not isinstance(value, (str, int))):
            return (f"ERROR: env {key!r} must have a string or integer value, "
                    f"got {value!r}. Nothing was changed.")
        clean[key] = str(value)
    heap = clean.get("HOL4_MCP_MAXHEAP_MB")
    if heap is not None and not (heap.strip().isdigit() and int(heap) >= 256):
        return ("ERROR: HOL4_MCP_MAXHEAP_MB must be an integer >= 256 (MB). "
                "Nothing was changed.")
    return clean


def _drop_dead_session(name: str) -> None:
    """Forget a session whose HOL process is gone; the next start says so."""
    _sessions.pop(name, None)
    _session_ended[name] = "ended because its HOL process died"


def _heap_pressure_lines(session: HOLSession) -> list[str]:
    """A line when HOL's resident memory is at its heap limit, where Poly/ML
    spends nearly all its time collecting garbage."""
    limit = session.maxheap_mb
    resident = session.resident_mb()
    if not limit or resident is None or resident < 0.9 * limit:
        return []
    return ["", f"[Heap pressure: HOL holds {resident} MB against its {limit} MB "
            f"heap limit. At the limit Poly/ML spends nearly all its time "
            f"collecting garbage: steps slow down by orders of magnitude and "
            f"SIGINT is answered late or not at all. Raise HOL4_MCP_MAXHEAP_MB "
            f"with hol_setenv (it restarts the session).]"]


def _indexed_saves(ckpt_dir: Path) -> set[str]:
    """The saves a later session may start from, as the reuse indexes of
    the directory's scripts name them (FileProofCursor.persist_reusable_state)."""
    keep: set[str] = set()
    for index in ckpt_dir.glob("reuse-*.json"):
        try:
            keep.update(node for node, _ in json.loads(index.read_text()).get("chain", []))
        except (OSError, ValueError, TypeError, AttributeError):
            continue
    return keep


def _gc_cursor_checkpoints(cursor: FileProofCursor):
    """Delete orphaned per-theorem checkpoint .save files from a dying cursor.

    Keeps base_deps.save and deps_only.save (expensive ~200MB rebuilds), and
    the context saves a later session of a script may start from (one
    chain per script). Removes the other per-theorem context/end_of_proof
    saves (cheap to rebuild via replay).
    """
    ckpt_dir = cursor._checkpoint_dir
    if not ckpt_dir or not ckpt_dir.exists():
        return
    cursor.persist_reusable_state()
    keep = _indexed_saves(ckpt_dir)
    for f in [*ckpt_dir.glob("*_context.save"), *ckpt_dir.glob("*_end_of_proof.save")]:
        if str(f) not in keep:
            f.unlink(missing_ok=True)
    try:
        ckpt_dir.rmdir()  # only removes if empty
    except OSError:
        pass


def _gc_workdir_orphans(workdir: Path):
    """Clean orphaned per-theorem checkpoints from a workdir.

    Called on hol_start. Deletes *_context.save and *_end_of_proof.save
    (cheap replay rebuilds) across the cursor_checkpoints/ dirs under the
    workdir, except those of this server's live cursors and those a reuse
    index names. Keeps base_deps.save and deps_only.save (expensive ~200MB
    rebuilds).
    """
    live = {
        Path(e.cursor._checkpoint_dir).resolve()
        for e in _sessions.values() if e.cursor is not None
    }
    for ckpt_dir in workdir.glob("**/cursor_checkpoints"):
        if not ckpt_dir.is_dir() or ckpt_dir.resolve() in live:
            continue
        keep = _indexed_saves(ckpt_dir)
        for f in [*ckpt_dir.glob("*_context.save"), *ckpt_dir.glob("*_end_of_proof.save")]:
            if str(f) not in keep:
                f.unlink(missing_ok=True)
        try:
            ckpt_dir.rmdir()
        except OSError:
            pass


async def _prune_idle_sessions():
    """Stop and remove sessions idle longer than _SESSION_IDLE_TIMEOUT.

    Throttled to run at most once per _PRUNE_INTERVAL seconds.
    """
    global _last_prune_time
    now = time.time()
    if now - _last_prune_time < _PRUNE_INTERVAL:
        return
    _last_prune_time = now
    to_prune = [
        name for name, entry in _sessions.items()
        if now - entry.last_used > _SESSION_IDLE_TIMEOUT
    ]
    for name in to_prune:
        entry = _sessions.get(name)
        if not entry:
            continue
        # Status polling must not reap a long-running proof as "idle".
        locks = (getattr(entry.session, "_lock", None),
                 getattr(entry.cursor, "_nav_lock", None))
        if any(lock is not None and lock.locked() for lock in locks):
            continue
        operation = _session_operations.get(name)
        if operation is not None and operation.lock.locked():
            continue
        # Re-check: session may have been touched during a prior await
        idle = time.time() - entry.last_used
        if idle <= _SESSION_IDLE_TIMEOUT:
            continue
        _sessions.pop(name, None)
        _session_ended[name] = f"was stopped after {idle / 60:.0f} min idle"
        if entry.cursor:
            _gc_cursor_checkpoints(entry.cursor)
        await entry.session.stop()


_GC_CALL_INTERVAL = 10    # At most once per N tool calls
_GC_TIME_INTERVAL = 120   # At most once per K seconds
_gc_call_counter = 0
_gc_last_time = 0.0
_gc_tasks: set[asyncio.Task] = set()


@_serialized_session("session_name")
async def _do_gc(session_name: str):
    """Actually run PolyML.fullGC(). Runs as background task."""
    entry = _sessions.get(session_name)
    if entry and entry.session.is_running:
        try:
            await entry.session.send('PolyML.fullGC();', timeout=10)
        except Exception:
            pass  # Best effort — don't crash on GC failure


def _schedule_gc(session_name: str):
    """Schedule background GC if due. Non-blocking — doesn't delay response.

    Triggers when both conditions met: N calls since last GC AND K seconds elapsed.
    """
    global _gc_call_counter, _gc_last_time
    _gc_call_counter += 1
    if _gc_call_counter < _GC_CALL_INTERVAL:
        return
    now = time.time()
    if now - _gc_last_time < _GC_TIME_INTERVAL:
        return
    _gc_call_counter = 0
    _gc_last_time = now
    # The loop keeps only a weak reference to a task.
    task = asyncio.create_task(_do_gc(session_name))
    _gc_tasks.add(task)
    task.add_done_callback(_gc_tasks.discard)


async def _get_session(name: str) -> Optional[HOLSession]:
    """Get session from registry, or None if not found. Triggers idle pruning."""
    await _prune_idle_sessions()
    entry = _sessions.get(name)
    if entry:
        entry.last_used = time.time()
    return entry.session if entry else None


async def _get_cursor(name: str) -> Optional[FileProofCursor]:
    """Get cursor from registry, or None if not found. Triggers idle pruning."""
    await _prune_idle_sessions()
    entry = _sessions.get(name)
    if entry:
        entry.last_used = time.time()
    return entry.cursor if entry else None


def _session_age(name: str) -> str:
    """Get human-readable session age."""
    entry = _sessions.get(name)
    if not entry:
        return "unknown"
    started = entry.started
    delta = datetime.now() - started
    secs = int(delta.total_seconds())
    if secs < 60:
        return f"{secs}s"
    elif secs < 3600:
        return f"{secs // 60}m"
    else:
        return f"{secs / 3600:.1f}h"


@mcp.tool()
@_serialized_session("name")
@_serialized_session(None)
async def hol_start(workdir: str, name: str = "default", env: dict = None,
                    force: bool = False) -> str:
    """Start a HOL4 REPL session.

    Idempotent - returns existing session if already running.
    Usually called automatically by hol_state_at (via file= parameter).

    Refuses to start a SECOND concurrent session (RULE J: one session at a
    time — a second session can resolve bare theorem names against a built
    ancestor's old version and falsely pass). Pass force=True to override.

    Args:
        workdir: Working directory (should contain Holmakefile for dependencies)
        name: Session identifier (e.g., "main")
        env: Optional environment variables (e.g. {"VFMDIR": "/path/to/vfm"}).
             HOL4_MCP_MAXHEAP_MB sets the interactive Poly/ML heap limit in MB
             (integer >= 256; default half of the machine's RAM, at least
             8192); holmake's heap_size is independent. The env belongs to
             the session name: every later start of it, automatic restarts
             included, uses it until hol_setenv or another hol_start(env=...)
             replaces it. Not applied to a session already running (the
             reply says so; hol_setenv applies it).
        force: Allow a second concurrent session despite RULE J (default False)

    Returns: Session status
    """
    if env is not None:
        env = _session_env(env)
        if isinstance(env, str):
            return env
    await _prune_idle_sessions()
    # If session exists and is running, return its state
    if name in _sessions:
        session = _sessions[name].session
        if session.is_running:
            goals = await session.send("top_goals();", timeout=10)
            current = _sessions[name].env or {}
            unapplied = ""
            if env and any(current.get(k) != v for k, v in env.items()):
                unapplied = (f"\nThe env passed was NOT applied ({env}); the running "
                             f"process has {current or 'no extra env'}. hol_setenv "
                             f"applies it (it restarts the session).")
            return f"Session '{name}' already running.{unapplied}\n\n=== Goals ===\n{goals}"
        _drop_dead_session(name)
    if env is None:
        env = _session_envs.get(name)

    # RULE J: one HOL session at a time. A second concurrent session resolves
    # bare theorem names against stale built ancestors and can falsely pass.
    others = [
        (n, e) for n, e in _sessions.items()
        if n != name and e.session.is_running
    ]
    if others and not force:
        listing = "\n".join(
            f"  {n}  (workdir {e.workdir})" for n, e in others
        )
        return (
            f"ERROR: refusing to start session '{name}' — other HOL "
            f"session(s) already running:\n{listing}\n"
            f"RULE J: one session at a time; a second session can resolve "
            f"bare theorem names\nagainst stale built ancestors and falsely "
            f"pass. Stop the other session\n(hol_stop(session=...)) or pass "
            f"force=True if you really need both."
        )

    # Validate workdir
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Working directory does not exist: {workdir}"

    # Create session with optional env
    session = HOLSession(str(workdir_path), env=env)

    try:
        result = await session.start()
    except Exception as e:
        await session.stop()
        return f"ERROR starting HOL: {e}"
    except BaseException:
        # A cancel (hol_interrupt, hol_stop, the client) must not leave an
        # unregistered HOL process behind.
        await asyncio.shield(session.stop())
        raise

    if not session.is_running:
        return f"ERROR: HOL failed to start. Output: {result}"

    # Register session. Handle concurrent hol_start(name=...) calls:
    # if another caller already registered a running session, stop this one
    # and return the existing session state.
    existing = _sessions.get(name)
    if existing and existing.session.is_running:
        await session.stop()
        goals = await existing.session.send("top_goals();", timeout=10)
        return f"Session '{name}' already running.\n\n=== Goals ===\n{goals}"

    _sessions[name] = SessionEntry(session, datetime.now(), workdir_path, env=env)
    if env is not None:
        _session_envs[name] = env
    _session_ended.pop(name, None)

    # Clean orphaned per-theorem checkpoints left by previous server lifetimes
    _gc_workdir_orphans(workdir_path)

    return f"Session '{name}' started. {result}\nWorkdir: {workdir_path}"


@mcp.tool()
async def hol_sessions() -> str:
    """List all active HOL sessions with their workdir, age, status, cursor."""
    await _prune_idle_sessions()
    if not _sessions:
        return "No active sessions."

    lines = ["SESSION      WORKDIR                                    AGE     IDLE    STATUS   CURSOR"]
    lines.append("-" * 105)

    now = time.time()
    for name, entry in _sessions.items():
        status = "running" if entry.session.is_running else "dead"
        age = _session_age(name)
        idle_secs = int(now - entry.last_used)
        if idle_secs < 60:
            idle_str = f"{idle_secs}s"
        elif idle_secs < 3600:
            idle_str = f"{idle_secs // 60}m"
        else:
            idle_str = f"{idle_secs / 3600:.1f}h"
        workdir_str = str(entry.workdir)
        if len(workdir_str) > 40:
            workdir_str = "..." + workdir_str[-37:]

        # Cursor info. Not `cursor.status`: it reparses the file, which may
        # rearm a reinit under the call that holds the session.
        cursor_str = getattr(entry.cursor, "_active_theorem", None) or "(none)"

        lines.append(f"{name:<12} {workdir_str:<42} {age:<7} {idle_str:<7} {status:<8} {cursor_str}")
        phase = getattr(entry.cursor, "_phase", None)
        if phase and phase.get("active"):
            elapsed = time.perf_counter() - phase["started"]
            lines.append(f"  {_phase_description(phase)} Elapsed {elapsed:.1f}s.")
        lines.extend(_failure_evidence_lines(entry.session))

    return "\n".join(lines)


_PROOF_STATE_PATTERNS = []


# Commands that may mutate the live proofManager / goal stack. A hol_send of any
# of these desyncs hol_state_at's position cache (its `reused` fast path returns
# the live goal without re-establishing it). When matched, we taint the session's
# cursor so the NEXT hol_state_at re-establishes the goal via checkpoint/replay
# (cheap — current theorem only, prefix checkpoints untouched) instead of reusing
# the polluted state. Errs toward over-matching: a false positive only costs one
# cheap re-setup; a false negative reintroduces the silent-desync bug.
_PROOFMGR_MUTATING_RE = re.compile(
    r'\b(?:'
    r'drop_all|backup_n|new_goalstack'
    r'|set_goal|set_goalfrag|set_suspended_goal|set_resume_goalfrag\w*'
    r'|verify_resume\w*|run_resume\w*|verify_core'
    r'|markerLib\.resume|bossLib\.sg'
    r'|proofManagerLib\.(?:e|b|r|g|gf|ef|eall|ee|eta|enth|expand|expandf'
    r'|expand_list|expand_frag|rotate|restart|drop|dropn|backup|add|split)'
    r')\b'
    # bare top-level proof drivers (tactic_prefix shadows e/expand/ef at top level;
    # eall/enth/eta/ee reach the goal stack straight from proofManagerLib)
    r'|(?<![\w.])(?:eall|enth|expand_list|expandf|expand|eta|ef|ee|e'
    r'|sg|gf|g|b|r)\s*[(`]'
)


def _command_mutates_proof_state(command: str) -> bool:
    return _PROOFMGR_MUTATING_RE.search(command) is not None


# `val gs = ...` etc. shadows a HOL primitive/tactic for the REST of the
# session — later tactics and probes using the name silently misbehave.
_SHADOW_BINDING_RE = re.compile(
    r'\bval\s+(gs|fs|rw|simp|e|b|g|it|concl|hyp|dest_thm|tag|aconv|drop)\s*='
)


def _check_shadow_binding(command: str) -> str | None:
    """Reject hol_send commands that shadow HOL primitives. None if allowed."""
    m = _SHADOW_BINDING_RE.search(command)
    if not m:
        return None
    nm = m.group(1)
    return (
        f"ERROR: hol_send BLOCKED — `val {nm} = ...` shadows the HOL4 "
        f"primitive/tactic `{nm}` for the rest of the session; later tactics "
        f"and probes that use `{nm}` will silently misbehave.\n"
        f"Bind a prefixed name instead, e.g. `val my_{nm} = ...`."
    )


# Interactive GOAL-CREATION in hol_send is the reconstruct-from-scratch footgun:
# spinning up a fresh goal with `g`/`gf`/`set_goal` and driving it with `e`/`ef`
# builds a proof in the SCRATCH session that says NOTHING about whether the FILE
# form replays (RULE G), diverges silently (goal order, prover-gen names, type
# ambiguity), and is lost on compaction. The session is scratch, not storage.
#
# Block the goal CREATORS here (navigation establishes frontiers via quse_string,
# which does NOT route through this tool, so hol_state_at is unaffected; short
# e/ef PROBES on an already-navigated frontier stay allowed).
_INTERACTIVE_GOAL_RE = re.compile(
    r'\bproofManagerLib\.(?:g|gf|set_goal|set_goalfrag|set_suspended_goal'
    r'|new_goalstack|restart)\b'
    r'|(?<![\w.])(?:g|gf|set_goal|set_goalfrag|set_suspended_goal'
    r'|new_goalstack|restart)\s*[(`]'
)

# Term quotations (`...` / ``...``), SML string literals, and comments routinely
# contain a HOL variable `g` next to `(` or a closing backtick (e.g.
# ``EVAL ``LENGTH (g xs)`` `` or `"g(x)"`). Those are legitimate read-only
# queries, NOT goal creation. Blank out their CONTENTS (keeping the delimiters,
# so a real `g `tm`` still shows `g `` and matches) before scanning.
_QUOTE_SPAN_RE = re.compile(r'`+[^`]*`+')
_SML_STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
_SML_COMMENT_RE = re.compile(r'\(\*.*?\*\)', re.DOTALL)


def _strip_noncode(command: str) -> str:
    out = _SML_COMMENT_RE.sub(' ', command)
    out = _QUOTE_SPAN_RE.sub('``', out)
    out = _SML_STRING_RE.sub('""', out)
    return out


def _check_interactive_goal(command: str) -> str | None:
    """Reject hol_send commands that create a fresh interactive goal. None if allowed."""
    if not _INTERACTIVE_GOAL_RE.search(_strip_noncode(command)):
        return None
    return (
        "ERROR: hol_send BLOCKED — creating an interactive goal (g/gf/set_goal/"
        "set_goalfrag/new_goalstack) reconstructs a proof in the SCRATCH session.\n"
        "An interactive close says NOTHING about whether the FILE form replays "
        "(hol4-proving RULE G/I): the two diverge silently on goal order, "
        "prover-generated names, and type ambiguity, and are lost on compaction.\n"
        "\n"
        "Develop on the FILE instead:\n"
        "  1. Write the proof attempt (or a `cheat`/`>- suspend` frontier) into "
        "the *Script.sml.\n"
        "  2. hol_state_at(line,col) — replays the file prefix in order, shows the "
        "ACCURATE goal; probe with SHORT hol_send (ONE tactic) on that frontier.\n"
        "  3. hol_check_proof — validate the file form.\n"
        "Extract a stuck sub-fact as its own `Theorem foo[local]: ... QED` rather "
        "than reconstructing its goal with `g`."
    )


_UNDECLARED_RE = re.compile(
    r"(?:Value or constructor|Structure) \(([A-Za-z0-9_']+)\) has not been declared")


def _undeclared_name_hint(session: str, output: str) -> str | None:
    """When HOL rejects a name that is a theorem of the cursor's file at or
    after the parked position, say so: the name exists in the session only
    once navigation has passed its QED."""
    m = _UNDECLARED_RE.search(output)
    entry = _sessions.get(session) if m else None
    cursor = entry.cursor if entry else None
    if cursor is None:
        return None
    name = m.group(1)
    thm = cursor._get_theorem(name)
    loaded = cursor._loaded_to_line
    if thm is None or thm.start_line < loaded:
        return None
    parked = (f"in {cursor._active_theorem}" if cursor._active_theorem
              else "before the first theorem")
    # The line after a QED is between blocks and not navigable; the block is
    # admitted by navigating INTO the proof that follows it.
    later = [t for t in cursor._theorems if t.start_line > thm.start_line]
    following = min(later, key=lambda t: t.start_line) if later else None
    if following is not None:
        route = (f"navigate INTO the next proof, `{following.name}` — "
                 f"hol_state_at(line={following.proof_start_line}) — whose prefix "
                 f"admits `{name}`")
    else:
        route = (f"`{name}` is the file's last block, so no later proof admits it "
                 f"for hol_state_at; hol_check_proof(theorem=\"{name}\") validates it, "
                 f"and a consumer theorem added after it would bring it into scope")
    return (
        f"[hint: `{name}` is a {thm.kind if hasattr(thm, 'kind') else 'theorem'} "
        f"at line {thm.start_line} of {Path(cursor.file).name}, AFTER the parked "
        f"position (loaded through line {max(loaded - 1, 0)}, {parked}). A name "
        f"exists in the session only once navigation has passed its QED: {route}; "
        f"or work at a position where it is already in scope.]"
    )


_LOAD_USE_RE = re.compile(r'(?<![\w.])(load|use)\s*\(?\s*"')


def _check_load_use(command: str) -> str | None:
    """Reject `load "..."` / `use "..."` through hol_send. Either one changes
    what is in scope for the rest of the session behind the cursor's back:
    a theory the file does not declare resolves names the build will not,
    and a `use`d file is invisible to every later navigation and check."""
    m = _LOAD_USE_RE.search(_strip_noncode(command))
    if not m:
        return None
    verb = m.group(1)
    return (
        f"ERROR: hol_send BLOCKED — `{verb}` changes the session's scope behind "
        f"the cursor: names it brings in resolve here and not in the build, and "
        f"every later hol_state_at/hol_check_proof runs in a session the file "
        f"does not describe.\n"
        f"Put the dependency in the FILE — `Ancestors` (or `open fooTheory`) for "
        f"a theory, the script itself for SML helpers — then hol_state_at(file=...) "
        f"loads it for you; a missing built dependency is a holmake target, not a "
        f"load."
    )


def _check_proof_state_command(command: str) -> str | None:
    """Block hol_send commands that interact with proof state.

    Returns an error message if blocked, None if allowed.
    """
    cmd = command.strip()
    for pattern, name in _PROOF_STATE_PATTERNS:
        if pattern.search(cmd):
            return (
                f"ERROR: hol_send BLOCKED — '{name}' interacts with proof state.\n"
                f"\n"
                f"hol_send must ONLY be used for read-only queries:\n"
                f"  DB.match, DB.find, type_of, EVAL, printing theorems\n"
                f"\n"
                f"For proof development, use:\n"
                f"  hol_state_at(line, col) — navigate to position, see goals\n"
                f"  Edit tool — modify tactics in the file\n"
                f"  hol_check_proof — validate complete proofs\n"
            )
    return None


@mcp.tool()
@_serialized_session()
async def hol_send(command: str, timeout: int = 5, max_output: int = DEFAULT_MAX_OUTPUT, session: str = "default") -> str:
    """Send raw SML command to HOL session.

    Scope: SMALL probes only — test-drive a small tactic block at a parked
    frontier, fully close a small goal, inspect terms, check rewrites,
    evaluate expressions. NEVER drive a whole proof through hol_send: the
    interactive session and the file form diverge silently (prover-generated
    names, >> vs \\, parens, simp-set order) and the proof gets redone.
    Develop on the FILE — going deep means sub-suspend (>- suspend "X" +
    Resume), then jump with hol_state_at.

    For navigating an existing script file (replaying tactics from theorem
    start to a position), use hol_state_at — it handles file changes,
    checkpoints, and tactic replay automatically. For goal counts/slices use
    hol_goals; for DB searches use hol_search.

    Rejected mechanically: `val gs/fs/rw/simp/e/b/g/it/concl/hyp/dest_thm/
    tag/aconv/drop = ...` (shadows a HOL primitive for the rest of the
    session — bind a prefixed name like `val my_gs = ...` instead).

    Also rejected: creating an interactive goal (g/gf/set_goal/set_goalfrag/
    new_goalstack) — that reconstructs a proof in the scratch session, which
    says nothing about whether the FILE form replays (RULE G/I) and diverges
    silently. Develop on the file: hol_state_at to read the accurate goal,
    Edit to change tactics, hol_check_proof to validate. Short single-goal `e`
    probes on an already-navigated frontier stay allowed; `ef` does not count
    as one — it takes a frag_tactic, so running a tactic through it means
    goalFrag.expand/expandf, which apply to EVERY goal in the fragment.

    Also rejected: `load "..."` / `use "..."` — they change the session's scope
    behind the cursor. Dependencies belong in the file (`Ancestors`/`open`);
    hol_state_at(file=...) loads them.

    Args:
        command: SML command to execute
        session: Session name (default: "default")
        timeout: Max seconds to wait (default 5, max 600)
        max_output: Max bytes of output to return (default 4096).
                    Shows tail when truncated (errors/results come after echoed input).

    Returns: HOL output (may include errors), truncated if exceeds max_output
    """
    blocked = _check_proof_state_command(command)
    if blocked:
        return blocked

    blocked = _check_shadow_binding(command)
    if blocked:
        return blocked

    blocked = _check_interactive_goal(command)
    if blocked:
        return blocked

    blocked = _check_load_use(command)
    if blocked:
        return blocked

    s = await _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."

    if not s.is_running:
        _drop_dead_session(session)
        return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."

    # Validate timeout
    if timeout < 1:
        timeout = 1
    elif timeout > 600:
        timeout = 600

    t0 = time.monotonic()
    result = await s.send(command, timeout=timeout)
    elapsed = time.monotonic() - t0
    hint = _undeclared_name_hint(session, result)
    if hint:
        result = f"{result.rstrip()}\n{hint}"

    # If this command may have mutated the live proofManager, taint the cursor so
    # the next hol_state_at re-establishes its goal instead of reusing the now-
    # desynced cached position (see _PROOFMGR_MUTATING_RE).
    if _command_mutates_proof_state(command):
        entry = _sessions.get(session)
        if entry and entry.cursor:
            entry.cursor._session_dirty = True

    _schedule_gc(session)
    timing = f"\n[{elapsed:.3f}s]"
    return _truncate_output(result, max_output, footer=timing)


@mcp.tool()
@_serialized_session()
async def hol_search(
    query: str = None,
    pattern: str = None,
    theory: str = None,
    limit: int = 10,
    max_statement: int = 200,
    session: str = "default",
) -> str:
    """Search the theorem database by name and/or term pattern.

    First-class replacement for hol_send DB.find/DB.match probes: results
    come back as a compact `theory.name` + truncated-statement table.

    Args:
        query: Case-insensitive substring of the theorem name (DB.find).
        pattern: Term pattern, e.g. "MEM _ (MAP _ _)" (DB.match). When both
                 query and pattern are given, results must match both.
        theory: Restrict results to one theory (e.g. "list").
        limit: Max results shown (default 10; total count always reported).
        max_statement: Truncate each statement to this many chars (default 200).
        session: Session name (default: "default")

    Returns: Matching theorems with statements, or an error.
    """
    if not query and not pattern:
        return ("ERROR: provide query= (name substring) and/or "
                "pattern= (term pattern).")
    s = await _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."
    if not s.is_running:
        _drop_dead_session(session)
        return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."

    cmd = (
        f'db_search_json "{escape_sml_string(query or "")}" '
        f'"{escape_sml_string(pattern or "")}" '
        f'"{escape_sml_string(theory or "")}" {int(limit)};'
    )
    output = await s.send(cmd, timeout=30)
    data = _try_find_json_line(output)
    if 'err' in data:
        return f"ERROR: {data['err']}"
    if 'ok' not in data:
        return f"ERROR: unexpected db_search_json output: {output[:300]}"

    total = data['ok'].get('total', 0)
    results = data['ok'].get('results', [])
    if total == 0:
        return "No matches."
    header = f"{total} match(es)"
    if total > len(results):
        header += f", showing first {len(results)} (raise limit= for more)"
    lines = [header + ":"]
    for r in results:
        stmt = " ".join(str(r.get('statement', '')).split())
        if len(stmt) > max_statement:
            stmt = stmt[:max_statement] + " …"
        lines.append(f"{r.get('theory')}.{r.get('name')}")
        lines.append(f"  {stmt}")
    _schedule_gc(session)
    return "\n".join(lines)


@mcp.tool()
@_serialized_session()
@_budget_doc
async def hol_goals(
    n: int = None,
    asm: int = None,
    max_term: int = 300,
    file: str = None,
    line: int = None,
    col: int = 1,
    workdir: str = None,
    session: str = "default",
    skip_prefix: bool = False,
    timeout: float = None,
) -> str:
    """Goal count and structured goal slices, without a full top_goals() dump.

    Default: goal count plus a one-line headline per goal (truncated
    conclusion, assumption count). Drill down with n= and asm=.

    Args:
        n: Show goal n (1-based, 1 = top goal) with numbered assumptions.
        asm: With n, show assumption asm (1-based) of that goal in full.
        max_term: Truncate each shown term to this many chars (default 300).
        file: Script file — navigates like hol_state_at before reading goals
              (auto-inits the cursor when needed).
        line: With file (or an active cursor), position to navigate to first.
              Without line, reads the LIVE session goal state (works for
              hol_send-driven goals too).
        col: 1-indexed column for line (default 1).
        workdir: Working directory for HOL (used with file).
        session: Session name (default: "default")
        skip_prefix: With line, bind prefix theorems by cheat (statement only)
              instead of replaying — see hol_state_at for the full semantics.
              Off by default and never a shortcut (RULE K): the user
              pre-grants with `skip prefix ok`, otherwise H31 blocks the
              first use per file and a repeat is your logged decision.
              (default: False)
        timeout: With line, overall wall-clock budget (seconds) for the
              navigation; None uses the server default ({STATE_AT_TIMEOUT}s,
              set by HOL4_MCP_STATE_AT_TIMEOUT). On expiry HOL is interrupted
              and a TIMEOUT is returned
              instead of hanging. See hol_state_at. (default: None)

    Returns: Goal count + headlines, one goal, or one assumption.
    """
    cursor = await _get_cursor(session)

    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if line is not None:
        if not cursor:
            return (f"ERROR: No cursor for session '{session}'. "
                    f"Pass file= to auto-init.")
        bad_timeout = _timeout_arg_error(timeout)
        if bad_timeout:
            return bad_timeout
        result = await _state_at_bounded(cursor, line, col, skip_prefix=skip_prefix, timeout=timeout)
        if result.error and not result.goals:
            return f"ERROR: {result.error}"
        _complete, _structural, _broken = _classify_state_at(result)
        if _structural or _broken:
            # The goals on the stack belong to the point replay stopped at, not
            # to the requested position; presenting them as "N goal(s) at line
            # L" is the same false-green hol_state_at refuses.
            return (
                f"ERROR: PROOF BROKEN — replay stopped at step "
                f"{result.tactics_replayed} of {result.tactics_total}, before "
                f"line {line}. The goals on the stack are the failure point's, "
                f"not line {line}'s. Use hol_state_at(line={line}) to see where "
                f"and which tactic failed.\n{result.error}"
            )
        goals = result.goals
        origin = f"at line {line}"
        active = cursor._active_theorem
        caveats = await _state_caveat_lines(
            cursor, result, active,
            cursor._get_theorem(active) if active else None, line,
        )
        caveats = [*caveats, *_timing_lines(result)]
    else:
        s = await _get_session(session)
        if not s:
            return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."
        if not s.is_running:
            _drop_dead_session(session)
            return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."
        output = await s.send('goals_json();', timeout=10)
        data = _try_find_json_line(output)
        if 'err' in data:
            return f"No live proof: {data['err']}"
        if 'ok' not in data:
            return f"ERROR: unexpected goals_json output: {output[:300]}"
        goals = [
            g if isinstance(g, dict) and 'goal' in g
            else {"asms": [], "goal": str(g)}
            for g in data['ok']
        ]
        origin = "live session"
        caveats = []

    _schedule_gc(session)

    def qualified(text: str) -> str:
        """Append the caveats that qualify what these goals rest on."""
        return "\n".join([text, *caveats]) if caveats else text

    def trunc(s: str, limit: int, flatten: bool = True) -> str:
        if flatten:
            s = " ".join(s.split())
        if len(s) > limit:
            return s[:limit] + f" … [{len(s)} chars total]"
        return s

    if not goals:
        return qualified(f"0 goals ({origin}) — proof complete.")

    if n is None:
        lines = [f"{len(goals)} goal(s) ({origin}, goal 1 = top):"]
        for i, g in enumerate(goals, start=1):
            asms = g.get('asms', [])
            lines.append(f"{i}: [{len(asms)} asm] {trunc(g['goal'], max_term)}")
        if any(g.get('asms') for g in goals):
            lines.append("Use n=k for goal k's assumptions; n=k, asm=j for one in full.")
        return qualified("\n".join(lines))

    if n < 1 or n > len(goals):
        return f"ERROR: n={n} out of range (1..{len(goals)})"
    g = goals[n - 1]
    asms = g.get('asms', [])

    if asm is not None:
        if asm < 1 or asm > len(asms):
            return (f"ERROR: asm={asm} out of range "
                    f"(goal {n} has {len(asms)} assumptions)")
        return qualified(f"Goal {n} assumption {asm}:\n{asms[asm - 1]}")

    lines = [f"Goal {n} of {len(goals)} ({len(asms)} asm):"]
    for j, a in enumerate(asms, start=1):
        lines.append(f"  asm {j}: {trunc(a, max_term)}")
    if asms:
        lines.append("  " + "-" * 40)
    lines.append(f"  {trunc(g['goal'], max_term, flatten=False)}")
    return qualified("\n".join(lines))


@mcp.tool()
async def hol_interrupt(session: str = "default") -> str:
    """Stop the call running on a session (a runaway tactic, a stuck load).

    Cancels the call in progress — hol_state_at, hol_check_proof, hol_send,
    ... — which sends SIGINT to HOL (twice if needed) and re-aligns the pipe;
    that call then returns "INTERRUPTED: ..." instead of a result. Returns
    once it has. Says so when nothing was running, and when HOL used no CPU
    while the call waited (its reply was most likely lost). Never kills: HOL that
    ignores SIGINT is left running, marked busy, and nothing more is sent to
    it; hol_stop ends the session (the next call restarts HOL and reloads
    the prefix).

    Args:
        session: Session name (default: "default")

    Returns: What was interrupted, or that the session was idle
    """
    s = await _get_session(session)
    if not s:
        # A call may be starting the session (hol_start, auto-init) before
        # it is registered: that call is still interruptible.
        tool = await _preempt(session, "interrupt", wait=60)
        if tool:
            return (f"Interrupted the {tool} call that was starting session "
                    f"'{session}'; it returns \"INTERRUPTED: ...\".")
        return f"ERROR: Session '{session}' not found."

    if not s.is_running:
        _drop_dead_session(session)
        return f"ERROR: Session '{session}' died."

    still_busy = (f"HOL ignores SIGINT and is still running the command; nothing "
                  f"more is sent to it until it stops. hol_stop ends the session "
                  f"(the next call restarts HOL and reloads the prefix)."
                  + "".join(f"\n{line}" for line in _heap_pressure_lines(s) if line))
    operation = _session_operations.get(session)
    holder = operation.owner if operation is not None else None
    if holder is None or holder.done():
        if not s.busy:
            return (f"Session '{session}' is idle: no call is running on it, so "
                    f"there was nothing to interrupt.")
        if await s.interrupt_and_realign():
            return (f"Interrupted the command a timed-out call left running on "
                    f"session '{session}'; HOL is back at its prompt.")
        return f"Session '{session}': {still_busy}"

    computing = await s.is_computing()
    tool = await _preempt(session, "interrupt", wait=60, holder=holder)
    if tool is None:
        return f"Session '{session}': the running call finished before the interrupt."
    if not holder.done():
        return (f"Sent the interrupt to the {tool} call on session '{session}', "
                f"but it has not returned within 60s. hol_stop ends the session.")
    if s.busy:
        return f"Cancelled the {tool} call on session '{session}', but {still_busy}"
    idle = (" HOL used no CPU while that call waited: its reply had most likely "
            "been lost, unless the command was sleeping or blocked."
            if computing is False else "")
    return (f"Interrupted the {tool} call on session '{session}'; it returns "
            f"\"INTERRUPTED: ...\".{idle}")


@mcp.tool()
async def hol_stop(session: str = "default") -> str:
    """Terminate HOL session.

    Works while a call is running on it: that call is cancelled and returns
    "STOPPED: ...". Kills HOL (SIGTERM, then SIGKILL) without waiting for a
    command to stop, so it also ends one that ignores hol_interrupt. The next
    call on the session restarts HOL, with the session's env (hol_setenv),
    and reloads the prefix: from the script's last saved state when nothing
    it depends on changed (no dependency reload), else cold.

    Args:
        session: Session name (default: "default")

    Returns: Confirmation message
    """
    entry = _sessions.get(session)
    tool = await _preempt(session, "stop", wait=15)
    # While the cancelled call unwound, a queued call may have replaced the
    # entry: stop the session as it is now, and remove only that entry.
    current = _sessions.get(session) or entry
    if current is None:
        if tool:
            return (f"Stopped the {tool} call that was starting session "
                    f"'{session}'; it returns STOPPED.")
        return f"Session '{session}' not found."
    for stale in {id(e): e for e in (entry, current) if e is not None}.values():
        if stale.cursor:
            _gc_cursor_checkpoints(stale.cursor)
        await stale.session.stop()
    if _sessions.get(session) is current:
        del _sessions[session]
        _session_ended[session] = "was stopped by hol_stop"
    ended = f" The {tool} call running on it returns STOPPED." if tool else ""
    return f"Session '{session}' stopped.{ended}"


@mcp.tool()
async def hol_restart(session: str = "default") -> str:
    """Restart HOL session (stop + start, preserves workdir).

    Works while a call is running on it: that call is cancelled and returns
    "STOPPED: ...", and the restart does not wait for it to finish.

    Nothing in the ordinary loop needs it: hol_state_at/hol_check_proof detect
    edits to the current file, reload the session when an ancestor theory has
    been rebuilt ("[Session reloaded: ancestor ...]"), and move it to another
    workdir when file= points there ("[Session restarted: workdir ...]"). Hook
    H29 blocks a REPEAT stop/restart in the same theory directory within 30 min
    once (first stop, directory switches, and a stop right after a budget
    TIMEOUT or an H30 stale-ancestor refusal pass; a deliberate repeat passes
    and is logged for the user). The next call starts from the script's
    saved state when nothing it depends on changed, else reloads cold. "Corrupted state" is essentially never the cause: a weird replay
    is a proof or navigation error (RULE D) that restarting hides, and the
    restart also wipes the state that would have localised it.

    Args:
        session: Session name to restart

    Returns: hol_start's reply (cursor is cleared, use hol_state_at file= to
             re-init), plus a line when a running call was stopped
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found."

    tool = await _preempt(session, "restart", wait=15)
    if tool:
        # Its recovery stops HOL; make sure, so the guard is released.
        await entry.session.stop()
    # Hold the guard so no queued call runs between the stop and the start.
    try:
        async with _session_operation(session, "hol_restart"):
            # A queued call (a workdir switch, hol_setenv) may have replaced
            # the entry meanwhile: restart what is there now.
            entry = _sessions.get(session) or entry
            workdir, env = entry.workdir, _session_envs.get(session, entry.env)
            await hol_stop(session)
            # Replacing this session is not a second one: RULE J does not apply.
            started = await hol_start(workdir=str(workdir), name=session, env=env,
                                      force=True)
    except _Interrupted as cancelled:
        return _cancelled_call_text("hol_restart", cancelled.state, cancelled.intent)
    ended = f"\nThe {tool} call that was running returns STOPPED." if tool else ""
    return f"{started}{ended}"


@mcp.tool()
@_serialized_session()
async def hol_setenv(env: dict, session: str = "default") -> str:
    """Set environment variables for a HOL session and auto-restart to apply.

    These are passed to the HOL process and affect Holmakefile INCLUDES
    expansion; HOL4_MCP_MAXHEAP_MB sets the heap limit (see hol_start). They
    belong to the session name: every later start uses them, automatic
    restarts included.

    Example: hol_setenv({"VFMDIR": "/home/user/verifereum"})

    Args:
        env: Environment variables to set (merged with existing)
        session: Session name (default: "default")

    Returns: Confirmation message (includes restart output if session was running)
    """
    env = _session_env(env)
    if isinstance(env, str):
        return env
    merged = {**_session_envs.get(session, {}), **env}
    _session_envs[session] = merged
    entry = _sessions.get(session)
    if not entry:
        return (f"Environment set for session '{session}': {env}; it applies "
                f"when the session next starts.")
    entry.env = merged

    # Auto-restart to apply new env to running process
    if entry.session.is_running:
        restart_result = await hol_restart(session)
        return f"Environment updated and session restarted: {env}\n{restart_result}"

    return f"Environment updated for session '{session}': {env}"


async def _kill_process_group(proc):
    """Kill process group: SIGTERM, wait, SIGKILL if needed.

    Must kill even if parent exited - children (buildheap) may still be alive.
    """
    if proc is None:
        return

    pgid = proc.pid

    # Send SIGTERM to the whole process group
    try:
        os.killpg(pgid, signal.SIGTERM)
    except OSError:
        return  # Process group doesn't exist

    # Wait for processes to die gracefully (up to 1s)
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=1.0)
        except (asyncio.TimeoutError, asyncio.CancelledError):
            pass
    else:
        # Parent already exited, give children time to die from SIGTERM
        try:
            await asyncio.sleep(1.0)
        except asyncio.CancelledError:
            pass  # Still need to SIGKILL

    # SIGKILL anything remaining in the group
    try:
        os.killpg(pgid, signal.SIGKILL)
    except OSError:
        pass  # Already gone

    # Reap parent if needed
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=0.5)
        except:
            pass


def _signal_process_group(proc, sig: signal.Signals) -> bool:
    """Signal a build process group without competing to reap its parent."""
    if proc is None:
        return False
    try:
        os.killpg(proc.pid, sig)
        return True
    except OSError:
        return False


async def _kill_reaped_process_group(proc):
    """Stop children left behind after the detached build parent was reaped."""
    if not _signal_process_group(proc, signal.SIGTERM):
        return
    try:
        await asyncio.sleep(1.0)
    except asyncio.CancelledError:
        pass
    _signal_process_group(proc, signal.SIGKILL)


def _project_root(workdir: Path) -> Path | None:
    """The directory whose holproject.toml puts ``workdir`` in Holmake's
    project mode, or None."""
    for directory in (workdir, *workdir.parents):
        if (directory / "holproject.toml").is_file():
            return directory
    return None


async def _build_claim(holmake_bin, workdir, environment, target, timeout, trace_discovery=False, detach=False):
    """Discover without executing recipes, then reserve mutable dependencies.

    Explicit targets bypass --json in some Holmake versions. --dirs takes
    the graph-only path; select the requested target's closure ourselves.
    Pre-exec hooks run here so generated rules participate in discovery;
    the actual build disables them to avoid running them twice.
    """
    proc = None
    trace_note = ""
    clean = target in {"clean", "cleanDeps", "cleanAll"}
    try:
        # In project mode (a holproject.toml above the directory) Holmake
        # honours --json for a named target, whose graph needs no directory
        # scan: `--dirs .` rejects some Holmakefiles outright (a starred
        # script dependency) and prints one `Scanning` line per include
        # directory. Outside a project a named target makes Holmake BUILD
        # instead of printing the graph, so only the directory form is safe
        # there. A targeted run that yields no graph falls through.
        attempts = ([[str(holmake_bin), "--json", target]]
                    if target and not clean and _project_root(workdir) else [])
        attempts.append([str(holmake_bin), "--json", "--dirs", "."]
                        + (["--no_preexecs"] if clean else []))  # Native cleaning skips hooks.
        failure = ""
        for command in attempts:
            command, trace_note = traced_build(command, workdir, trace_discovery, environment)
            proc = await asyncio.create_subprocess_exec(
                *command,
                cwd=workdir, env=environment, stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE, start_new_session=True,
            )
            stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout)
            if proc.returncode == 0:
                try:
                    claim = claim_from_graph(stdout.decode("utf-8"), workdir, target)
                    break
                except ValueError as exc:
                    failure = f"{exc}"
            else:
                output = (stderr + stdout).decode("utf-8", errors="replace")
                heading = build_failure_heading(proc.returncode, output, bool(trace_note))
                failure = f"{heading}\n{output[-2000:]}"
            await _kill_process_group(proc)
            proc = None
        else:
            raise ValueError(failure)
        claim.detached = detach
        claim.preflight_output += _condense_discovery(stderr.decode("utf-8", errors="replace"))
        if claim.preflight_output.strip():
            discovery = claim.preflight_output.rstrip()
            claim.preflight_output = (
                "=== Dependency discovery / preexec output ===\n"
                f"{discovery}\n"
                "=== Build output (preexec already ran; disabled below) ===\n"
            )
    except asyncio.TimeoutError:
        return (f"ERROR: dependency preflight timed out after {timeout}s in {workdir}. "
                f"No build was started; this is not a proof verdict.\n{trace_note}").rstrip()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        return (f"ERROR: dependency preflight in {workdir}: {type(exc).__name__}: {exc}. "
                f"No build was started; this is not a proof verdict.\n{trace_note}").rstrip()
    finally:
        await _kill_process_group(proc)
    # No await between reservation and handoff: cancellation while cleaning
    # up the discovery process must not strand an unowned reservation.
    try:
        error = build_claims.register(claim)
        return error or claim
    except (OSError, ValueError) as exc:
        return f"ERROR: dependency reservation in {workdir}: {exc}. No build was started."


def _condense_discovery(text: str) -> str:
    """Holmake's per-directory `Scanning` lines say nothing its `Scanned N
    directories` trailer does not; keep the trailer and everything else."""
    lines = text.splitlines()
    scanning = sum(1 for line in lines if line.startswith("Scanning "))
    kept = [line for line in lines if not line.startswith("Scanning ")]
    if scanning and not any(line.startswith("Scanned ") for line in kept):
        kept.insert(0, f"Scanned {scanning} directories")
    return "\n".join(kept) + ("\n" if kept and text.endswith("\n") else "")


# Holmake's own out-of-store markers (`oos_markers` in its poly/multibuild.sml).
_OOS_MARKERS = ("Run out of store - interrupting threads", "Failed to recover - exiting")
_HOLMAKE_OOS_RETRIES_RE = re.compile(
    r"(\d+) job\(s\) were re-run after Poly/ML reported\s+running out of store")
_SEQUENTIAL_OOS_RETRY = ("[hol4-mcp: Poly/ML ran out of store; re-running this "
                         "sequential build once]")


def _build_summary(output: str) -> str:
    """One clause per outcome, from the jobs' verdict lines: what the build
    actually rebuilt and what failed, so the result reads from the top. An
    out-of-store retry, Holmake's per job or the server's of a sequential
    build, gets its own clause."""
    state = coordination.job_verdicts(output)
    done = sorted(tag for tag, verdict in state.items()
                  if verdict in coordination._SUCCESS_VERDICTS)
    failed = sorted(tag for tag, verdict in state.items() if verdict.startswith("FAIL"))
    retries = [f"{m.group(1)} job(s) re-run after Poly/ML ran out of store"
               for m in _HOLMAKE_OOS_RETRIES_RE.finditer(output)]
    if _SEQUENTIAL_OOS_RETRY in output:
        retries.append("re-run once after Poly/ML ran out of store")
    if not done and not failed and not retries:
        return ""

    def show(names):
        return ", ".join(names[:8]) + (f" (+{len(names) - 8} more)" if len(names) > 8 else "")

    parts = []
    if done:
        parts.append(f"built {len(done)}: {show(done)}")
    if failed:
        parts.append(f"failed {len(failed)}: {show(failed)}")
    parts.extend(retries)
    return " " + "; ".join(parts) + "."


def _progress_lines(tags: dict, output: str) -> list[str]:
    """For each job the log shows started and not finished, the tail of
    Holmake's per-job log — where a theory's own output goes while it
    builds — so a long single-theory build is not a blank `Starting work on`."""
    out = []
    for tag, verdict in coordination.job_verdicts(output).items():
        if verdict != "started":
            continue
        directories = {coordination._unit_directory(Path(p)) for p in tags.get(tag, ())}
        for directory in sorted(directories):
            log = directory / ".hol" / "logs" / tag
            try:
                text, _ = _read_log_tail(log, 600)
                age = time.time() - log.stat().st_mtime
            except OSError:
                continue
            last = [line for line in text.splitlines() if line.strip()][-3:]
            out.append(f"[in progress: {tag} — {log} (last write {age:.0f}s ago)]")
            out.extend(f"  {line[:200]}" for line in last)
            break
        else:
            out.append(f"[in progress: {tag}]")
    return out[:12]


def _read_log_tail(path: Path, limit: int) -> tuple[str, bool]:
    """Read at most limit bytes; nonpositive limits explicitly request all."""
    with path.open("rb", buffering=0) as stream:
        if limit > 0:
            size = stream.seek(0, os.SEEK_END)
            stream.seek(max(0, size - limit))
            data = stream.read(limit)
            truncated = size > limit
        else:
            data = stream.read()
            truncated = False
    return data.decode("utf-8", errors="replace"), truncated


@mcp.tool()
@_budget_doc
async def holmake(workdir: str, target: str = None, env: dict = None, log_limit: int = 1024, timeout: int = budgets.HOLMAKE_TIMEOUT, heap_size: int = 12288, jobs: int = None, detach: bool = False, trace_discovery: bool = False) -> str:
    """Run Holmake --qof in directory.

    Name the target (hook H32 blocks an untargeted, whole-directory build once;
    it is the user's call, pre-grantable with `build ok`).

    Args:
        workdir: Directory containing Holmakefile
        target: Specific target to build (e.g. "fooTheory")
        env: Optional environment variables (e.g. {"MY_VAR": "/some/path"})
        log_limit: Max bytes per log file to include on failure (default 1024,
                   0 for unlimited)
        timeout: Max seconds to wait (default {HOLMAKE_TIMEOUT}, max
                 {MAX_HOLMAKE_TIMEOUT}). Ignored with detach.
        heap_size: Max heap size in MB for Poly/ML builds (default 12288)
        jobs: Max parallel jobs, passed as -j — jobs=1 included, which forces
              a sequential build in which Holmake streams each theory's
              output inline and writes no per-theory .hol/logs. Overrides
              HOL4_MCP_HOLMAKE_JOBS in env, then the inherited environment;
              unset: Holmake's own default (parallel, with .hol/logs).
        detach: After dependency discovery, start the build in the background with
                `job=<id>` and the log path; poll hol_build_status(job=...).
                For builds longer than the synchronous budget — never a shell
                `nohup Holmake` (hook H28), which nothing reports on.
                Discovery has its own {DETACHED_DISCOVERY_TIMEOUT}-second safety
                limit for detached jobs.
        trace_discovery: Opt-in Linux/strace diagnostic for opaque filesystem
                or discovery failures (e.g. SysErr noent). Retains syscall/path
                evidence and execution-context metadata under
                /var/tmp/hol4-mcp-<uid>/discovery (newest five kept). Adds
                overhead; defaults to False. One traced run is the whole
                diagnostic: do not retrace retries. Does not ignore missing
                sources or retry a filesystem failure.

    Returns: Holmake output (stdout + stderr). On failure, includes recent build logs.
             With detach: the job id and log path.

    Poly/ML sometimes runs out of store with memory to spare; a re-run
    usually succeeds. Holmake re-runs such a job once in a parallel build,
    and a jobs=1 build that fails this way is re-run once here, detached
    included. The summary line names each retry; a second failure is
    reported as is.

    Before recipes run, checks the requested target's dependency graph. Refuses
    an overlap with another MCP build on the same host and user on an artifact
    unit (the files one job writes for a target) that either build writes;
    read-only dependencies may be shared, and independent theories in one
    directory build concurrently. The error names the blocking job/build and
    units; wait for it to finish, then retry.
    When a build fails or is cancelled, each changed output is judged on its
    own: one whose Holmake job reported success keeps its standing, as do the
    .uo/.ui files Holmake compiles in its own process when Holmake exited
    normally or a sequential build stopped while a theory script ran; the
    rest may be partial or unverified and cannot be reused
    unchanged as up-to-date dependencies. A sequential `jobs=1` build prints
    no per-job verdicts: its theories are judged by Holmake's progress lines,
    a shell target by a later target having begun, and a quiet (`@`) recipe
    only by the exit status. Records, locks, detached-job logs with their exit
    statuses and discovery traces all live under /var/tmp/hol4-mcp-<uid>/,
    never in the project tree, and survive server restarts. Inspect/remove
    and rebuild suspect outputs, or use a build whose graph explicitly
    schedules their reconstruction. Remove a suspect under $HOLDIR only when
    the refusal says it may be removed; otherwise that is the user's to do.
    A detached job's record lets a server
    started later adopt it: hol_build_status reports or cancels it, and a
    build that meets its outputs applies its exit status before judging them.
    Requires Holmake's --json/--dirs graph interface. External build processes
    and undeclared recipe/pre-exec outputs are outside this coordination.
    """
    # Validate limits
    timeout = max(1, min(timeout, budgets.MAX_HOLMAKE_TIMEOUT))
    heap_size = max(256, heap_size)
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Directory does not exist: {workdir}"

    holmake_bin = HOLDIR / "bin" / "Holmake"
    if not holmake_bin.exists():
        return f"ERROR: Holmake not found at {holmake_bin}"

    logs_dir = workdir_path / ".hol" / "logs"

    # Preserve prior/peer build evidence. The native target locks coordinate
    # writers, but deleting a directory's logs here bypasses those locks.
    # For the optional failure excerpt below, consider only changed logs.
    def log_stamp(path):
        try:
            st = path.stat()
            return st.st_mtime_ns, st.st_ctime_ns, st.st_size, st.st_ino
        except FileNotFoundError:
            return None

    prior_logs = {p: log_stamp(p) for p in logs_dir.glob("*") if p.is_file()}

    # Resolve against the environment actually passed to the child.
    proc_env = os.environ.copy()
    if env:
        proc_env.update(env)
    setting = "HOL4_MCP_HOLMAKE_JOBS" if jobs is None else "jobs"
    value = proc_env.get(setting) if jobs is None else jobs
    if value is not None:
        try:
            jobs = max(1, int(value))
        except (TypeError, ValueError):
            return f"ERROR: {setting} must be an integer, got {value!r}. No build was started."

    cmd = [str(holmake_bin), "--no_preexecs", "--qof", f"--heap-size={heap_size}"]
    if jobs != 1:
        # Holmake ignores it, with a warning, under -j1.
        cmd.append("--retry-oos=1")
    if jobs is not None:
        cmd.extend(["-j", str(jobs)])
    if target:
        cmd.append(target)

    try:
        cmd, trace_note = traced_build(cmd, workdir_path, trace_discovery, proc_env)
    except (OSError, ValueError) as exc:
        return f"ERROR: preparing build diagnostics in {workdir_path}: {exc}"

    start_time = time.monotonic()
    claim = await _build_claim(holmake_bin, workdir_path, proc_env, target,
                               budgets.DETACHED_DISCOVERY_TIMEOUT if detach else timeout,
                               trace_discovery, detach)
    if isinstance(claim, str):
        return claim
    if not detach and time.monotonic() - start_time >= timeout:
        # Discovery used the whole budget: a build spawned now would be
        # killed a moment into a recipe.
        build_claims.finish(claim)
        return f"ERROR: Build timed out after {timeout}s.\n{trace_note}"
    # A synchronous build is a detached job the call waits for: its job
    # record and exit status outlive this server, so a later one can adopt it.
    try:
        started = await _start_detached_build(cmd, workdir_path, proc_env, target, trace_note,
                                              claim, retry_out_of_store=jobs == 1)
    except BaseException:
        build_claims.finish(claim)
        raise
    if detach:
        return started

    job = _build_jobs[claim.token]
    try:
        try:
            await asyncio.wait_for(asyncio.shield(job.done.wait()),
                                   max(0.0, timeout - (time.monotonic() - start_time)))
        except asyncio.TimeoutError:
            return f"ERROR: Build timed out after {timeout}s.\n{trace_note}"
        wall = time.monotonic() - start_time
        returncode = job.proc.returncode
        output = _condense_discovery(_read_log_tail(job.log, 0)[0])
        if returncode == 0:
            result = f"Build succeeded.{_build_summary(output)}\n\n{output}"
            if env:
                # Store env in matching session entries for auto-holmake at startup
                for entry in _sessions.values():
                    if entry.workdir == workdir_path:
                        entry.holmake_env = env
                # Include env in output for caller to capture if needed
                result += f"\nHOLMAKE_ENV: {json.dumps(env)}"
            return f"{result}\n[{wall:.1f}s]\n{trace_note}".rstrip()

        # Shared-directory logs may also have changed in a peer build. Label
        # this honestly; the command's own output above is authoritative.
        result = (build_failure_heading(returncode, output, bool(trace_note))
                  + _build_summary(output) + f"\n\n{output}")

        if logs_dir.exists():
            logs = sorted(
                [f for f in logs_dir.iterdir()
                 if f.is_file() and log_stamp(f) != prior_logs.get(f)],
                key=lambda f: -f.stat().st_mtime
            )
            if logs:
                result += ("\n\n=== Build Logs ===\n"
                           "Changed during this build; may include concurrent jobs.\n")
                for log_file in logs[:3]:
                    content, truncated = _read_log_tail(log_file, log_limit)
                    if truncated:
                        content = f"...(truncated, showing last {log_limit} bytes)...\n" + content
                    result += f"\n--- {log_file.name} ---\n{content}\n"

        if re.search(r"\b(?:noent|ENOENT|SysErr)\b", output) and not trace_note:
            result += ("\nFilesystem/discovery failure: this is not a proof verdict. "
                       f"Workdir={workdir_path}. For syscall/path evidence, ONE run "
                       "with trace_discovery=True is the whole diagnostic (it keeps a "
                       "full strace log; do not retrace retries); do not infer the "
                       "failing path from the last printed directory.")
        return f"{result}\n[{wall:.1f}s]\n{trace_note}".rstrip()

    except Exception as e:
        return f"ERROR: build in {workdir_path}: {type(e).__name__}: {e}\n{trace_note}".rstrip()
    finally:
        # Whatever ended the call — a timeout or a client abort included —
        # the build stops, and its reaper releases the reservation.
        if not job.done.is_set():
            await asyncio.shield(_stop_build_job(job))


@dataclass
class _BuildJob:
    proc: asyncio.subprocess.Process
    workdir: Path
    target: str | None
    log: Path
    started: float
    finished: float | None = None
    trace_note: str = ""
    claim: object = None
    done: asyncio.Event = field(default_factory=asyncio.Event)
    cancel_requested: bool = False
    # The whole log, judged once when the job ends: a status poll then reads
    # only the bytes it returns.
    full_log_verdict: str | None = None


_build_jobs: dict[str, _BuildJob] = {}


async def _stop_build_job(job: _BuildJob) -> None:
    """Kill a job's process group (SIGTERM, then SIGKILL) and wait briefly
    for its reaper to release the reservation."""
    job.cancel_requested = True
    _signal_process_group(job.proc, signal.SIGTERM)
    try:
        await asyncio.wait_for(job.done.wait(), timeout=2.5)
    except asyncio.TimeoutError:
        _signal_process_group(job.proc, signal.SIGKILL)
        try:
            await asyncio.wait_for(job.done.wait(), timeout=1.0)
        except asyncio.TimeoutError:
            pass


async def _start_detached_build(cmd: list[str], workdir_path: Path, proc_env: dict,
                                target: str | None, trace_note: str = "", claim=None,
                                retry_out_of_store: bool = False) -> str:
    """Spawn Holmake with its output on a log file under `.hol/` and register
    it as a job for hol_build_status. With ``retry_out_of_store``, a run that
    fails with Poly/ML's out-of-store message is re-run once."""
    import uuid
    job_id = claim.token if claim is not None else uuid.uuid4().hex[:12]
    log_dir = coordination.builds_directory()
    coordination.prune_builds()
    log = log_dir / f"{job_id}.log"
    # A shell wrapper outlives Holmake just long enough to record its exit
    # status, so a server started later can tell a finished job from a lost
    # one. Killing the process group kills the wrapper too: no status, which
    # is the honest answer for a cancelled build.
    exit_file = log_dir / f"{job_id}.exit"
    exit_file.unlink(missing_ok=True)
    import shlex
    markers = " ".join(f"-e {shlex.quote(m)}" for m in _OOS_MARKERS)
    # Only the first run's output decides a retry, not the preflight text
    # before it.
    wrapped = ["/bin/sh", "-c",
               'log=$1; shift; n=0; [ -n "$log" ] && n=$(wc -c < "$log"); "$@"; s=$?; '
               f'if [ "$s" -ne 0 ] && [ -n "$log" ] && '
               f'tail -c +$((n + 1)) "$log" | grep -qF {markers}; then '
               f'printf "\\n%s\\n" {shlex.quote(_SEQUENTIAL_OOS_RETRY)}; "$@"; s=$?; fi; '
               'printf %s "$s" > "$0.tmp" && mv -f "$0.tmp" "$0"; exit "$s"',
               str(exit_file), str(log) if retry_out_of_store else "", *cmd]
    log_fh = open(log, "wb")
    try:
        if claim is not None:
            log_fh.write(claim.preflight_output.encode("utf-8"))
            log_fh.flush()
        proc = await asyncio.create_subprocess_exec(
            *wrapped, cwd=workdir_path, env=proc_env,
            stdout=log_fh, stderr=asyncio.subprocess.STDOUT,
            start_new_session=True,
            pass_fds=tuple(claim.lock_fds) if claim is not None else (),
        )
    finally:
        log_fh.close()
    started = time.time()
    if claim is not None:
        claim.proc = proc
        claim.detached = True
        claim.log = log
        try:
            coordination.write_job(coordination.job_record(
                claim, pid=proc.pid, target=target, log=log, exit_file=exit_file,
                trace_note=trace_note, started=started))
        except OSError as exc:
            claim.state_error = f"Build job record could not be written: {exc}"
    job = _BuildJob(proc=proc, workdir=workdir_path, target=target, log=log,
                    started=started, trace_note=trace_note, claim=claim)
    _build_jobs[job_id] = job

    async def _reap():
        try:
            # This task is the sole waiter for a detached process.  asyncio's
            # subprocess transport can strand one of two concurrent waiters,
            # leaving the build reservation live after cancellation.
            await proc.wait()
            await _kill_reaped_process_group(proc)
        finally:
            try:
                try:
                    output = _read_log_tail(log, 0)[0]
                except OSError:
                    output = None
                if output is not None:
                    job.full_log_verdict = (
                        ("Build succeeded" if proc.returncode == 0 else
                         build_failure_heading(proc.returncode, output, bool(trace_note)))
                        + f".{_build_summary(output)}")
                if claim is not None:
                    build_claims.finish(claim, output or "")
                    coordination.record_finalized(claim.token, proc.returncode)
            finally:
                job.finished = time.time()
                job.done.set()
    asyncio.create_task(_reap())
    return (f"Build started in background: job={job_id} target={target or '(all)'} "
            f"workdir={workdir_path}\nlog={log}\n{trace_note}\n"
            f"Poll hol_build_status(job=\"{job_id}\"); it reports running/done "
            f"with the log tail, and cancel=True stops it.")


async def _adopted_build_status(job: str, cancel: bool, tail: int, wait: int = 0) -> str:
    """Report a job this server did not start, from the record its starter
    left: running, done (its wrapper recorded Holmake's exit status, applied
    to its outputs here), cancelled, or lost — controller and process both
    gone with no status, so its changed outputs stay suspect until rebuilt.
    A token naming one of this server's synchronous builds is reported too,
    so the overlap check and this tool agree on what exists."""
    record = coordination.read_job(job)
    if record is None:
        claim = build_claims.active.get(job)
        if claim is not None:
            return (f"active (synchronous build in this server): {claim.label}, started "
                    f"{time.time() - claim.created:.0f}s ago. It ends when its holmake "
                    f"call returns; the reservation is released then, or reaped by the "
                    f"next build if the call was abandoned.")
        known = ", ".join(sorted(_build_jobs)) or "none"
        return (f"ERROR: unknown build job '{job}' (known to this server: {known}; "
                f"no record of it on this host).")
    returncode = coordination.job_exit_status(record)
    alive = returncode is None and coordination.process_alive(record)
    if wait and alive and not cancel:
        deadline = time.monotonic() + wait
        while time.monotonic() < deadline and alive:
            await asyncio.sleep(0.5)
            returncode = coordination.job_exit_status(record)
            alive = returncode is None and coordination.process_alive(record)
    cancelled = False
    if cancel and alive:
        cancelled = True
        for sig, grace in ((signal.SIGTERM, 2.5), (signal.SIGKILL, 1.0)):
            try:
                os.killpg(record["pid"], sig)
            except OSError:
                break
            deadline = time.monotonic() + grace
            while time.monotonic() < deadline and coordination.process_alive(record):
                await asyncio.sleep(0.05)
            if not coordination.process_alive(record):
                break
        alive = coordination.process_alive(record)
        returncode = coordination.job_exit_status(record)
    log = Path(record["log"])
    try:
        text = _read_log_tail(log, tail)[0] if tail > 0 else ""
        full = _read_log_tail(log, 0)[0]
    except OSError:
        text = full = ""
    finalized = record.get("finalized")
    if not finalized and (returncode is not None or (cancelled and not alive)):
        try:
            coordination.finalize_job(record, returncode, full)
            finalized = record["finalized"]
        except (OSError, ValueError, KeyError, TypeError) as exc:
            text = f"WARNING: build coordination state could not be finalized: {exc}\n\n{text}"
    if returncode is not None:
        state = "done"
    elif cancelled and not alive:
        state = "cancelled"
    elif alive:
        state = "running"
    else:
        state = "lost"
    end = finalized["at"] if finalized else time.time()
    elapsed = end - record.get("started", end)
    head = (f"{state} (adopted: started by a previous MCP server): job={job} "
            f"target={record.get('target') or '(all)'} workdir={record['workdir']} "
            f"[{elapsed:.0f}s]")
    if state == "done":
        verdict = ("Build succeeded" if returncode == 0 else
                   build_failure_heading(returncode, full, bool(record.get("trace_note"))))
        head += f"\n{verdict}.{_build_summary(full)}"
    elif state == "lost":
        head += ("\nThe controller and the build process are both gone and no exit "
                 "status was recorded: its changed outputs stay suspect until rebuilt.")
    elif state == "running":
        head += "".join(f"\n{line}" for line in _progress_lines(record.get("tags", {}), full))
    return f"{head}\nlog={log}\n{record.get('trace_note', '')}\n\n{text}".rstrip()


@mcp.tool()
async def hol_build_status(job: str, cancel: bool = False, tail: int = 2000,
                           wait: int = 0, retire: bool = False) -> str:
    """Status of a detached holmake job (holmake(detach=True)).

    Args:
        job: Job id from the detached holmake call
        cancel: Kill the build's process group (default False)
        retire: Move the coordination records of a LOST build (one a build
                refusal names as lost) aside, so its files are no longer
                suspect and are trusted as they are. Refused while the build
                may still be running. Ask the user first: only they know
                whether the files were rebuilt since.
        tail: Bytes of log to include (default 2000, 0 to omit the log)
        wait: Seconds to block for the job to end before reporting (0–100;
              default 0). One call then covers up to 100 s of a long build
              instead of a poll per turn; the bound keeps the call inside a
              client's own tool timeout.

    Returns: job state with elapsed time, exit code and the log tail; a done
             job's line says `Build succeeded` or `Build failed` and
             summarises what its jobs built. While a theory is in progress,
             the tail of its own per-theory log (.hol/logs/<thy>) follows the
             state line. Cancellation is not reported complete until the
             reaper releases its claim. A job started by a previous MCP
             server (replaced or crashed) is adopted from its on-disk record
             and reported as running, done (its exit status is applied to its
             outputs), cancelled or lost; the token of one of this server's
             synchronous builds is reported as active.
    """
    if retire:
        running = _build_jobs.get(job)
        if job in build_claims.active or (running is not None and not running.done.is_set()):
            return f"ERROR: build={job} is running in this server: nothing was retired."
        try:
            count, where = coordination.retire_build(job)
        except (OSError, ValueError) as exc:
            return f"ERROR: {exc}"
        if not count:
            return f"No coordination records of build={job} remain: nothing to retire."
        return (f"retired build={job}: moved {count} coordination records to {where}. "
                f"Its files are no longer suspect; builds trust them as they are.")
    wait = max(0, min(int(wait or 0), 100))
    entry = _build_jobs.get(job)
    if entry is None:
        return await _adopted_build_status(job, cancel, tail, wait)
    proc = entry.proc
    if wait and not cancel and not entry.done.is_set():
        try:
            await asyncio.wait_for(entry.done.wait(), timeout=wait)
        except asyncio.TimeoutError:
            pass
    if cancel and not entry.done.is_set() and proc.returncode is None:
        await _stop_build_job(entry)
    if entry.done.is_set():
        state = "cancelled" if entry.cancel_requested else "done"
    elif entry.cancel_requested:
        state = "cancellation pending"
    elif proc.returncode is None:
        state = "running"
    else:
        # The reaper has observed process exit and is cleaning up descendants
        # before releasing the build reservation.
        state = "finishing"
    end = entry.finished or time.time()
    elapsed = end - entry.started
    # The log is read once, bounded by `tail`. A done job's verdict and
    # summary were drawn from its whole log when it ended; progress comes
    # from the text returned.
    truncated = False
    try:
        text, truncated = _read_log_tail(entry.log, tail) if tail > 0 else ("", False)
    except OSError:
        text = ""
    head = f"{state}: job={job} target={entry.target or '(all)'} workdir={entry.workdir} [{elapsed:.0f}s]"
    if entry.claim is not None and entry.claim.state_error:
        head += f"\nWARNING: {entry.claim.state_error}"
    if state == "done" and entry.full_log_verdict is not None:
        head += f"\n{entry.full_log_verdict}"
    elif state == "done":
        verdict = ("Build succeeded" if proc.returncode == 0 else
                   build_failure_heading(proc.returncode, text, bool(entry.trace_note)))
        summary = _build_summary(text)
        head += f"\n{verdict}.{summary}" + (
            " (within the returned log tail)" if summary and truncated else "")
    elif state == "running":
        tags = entry.claim.tags if entry.claim is not None else {}
        head += "".join(f"\n{line}" for line in _progress_lines(tags, text))
    return f"{head}\nlog={entry.log}\n{entry.trace_note}\n\n{text}".rstrip()


@mcp.tool()
async def hol_log(workdir: str, theory: str, limit: int = 1024) -> str:
    """Read build log for a specific theory.

    Use after holmake to inspect warnings or errors in detail.

    Args:
        workdir: Directory containing .hol/logs/
        theory: Theory name (e.g., "fooTheory")
        limit: Max bytes to return (default 1024, 0 for unlimited)

    Returns: Log file contents (tail if truncated).
    """
    workdir_path = Path(workdir).resolve()
    log_file = workdir_path / ".hol" / "logs" / theory

    if not log_file.exists():
        # Try without "Theory" suffix
        log_file = workdir_path / ".hol" / "logs" / f"{theory}Theory"
        if not log_file.exists():
            available = []
            logs_dir = workdir_path / ".hol" / "logs"
            if logs_dir.exists():
                available = [f.name for f in logs_dir.iterdir() if f.is_file()]
            if available:
                return f"Log not found: {theory}\nAvailable: {', '.join(sorted(available))}"
            return f"Log not found: {theory}\nNo logs in {logs_dir}"

    content, truncated = _read_log_tail(log_file, limit)
    if truncated:
        return f"...(truncated, showing last {limit} bytes)...\n{content}"
    return content


@mcp.tool()
async def hol_logs(workdir: str) -> str:
    """List available build logs.

    Args:
        workdir: Directory containing .hol/logs/

    Returns: List of log files with sizes and modification times
    """
    workdir_path = Path(workdir).resolve()
    logs_dir = workdir_path / ".hol" / "logs"

    if not logs_dir.exists():
        return f"No logs directory: {logs_dir}"

    logs = []
    for log_file in sorted(logs_dir.iterdir()):
        if log_file.is_file():
            stat = log_file.stat()
            size = stat.st_size
            mtime = datetime.fromtimestamp(stat.st_mtime).strftime("%H:%M:%S")
            logs.append(f"  {log_file.name}: {size} bytes, modified {mtime}")

    if not logs:
        return "No log files found."
    return "Build logs:\n" + "\n".join(logs)


# =============================================================================
# Cursor Tools (for multi-theorem files)
# =============================================================================


@_serialized_session()
async def _init_file_cursor(
    file: str,
    session: str = "default",
    workdir: str = None,
) -> str:
    """Initialize cursor for a HOL4 script file (internal helper).

    Parses file for theorems and their proofs. Auto-starts HOL session if needed.
    After init, use hol_state_at to navigate to specific positions and see goals.

    Args:
        file: Path to *Script.sml file containing theorems
        session: Session name (default: "default")
        workdir: Working directory for HOL (default: file's parent directory)

    Returns: List of theorems with line numbers and cheat status
    """
    # Validate file first
    file_path = Path(file).resolve()
    if not file_path.exists():
        return f"ERROR: File not found: {file}"

    # Determine target workdir
    target_workdir = Path(workdir).resolve() if workdir else file_path.parent

    # Auto-start or restart session if workdir changed or file content changed
    s = await _get_session(session)
    entry = _sessions.get(session)
    notices: list[str] = []
    t_begin = time.perf_counter()

    if s and s.is_running:
        # Workdir switch: one session at a time (RULE J), so the session
        # moves with the file. The previous workdir's loaded context and open
        # suspensions do not survive; the notice says so.
        if entry and entry.workdir != target_workdir:
            notices.append(
                f"[Session restarted: workdir {entry.workdir} → {target_workdir}; "
                f"the previous workdir's loaded context and open suspensions "
                f"were dropped]"
            )
            await hol_stop(session)
            s = None
        # Check if file content changed - session has stale definitions
        elif entry and entry.cursor:
            old_cursor = entry.cursor
            old_file = Path(old_cursor.file).resolve()
            if old_file == file_path:
                # Same file - check if content changed
                old_hash = old_cursor._content_hash
                new_content = file_path.read_text(encoding="utf-8")
                new_hash = hashlib.sha256(new_content.encode()).hexdigest()
                if old_hash and new_hash != old_hash:
                    # File changed - restart session to clear stale definitions
                    await hol_stop(session)
                    s = None
            else:
                # Another script in the same workdir. A fresh process, so
                # nothing the previous file loaded or defined (theorems, SML
                # bindings, open suspensions) is visible to this one.
                notices.append(
                    f"[Session restarted: file {old_file.name} → {file_path.name}; "
                    f"the previous file's loaded context and open suspensions "
                    f"were dropped]"
                )
                await hol_stop(session)
                s = None

    ended = None
    if not s or not s.is_running:
        # The session's env (hol_start/hol_setenv) applies to every start.
        start_env = _session_envs.get(session) or (entry.env if entry else None)
        ended = _session_ended.get(session) if entry is None else None
        # Replacing an existing session is not a second one (RULE J).
        start_result = await hol_start(workdir=str(target_workdir), name=session,
                                       env=start_env, force=entry is not None)
        if start_result.startswith("ERROR"):
            return start_result
        s = await _get_session(session)

    # GC stale per-theorem checkpoints from old cursor before replacing
    if entry and entry.cursor:
        _gc_cursor_checkpoints(entry.cursor)

    t0 = time.perf_counter()
    
    cursor = FileProofCursor(file_path, s, tactic_timeout=TACTIC_TIMEOUT)
    try:
        result = await cursor.init(reuse=True)
    except BaseException:
        # The process may now hold this cursor's deps and base saves in its
        # SaveState hierarchy, which no later cursor can save over: keep
        # this one, and let its next call rebuild the session.
        cursor._schedule_full_reinit("session reinit: the previous start was interrupted")
        if session in _sessions:
            _sessions[session].cursor = cursor
        raise

    init_time = time.perf_counter() - t0
    cursor._startup_seconds = time.perf_counter() - t_begin
    cursor._startup_cause = ("warm start: HOL start and a previous session's saved state"
                             if cursor._reused_state else
                             "cold init: HOL start and dependency load")
    if ended:
        notices.append(
            f"[Session started: the previous '{session}' session {ended}; "
            f"HOL heap {s.maxheap_mb} MB; "
            + ("the prefix resumes from the reused state]" if cursor._reused_state
               else "the prefix reloads from line 1]"))
    cursor._session_notices.extend(notices)

    _sessions[session].cursor = cursor

    if result.get("error"):
        err_lines = [f"ERROR: {result['error']}"]
        err_lines.extend(_failure_evidence_lines(s))
        err_lines.extend(
            _quote_diagnosis_if_parse_error(file_path, result['error'])
        )
        return "\n".join(err_lines)

    # Build status output
    lines = [
        f"File: {file_path}",
        f"Theorems: {len(result['theorems'])} ({len(result['cheats'])} cheats)",
    ]

    if result['cheats']:
        lines.append("")
        lines.append("Cheats to fix:")
        for cheat in result['cheats']:
            lines.append(f"  {cheat['theorem']} (line {cheat['line']})")

    lines.append("")
    lines.append(f"[Init time: {init_time*1000:.0f}ms]")

    return "\n".join(lines)


@mcp.tool()
@_serialized_session()
@_budget_doc
async def hol_state_at(
    line: int,
    col: int = 1,
    file: str = None,
    workdir: str = None,
    max_output: int = DEFAULT_MAX_OUTPUT,
    session: str = "default",
    show_partial: bool = False,
    all_goals: bool = False,
    context_before: int = 0,
    context_after: int = 0,
    skip_prefix: bool = False,
    timeout: float = None,
) -> str:
    """Get proof state at a file position.

    Replays tactics from theorem start up to (but not including) the tactic at
    the given position, then shows current goals. Auto-enters theorem if needed.

    By default only the top goal is shown (with total count). Set all_goals=True
    to see every goal on the stack.

    If replay fails before reaching the requested position, the default behavior
    is to refuse to show goals (they would be from the wrong proof state).
    Set show_partial=True to see the best-effort goals anyway.

    Args:
        line: 1-indexed line number (position in the proof)
        col: 1-indexed column number (default 1)
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        max_output: Max characters of output (default 4096)
        session: Session name (default: "default")
        show_partial: If True, show best-effort goals even when replay fails
                      before reaching the requested position (default: False)
        all_goals: If True, show all goals; otherwise only the top goal (default: False)
        context_before: On PROOF BROKEN, number of source lines before the failure
                       to include in the step plan context (default: 0, off).
                       The failing step is always shown; this adds steps whose
                       source positions fall within the line range.
        context_after: On PROOF BROKEN, number of source lines after the failure
                      to include in the step plan context (default: 0, off).
                      Both default to 0 (only failing step shown); pass e.g. 3
                      for surrounding context.
        skip_prefix: If True, bind every theorem BEFORE the target via `cheat`
                      (statement only) instead of replaying it — instant
                      navigation into a target in a cold/unbuilt theory whose
                      earlier proofs are slow or non-terminating. The target's
                      own tactics still replay, so its live goal is real, but it
                      rests on the skipped statements (NOT a verification).
                      Off by default and never a shortcut (RULE K): the user
                      pre-grants with `skip prefix ok`, otherwise H31 blocks
                      the first use per file and a repeat is your logged
                      decision. Toggling the mode forces a clean prefix
                      reload. (default: False)
        timeout: Overall wall-clock budget (seconds) for this navigation. None
                      uses the server default ({STATE_AT_TIMEOUT}s, set by
                      HOL4_MCP_STATE_AT_TIMEOUT). On expiry the HOL process is
                      interrupted (recoverable) and a
                      TIMEOUT is returned instead of hanging. Raise it only for a
                      genuinely huge prefix replay; <= 0 disables the bound.

    When a proof is broken, the failing step's text is always shown.
    With context_before/context_after > 0, a "=== Steps around failure ===" section
    shows step plan entries whose source lines fall within the requested range,
    indented by nesting depth.
    Each step's text depends on its kind:
      - expand: the tactic text itself (e.g. strip_tac, simp[], Induct_on `x`)
      - open: the goalFrag function name (open_then1, open_by) — marks start of >- / by
      - mid: the goalFrag function name (then2, then3) — marks additional >- branches
      - close: close_paren — marks end of a >- / by group
    The failing step is marked with "<-- FAILED" in the steps section.

    Diagnostic lines to read, not ignore:
      - "[context admission history (not a dependency list): ...]" — recorded
        load failures/admissions, not an inferred dependency closure. Actual
        oracle use is reported separately by hol_check_proof. Verify at-risk
        prerequisites before claiming the file is complete.
      - "[inside opaque step k (lines A-B): state after sub-step j of n ...]"
        — the position is inside one opaque (parenthesized) step and the
        group receives exactly one goal there, so the step's flat sub-plan
        was replayed to the position: the goals ARE the state at line N.
        Not cached (the next call re-establishes the boundary).
      - "NOTE: target line N is INSIDE step k ..." — same situation but the
        group receives several goals, where a flat replay would diverge from
        the file; the state shown is that step's ENTRY, not the state at
        line N. Split the arm with `>- suspend` to navigate inside.
      - "TIMEOUT: step k (lines A-B) ..." — the failing step's source span;
        split it with `>- suspend` or raise the per-tactic timeout.
      - "TIMEOUT: state_at exceeded ... prefix=Ps, target=Ts" — where the
        overall budget went. Read "Active item" to distinguish dependency
        loading, current-file SML/translation and preceding theorem replay;
        target is this theorem's own tactics. hol_sessions exposes progress
        during a long prefix without sending a HOL command.
      - "PROOF BROKEN in opaque step k (lines A-B); ..." — the failure is
        inside one opaque step and its goal is not observable; the line
        carries the sub-suspend recipe. Goals are withheld unless
        show_partial=True, and then they are the step's ENTRY state.
      - "... of a Termination proof" / "the step's SML does not compile" —
        two cases where the sub-suspend recipe does NOT apply: a Definition
        cannot be sub-suspended (probe the arm in place from its first
        tactic), and a Poly/ML compile error (undeclared name, type error)
        means no tactic ran — the compiler's lines are quoted; fix the
        binding or forward reference.
      - "[prefix errors (top-level SML that raised ...): lines A-B: ...]" —
        a Definition or other top-level item before the target raised when
        it ran (classically a failed automatic termination proof). The raise
        ends that span: the item and everything after it in lines A-B did
        not run, so their names are missing from the heap although
        navigation continued with the next span.
      - "Theorem: X ⚠ context has admission history" — inspect the history
        below; this does not assert that every recorded admission was used.
      - "Latest HOL failure evidence" — retained request/response JSON path,
        explicitly historical; the current request may have succeeded.
      - "[Loop: N edit→navigate cycles on X broke at the same step k ...]" —
        the same step has failed after N successive edits; stop editing
        blind and sub-suspend the arm as the line says.
      - "Ancestor chain for suspension '...'" — a Resume's label was missing;
        the chain names the first broken ancestor to fix.
      - "unmatched smart quote at line L col C" — likely cause of a parse
        error; fix with the printed command.
      - "[HOL diagnostics during this navigation: ...]" — what HOL said while
        running YOUR tactics. "variables of same name but different types" is
        always an error and is invisible in the goal text, which prints no
        types.
      - "Goals withheld: ..." — replay stopped before the requested position,
        so the live goals are the failure point's. Navigate there, or pass
        show_partial=True.
      - "[Session reloaded: ancestor X rebuilt ...]" — a dependency's built
        artifact changed since the session loaded it; the session was rebuilt
        and the prefix replayed from the new artifacts. Nothing to do.
      - "[Session restarted: workdir A → B ...]" / "[Session restarted:
        file A → B ...]" — file= names another script; HOL restarted for it,
        so nothing A loaded or defined is visible to B. A's loaded context
        and open suspensions are gone.
      - "[Session reinit: <why>; HOL restarts, dependencies reload ...]" —
        a full rebuild was owed (an edit before the first theorem; no
        checkpoint left to rewind to). Ordinary edits, including edits
        inside a suspend/Resume chain, replay from the edited block only.
      - "[Auto-cheated Resume R[L] (line N) after its body failed at load:
        ...]" — a chain member went red while loading the prefix. It names
        the Resume blocks its `suspend` labels would have served (now "No
        such label") and warns that every later load re-runs and re-fails
        that body. Make it green first: end the unfinished arm in `cheat`
        or `>- suspend "Label"`, then iterate inside the Resume body.
      - "[Broken suspend/Resume chain `R`: R[L] (line N) failed at load —
        ...]" — this edit landed in a chain with such a red member; the
        reload re-runs that body and auto-cheats it again unless the edit
        fixed it. The cost is the red arm's, not the file's.
      - "[Timing: total=..., replay=..., startup=...]" — startup is HOL
        start plus dependency loads (cold init or reload); replay is this
        theorem's tactics only. A slow call with startup≈total is a heavy
        dependency load (see HOL4_MCP_DEP_LOAD_TIMEOUT / HOLHEAP), not a
        slow proof. "[Slow prefix/setup: Ps — <cause>; ...]" names what
        the prefix time was spent on when the session knows.

    Returns: Proof position, goals at that position, errors if any
    """
    cursor = await _get_cursor(session)

    # Auto-init if file provided and no cursor (or different file)
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    bad_timeout = _timeout_arg_error(timeout)
    if bad_timeout:
        return bad_timeout
    result = await _state_at_bounded(cursor, line, col, skip_prefix=skip_prefix, timeout=timeout)
    active_theorem = cursor._active_theorem
    thm = cursor._get_theorem(active_theorem) if active_theorem else None

    # Helper to convert tactic index to absolute line:col
    def tactic_to_loc(idx):
        if not thm:
            return None
        if not thm.proof_body or idx <= 0:
            # Start of proof body content (accounts for stripped whitespace)
            return _file_offset_to_line_col(thm.proof_body_offset, cursor._content)
        if idx > len(cursor._step_plan):
            idx = len(cursor._step_plan)
        if idx > 0:
            step = cursor._step_plan[idx - 1]
            file_pos = thm.proof_body_offset + step.end
            return _file_offset_to_line_col(file_pos, cursor._content)
        return _file_offset_to_line_col(thm.proof_body_offset, cursor._content)

    lines = []
    error_footer = ""  # Errors go in footer so truncation never hides them
    
    is_proof_complete, is_structural, is_broken = _classify_state_at(result)

    # Structural error (not in theorem, etc.) - no goals to show
    if is_structural:
        lines.append(f"ERROR: {result.error}")
        lines.extend(_quote_diagnosis_if_parse_error(cursor.file, result.error))
        if "TIMEOUT" in (result.error or ""):
            lines.extend(_heap_pressure_lines(cursor.session))
        return "\n".join(lines)

    # Show theorem name (useful for hol_check_proof after edits). A state that
    # rests on auto-cheated dependencies says so on this first line; the named
    # list follows in the caveats.
    if active_theorem:
        marker = (" ⚠ context has admission history"
                  if _auto_cheated_deps_lines(cursor, active_theorem) else "")
        lines.append(f"Theorem: {active_theorem}{marker}")

    if is_broken:
        # Proof is broken before the requested position.
        stuck_loc = tactic_to_loc(result.tactics_replayed)
        stuck_str = f"line {stuck_loc[0]} col {stuck_loc[1]}" if stuck_loc else ""
        # 0-indexed: the step the replay could not get past.
        fail_idx = result.tactics_replayed
        fail_loc = tactic_to_loc(fail_idx)          # START of that step
        fail_end_loc = tactic_to_loc(fail_idx + 1)  # END of that step
        fail_str = f"line {fail_loc[0]} col {fail_loc[1]}" if fail_loc else ""

        step_plan = cursor._step_plan if cursor else []
        fail_step = step_plan[fail_idx] if 0 <= fail_idx < len(step_plan) else None

        # An opaque leaf step (`expand`/`expand_list`) that spans MULTIPLE source
        # lines cannot be inspected inside: the real failure is somewhere within
        # its line range, NOT at its first line. This is common when a `\\`-chain
        # feeds a `>- (parenthesized arm)` / `>|` / other goal-positional
        # combinator — the step decomposer (reexpand_group_atoms) keeps the whole
        # construct as one opaque Group, swallowing the chain that precedes it.
        # Report the RANGE honestly instead of pinning (and blaming) the start line.
        opaque_multiline = (
            fail_step is not None
            and fail_step.kind in ("expand", "expand_list")
            and fail_loc is not None and fail_end_loc is not None
            and fail_end_loc[0] > fail_loc[0]
        )

        # A raised exception (HOL_ERR from a no-longer-matching qpat/qmatch/
        # rename) can fire from anywhere inside a lumped/opaque step, so the
        # pinned step is only where replay STOPPED, not a confident fault site.
        is_exc = _is_raised_exception(result.error)
        is_static = _is_static_error(result.error)
        # A Termination proof is not a Theorem: `suspend` inside it leaves the
        # Definition unsaved, so the sub-suspend recipe does not apply.
        is_definition = thm is not None and thm.kind == "Definition"
        sc_marker = (_STATIC_FAIL_MARKER if is_static else
                     _RAISED_FAIL_MARKER if is_exc else "  <-- FAILED")
        sc_header = (_STATIC_FAIL_HEADER if is_static else
                     _RAISED_FAIL_HEADER if is_exc else "=== Failing tactic ===")
        opaque_remedy = (
            None if is_static else
            "Probe the arm in place from its first tactic — a Definition cannot "
            "be sub-suspended." if is_definition else
            "Use Suspend/Resume or extract as a lemma.")

        if opaque_multiline:
            range_str = f"lines {fail_loc[0]}-{fail_end_loc[0]}"
            fail_str = range_str  # footer uses this too
            if is_static:
                lines.append(
                    f"PROOF BROKEN in opaque step {fail_idx} ({range_str}): the "
                    f"step's SML does not compile, so no tactic ran"
                )
            elif is_definition:
                lines.append(
                    f"PROOF BROKEN in opaque step {fail_idx} ({range_str}) of a "
                    f"Termination proof; the goal at the failure is not observable, "
                    f"and a Definition cannot be sub-suspended — probe the arm in "
                    f"place (below)"
                )
            else:
                lines.append(
                    f"PROOF BROKEN in opaque step {fail_idx} ({range_str}); the goal "
                    f"at the failure is not observable — sub-suspend the arm "
                    f"(`>- suspend \"X\"` + "
                    f"`Resume {suspension_base(active_theorem or 'thm')}[X]: cheat QED`) "
                    f"to navigate inside it"
                )
            lines.append(
                f"ERROR: the failing step is a SINGLE opaque tactic spanning "
                f"{range_str}; the replay cannot localize WHERE inside it the "
                f"failure is — the line shown is the step's START, not the "
                f"failure. (Cause: a `\\\\`-chain feeding a `>- (parenthesized "
                f"arm)` / `>|` / similar goal-positional combinator is kept opaque "
                f"by the step decomposer, swallowing the whole preceding chain.)"
            )
            if is_exc:
                lines.extend(_exception_advisory_lines(result.error))
            lines.append("")
            if is_static:
                lines.extend(_static_error_lines(result.error))
            elif is_definition:
                lines.append(
                    f"To localize: this is a Termination proof, and `suspend`/`Resume` "
                    f"is unavailable inside a Definition — the Definition does not load "
                    f"while its termination proof holds a suspension. Navigate to the "
                    f"step's start, hol_state_at(line={fail_loc[0]}, col={fail_loc[1]}), "
                    f"to read the goal ENTERING the arm, then apply the arm's tactics "
                    f"one at a time with hol_send to find the failing one. Do NOT "
                    f"reconstruct the goal in a scratch session, and do NOT bisect by "
                    f"moving a `cheat` through the chain."
                )
            else:
                lines.append(
                    f"To localize: SUB-SUSPEND the arm — replace the failing "
                    f"`>- (...)` / `>|` / `\\\\`-chain arm with `>- suspend \"X\"` and "
                    f"add `Resume thm[X]: cheat QED` after the parent QED. Each arm "
                    f"becomes a navigable Resume body whose prefix the FILE owns, so "
                    f"`hol_state_at` lands on the real goal. This is the DEFAULT for an "
                    f"opaque break (99% of the time). Do NOT bisect by moving a `cheat` "
                    f"through the chain, and do NOT reconstruct the goal with "
                    f"`hol_send`/`e`/`sg` (a scratch goal diverges from the file form). "
                    f"The goal available here is the state ENTERING this opaque step, "
                    f"not the failure point."
                )
            if thm:
                s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
                lines.extend(format_step_context(
                    step_plan, fail_idx, s_lines,
                    context_before=context_before, context_after=context_after,
                    fail_marker=sc_marker, failing_header=sc_header,
                    opaque_remedy=opaque_remedy,
                ))
        else:
            if is_static:
                lines.append(f"PROOF BROKEN at {fail_str}: the step's SML does not "
                             f"compile, so no tactic ran")
                lines.extend(_static_error_lines(result.error))
            elif is_exc:
                lines.append(f"PROOF BROKEN at {fail_str} (replay stopped on a raised exception)")
            else:
                lines.append(f"PROOF BROKEN at {fail_str}")
                # Step plan context shows which tactic failed — raw error is redundant
                lines.append(f"ERROR: Tactic failed at step {fail_idx}")

            # Show failing tactic and optional step plan context
            if fail_idx < len(step_plan) and thm:
                s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
                lines.extend(format_step_context(
                    step_plan, fail_idx, s_lines,
                    context_before=context_before, context_after=context_after,
                    fail_marker=sc_marker, failing_header=sc_header,
                    opaque_remedy=opaque_remedy,
                ))

            if is_exc:
                lines.extend(_exception_advisory_lines(result.error))

            lines.append("")
            lines.append(
                f"Replay cannot reach the requested position because an earlier "
                f"tactic failed. The proof is sequential — later goals depend on "
                f"earlier tactics succeeding."
            )
            if fail_loc:
                lines.append(
                    f"Fix the broken tactic, or inspect the failure point with:\n"
                    f"  hol_state_at(line={fail_loc[0]}, col={fail_loc[1]})"
                )

        # Timeout attribution: name the step's source span so the user can
        # shrink the replayed unit instead of guessing which tactic is slow.
        if result.error and "timed out" in result.error:
            lines.append("")
            lines.append(
                f"TIMEOUT: step {fail_idx} ({fail_str}) exceeded the "
                f"per-tactic timeout. If this span is a lumped chain, split "
                f"it with `>- suspend` to shrink the replayed unit; a "
                f"long-running but correct tactic needs a higher "
                f"HOL4_MCP_TACTIC_TIMEOUT (or --tactic-timeout)."
            )

        if result.goals and not show_partial:
            # The replay stopped short of the requested position, so the live
            # goals belong to the failure point, not to the position asked for.
            lines.append("")
            lines.append(
                "Goals withheld: replay stopped before the requested position, "
                "so the live goals are NOT the goals there. Navigate to the "
                "failure point above to obtain them in their own right, or pass "
                "show_partial=True to see them from here."
            )
        elif result.goals:
            display_goals = result.goals if all_goals else result.goals[:1]
            total = len(result.goals)
            if opaque_multiline:
                goal_label = "Goals entering the opaque step" if all_goals else f"Goal entering the opaque step (1 of {total})"
                goal_loc_str = ""
            else:
                goal_label = f"Goals at failure point" if all_goals else f"Goal at failure point (1 of {total})"
                goal_loc_str = f" ({stuck_str})"
            lines.append("")
            lines.append(f"=== {goal_label}{goal_loc_str} ===")
            for i, g in enumerate(display_goals):
                if i > 0:
                    lines.append("")
                if g.get('asms'):
                    for asm in g['asms']:
                        lines.append(f"  {asm}")
                    lines.append("  " + "-" * 40)
                lines.append(f"  {g['goal']}")

        # Error footer for truncation safety
        if is_static:
            error_footer = (
                f"ERROR: PROOF BROKEN at {fail_str}: the step's SML does not compile "
                f"(no tactic ran). Fix the named binding or forward reference; this is "
                f"not a logical proof failure and sub-suspending localizes nothing."
            )
        elif opaque_multiline and is_definition:
            error_footer = (
                f"ERROR: PROOF BROKEN somewhere in the opaque step at {fail_str} of a "
                f"Termination proof. A Definition cannot be sub-suspended: probe the "
                f"arm in place from its first tactic (hol_state_at there, then one "
                f"hol_send per tactic)."
            )
        elif opaque_multiline:
            error_footer = (
                f"ERROR: PROOF BROKEN somewhere in the opaque step at {fail_str}. "
                f"The line shown is the step's start, not the failure — SUB-SUSPEND: "
                f"split the step into per-goal `>- suspend \"X\"` sub-suspends, each a "
                f"navigable Resume body you validate independently with the file "
                f"owning the prefix. This is the default for an opaque break; do NOT "
                f"bisect by moving a `cheat` through the chain."
            )
        else:
            error_footer = (
                f"ERROR: PROOF BROKEN at {fail_str}. "
                f"Fix the broken tactic before inspecting later positions."
            )
    else:
        # Normal path: replay succeeded (or position is at/before the failure)
        loc = tactic_to_loc(result.tactic_idx)
        loc_str = f"Line {loc[0]} col {loc[1]}, " if loc else ""
        lines.append(f"{loc_str}Proof position")
        if result.error and not is_proof_complete:
            error_footer = f"ERROR: {result.error}"
        lines.append("")
        if result.goals:
            display_goals = result.goals if all_goals else result.goals[:1]
            total = len(result.goals)
            if all_goals:
                lines.append(f"=== Goals ({total}) ===")
            else:
                lines.append(f"=== Goal (1 of {total}) ===")
            for i, g in enumerate(display_goals):
                if i > 0:
                    lines.append("")  # Blank line between goals
                if g.get('asms'):
                    for asm in g['asms']:
                        lines.append(f"  {asm}")
                    lines.append("  " + "-" * 40)
                lines.append(f"  {g['goal']}")
        elif is_proof_complete:
            lines.append("=== Goals ===")
            lines.append("No goals (proof complete)")
        else:
            lines.append("=== Goals ===")
            if result.error:
                lines.append("Goals unavailable (goal query failed; see ERROR below)")
            else:
                lines.append("No goals (proof status indeterminate)")

    lines.extend(await _state_caveat_lines(cursor, result, active_theorem, thm, line))
    lines.extend(_session_notice_lines(cursor))

    lines.extend(_timing_lines(result))

    if result.timings:
        lines.extend(_slow_nav_lines(session, cursor.file, active_theorem,
                                     result.timings.get('total', 0),
                                     max(0, result.timings.get('total', 0) -
                                         result.timings.get('replay', 0)),
                                     cause=result.timings.get('startup_cause'),
                                     revision=(hashlib.sha256(thm.proof_body.encode()).hexdigest()
                                               if thm and thm.proof_body is not None else None)))
    if ("TIMEOUT" in (result.error or "")
            or (result.timings or {}).get('total', 0) >= _SLOW_NAV_SECS):
        lines.extend(_heap_pressure_lines(cursor.session))

    _schedule_gc(session)
    return _truncate_output("\n".join(lines), max_output, footer=error_footer)


@mcp.tool()
@_serialized_session()
async def hol_check_proof(
    theorem: str,
    file: str = None,
    workdir: str = None,
    trace: bool = True,
    session: str = "default",
    fresh: bool = False,
) -> str:
    """Confirm a theorem's proof completes. END-OF-THEOREM ONLY.

    Replays from the theorem's start with the per-theorem timeout, so it costs
    the same as holmake at theorem granularity and localizes nothing: a failure
    inside an opaque `>- (...)` / chained arm is reported as the whole lumped
    step. Call it once, when every chunk has already been stepped through and
    you expect OK — not to "see if it closes", and not to find what broke.

    To DEVELOP or DIAGNOSE instead: hol_state_at reads the live goal, and
    sub-suspending an opaque arm (`>- suspend "X"` + `Resume thm[X]: cheat QED`)
    gives the failure its own navigable body.

    Args:
        theorem: Theorem name to check
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        trace: If True, include full per-step timing trace
        session: Session name (default: "default")
        fresh: Explicit recovery only: restart HOL and replay the full prefix,
            discarding all cached bindings, checkpoints and verdicts. Use after
            a transient admitted load once the file proof is ready. Defaults
            to False, preserving incremental replay and cached checks.

    Returns: Whether proof completes, failure location, brief goal summary.
             With trace=True, also includes per-step timing and goal counts.

    Status values: OK / FAILED / INCOMPLETE / CHEAT / NO TACTICS, plus
    CANNOT CHECK for a Resume whose suspension goal is unavailable (comes
    with an ancestor-chain diagnosis naming the first broken ancestor).
    "Status: OK ... ⚠ depends on cheat" is accompanied by kernel oracle
    evidence. "context admission history" separately names load failures;
    it is NOT a dependency closure and may include later theorems visited
    earlier in the session. A timeout adds "TIMEOUT: step k spans lines A-B" naming
    the span to split with `>- suspend`.
    """
    t_call = time.perf_counter()
    cursor = await _get_cursor(session)

    # Auto-init if file provided
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    # Re-parse file to pick up edits
    try:
        cursor._reparse_if_changed()
    except FileNotFoundError:
        return f"ERROR: File not found: {cursor.file}"

    header_problem = next((p for p in resume_header_problems(cursor._content)
                           if p.name == theorem), None)
    if header_problem is not None:
        return f"ERROR: {header_problem.message}"

    if fresh:
        # Validate the request before discarding a useful session. Merely
        # deleting _failed_proofs would leave the old admitted ML binding live.
        if not cursor._get_theorem(theorem):
            return f"ERROR: Theorem '{theorem}' not found"
        cursor._schedule_full_reinit("fresh verification requested")
        cursor._skip_prefix = False
        cursor._skipped_thms.clear()
        cursor._session_notices.append(
            "[Fresh verification: HOL restarted; full prefix replayed without "
            "old bindings, checkpoints or cached verdicts]")

    # Enter theorem and get step plan
    enter_result = await cursor.enter_theorem(theorem)
    if "error" in enter_result:
        err_lines = [f"ERROR: {enter_result['error']}"]
        err_lines.extend(_failure_evidence_lines(cursor.session))
        err_lines.extend(
            _quote_diagnosis_if_parse_error(cursor.file, enter_result['error'])
        )
        return "\n".join(err_lines)

    thm = cursor._get_theorem(theorem)
    if not thm:
        return f"ERROR: Theorem '{theorem}' not found"

    dep_marker = (" ⚠ context has admission history"
                  if _auto_cheated_deps_lines(cursor, theorem) else "")
    lines = [
        f"Theorem: {theorem}{dep_marker}",
        f"Lines: {thm.start_line}-{thm.proof_end_line - 1}",
    ]
    lines.extend(_session_notice_lines(cursor))
    lines.extend(_auto_cheated_deps_lines(cursor, theorem))
    lines.extend(_prefix_error_lines(cursor))
    lines.append("")

    if thm.has_cheat:
        lines.append("Status: CHEAT (not verified)")
        lines.append("NOTE: Tactics before 'cheat' are not replayed in this mode.")
        lines.append("      Remove 'cheat' and rerun hol_check_proof for full replay.")
        return "\n".join(lines)

    # Oracle tags are populated after execute_proof_traced (calls verify_theorem_json).
    # We check them after execution below.

    # Execute proof (clean mode by default - matches holmake, uses cache)
    trace_data = await cursor.execute_proof_traced(theorem)
    
    if not trace_data:
        if thm.kind == "Definition" and thm.proof_body:
            # Definition blocks can't use execute_proof_traced (TC goal context).
            # Fall back to state_at at the End line to check proof completion.
            result = await _state_at_bounded(cursor, thm.proof_end_line - 1, col=1)
            # "no goals" from goals_json means the proof completed; ANY other
            # error (a TIMEOUT above all) leaves goals empty too, so the error
            # must be tested FIRST or a timeout reads as a pass.
            no_goals_ok = bool(result.error and "no goals" in result.error.lower())
            if result.error and not no_goals_ok:
                lines.append(f"Status: FAILED")
                lines.append(f"Error: {result.error}")
            elif not result.goals or no_goals_ok:
                lines.append(f"Status: OK (Definition termination proof)")
            else:
                lines.append(f"Status: INCOMPLETE ({len(result.goals)} goals remaining)")
            return "\n".join(lines)
        if thm.kind == "Resume":
            # Empty trace on a Resume almost always means the suspension
            # goal could not be extracted (label missing from the store).
            lines.append("Status: CANNOT CHECK (Resume suspension goal unavailable)")
            diag = await cursor.diagnose_resume_failure(theorem)
            if diag:
                lines.append("")
                lines.append(diag)
            return "\n".join(lines)
        lines.append("Status: NO TACTICS (trivial or unparseable)")
        return "\n".join(lines)

    # Find failure point
    failed_idx = None
    for i, entry in enumerate(trace_data):
        if entry.error or (i == len(trace_data) - 1 and entry.goals_after != 0):
            failed_idx = i
            break

    step_plan = cursor._step_plan

    final = trace_data[-1]
    total_ms = sum(e.real_ms for e in trace_data)
    total_steps = len(trace_data)

    # The setup this call paid for (a cold init, a fresh restart) is its own:
    # consumed here, it is not charged to the next navigation.
    elapsed = time.perf_counter() - t_call
    cause, cursor._startup_cause = cursor._startup_cause, None
    cursor._startup_seconds = 0.0
    # Emitted before the verdict so it survives every early return below.
    lines.extend(_slow_nav_lines(
        session, cursor.file, theorem, max(elapsed, total_ms / 1000.0),
        max(0.0, elapsed - total_ms / 1000.0), cause=cause,
        revision=(hashlib.sha256(thm.proof_body.encode()).hexdigest()
                  if thm.proof_body is not None else None),
    ))
    if total_ms / 1000.0 >= _SLOW_NAV_SECS or "TIMEOUT" in (final.error or "").upper():
        lines.extend(_heap_pressure_lines(cursor.session))

    if final.error:
        lines.append(f"Status: FAILED at step {failed_idx + 1}/{total_steps} ({total_ms}ms)")
        lines.extend(_failure_evidence_lines(cursor.session))
        # HOL echoes the whole failing ML expression, so for a big opaque arm
        # this line alone can be hundreds of lines of the body being replayed.
        lines.append(f"Error: {elide_long_text(final.error)}")
        # Timeout attribution: name the step's source span so the user can
        # shrink the lump instead of guessing which tactic is slow.
        fe = trace_data[failed_idx]
        if fe.error and fe.error.lstrip().upper().startswith("TIMEOUT"):
            so = fe.start_offset or 0
            sl = _file_offset_to_line_col(
                thm.proof_body_offset + so, cursor._content)[0]
            el = (_file_offset_to_line_col(
                thm.proof_body_offset + fe.end_offset, cursor._content)[0]
                if fe.end_offset is not None else sl)
            span = f"line {sl}" if el <= sl else f"lines {sl}-{el}"
            lines.append(
                f"TIMEOUT: step {failed_idx + 1} spans {span}. FIRST suspect a "
                f"LOOPING tactic in this span — simp/fs/gvs/rw[<recursive_def>] "
                f"without `Once` (unfolds forever, esp. under its own induction "
                f"IH), a GSYM/symmetric-eq rewrite that oscillates, or an "
                f"unbounded metis_tac/every_case_tac. Read the span and fix the "
                f"loop (simp[Once <def>]; drop the GSYM; narrow the rewrite set) "
                f"BEFORE assuming it is merely slow. If genuinely slow-but-correct: "
                f"split with `>- suspend` to shrink the lump, or raise the "
                f"per-tactic timeout."
            )
    elif final.goals_after == 0:
        self_cheat = _target_self_cheated_reason(cursor, theorem)
        oracles = cursor._theorem_oracles.get(theorem, [])
        if self_cheat is not None:
            # The target itself was auto-cheated during prefix load — the
            # "0 goals" rests on its statement, not its replayed proof.
            lines.append(f"Status: NOT VALIDATED ({total_ms}ms)")
            lines.extend(_target_self_cheated_lines(self_cheat))
            return "\n".join(lines)
        if oracles:
            lines.append(f"Status: OK ({total_ms}ms, {total_steps} steps) ⚠ depends on cheat")
            lines.append(f"[kernel oracle evidence: {', '.join(map(str, oracles))}]")
        else:
            lines.append(f"Status: OK ({total_ms}ms, {total_steps} steps)")
        if not trace and not oracles:
            return "\n".join(lines)
    else:
        lines.append(f"Status: INCOMPLETE at step {len(trace_data)}/{total_steps} ({total_ms}ms)")

    # Per-step trace: step plan with timing and goal annotations
    if trace:
        lines.append("")
        lines.extend(format_steps(step_plan, fail_idx=failed_idx, trace_data=trace_data))

    # Show failing tactic with location (when not in trace mode)
    if not trace and failed_idx is not None and failed_idx < len(trace_data):
        s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
        lines.extend(format_step_context(step_plan, failed_idx, s_lines))

    # Brief goal summary for failure/incomplete
    if failed_idx is not None:
        lines.append("")
        ga = final.goals_after if final.goals_after is not None else "unknown"
        lines.append(f"Remaining: {ga} goal(s)")
        s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
        fail_line = s_lines[failed_idx] if failed_idx < len(s_lines) else thm.proof_start_line
        lines.append(f"Use hol_state_at(line={fail_line}) for full goals")

    _schedule_gc(session)
    return "\n".join(lines)


def _install_pi_extension():
    """Install the pi extension to ~/.pi/agent/extensions/."""
    import shutil
    
    # Find the extension file bundled with the package
    ext_source = Path(__file__).parent / "pi_extension" / "hol4-mcp.ts"
    if not ext_source.exists():
        print(f"Error: Extension file not found at {ext_source}", file=sys.stderr)
        sys.exit(1)
    
    # Target directory
    ext_dir = Path.home() / ".pi" / "agent" / "extensions"
    ext_dir.mkdir(parents=True, exist_ok=True)
    
    ext_target = ext_dir / "hol4-mcp.ts"
    shutil.copy2(ext_source, ext_target)
    print(f"Installed pi extension to {ext_target}")


def _cli_parser():
    import argparse

    parser = argparse.ArgumentParser(description="HOL4 MCP Server and Tools")
    subparsers = parser.add_subparsers(dest="command")

    # install-pi subcommand
    subparsers.add_parser("install-pi", help="Install pi extension to ~/.pi/agent/extensions/")

    # serve subcommand (default behavior)
    serve_parser = subparsers.add_parser("serve", help="Run the MCP server (default)")
    serve_parser.add_argument(
        "--transport",
        choices=["stdio", "http", "sse"],
        default="stdio",
        help="Transport protocol (default: stdio)",
    )
    serve_parser.add_argument("--port", type=int, default=8000, help="Port for HTTP/SSE (default: 8000)")
    serve_parser.add_argument("--host", default="127.0.0.1", help="Host for HTTP/SSE (default: 127.0.0.1)")
    serve_parser.add_argument("-v", "--verbose", action="store_true", help="Enable debug logging")
    serve_parser.add_argument("--tactic-timeout", type=float, default=None, help=f"Max seconds per tactic during proof replay (default: {budgets.TACTIC_TIMEOUT:g}, from HOL4_MCP_TACTIC_TIMEOUT when set)")
    serve_parser.add_argument("--state-at-timeout", type=float, default=None, help=f"Overall wall-clock budget (seconds) per state_at/hol_goals navigation (default: {budgets.STATE_AT_TIMEOUT:g}, from HOL4_MCP_STATE_AT_TIMEOUT when set)")

    # Also allow serve options at top level for backwards compat
    parser.add_argument("--transport", choices=["stdio", "http", "sse"], default="stdio", help=argparse.SUPPRESS)
    parser.add_argument("--port", type=int, default=8000, help=argparse.SUPPRESS)
    parser.add_argument("--host", default="127.0.0.1", help=argparse.SUPPRESS)
    parser.add_argument("-v", "--verbose", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--tactic-timeout", type=float, default=None, help=argparse.SUPPRESS)
    parser.add_argument("--state-at-timeout", type=float, default=None, help=argparse.SUPPRESS)
    return parser


def main():
    """CLI entry point for HOL4 MCP server."""
    import logging

    args = _cli_parser().parse_args()

    if args.command == "install-pi":
        _install_pi_extension()
        return

    # Default to serve behavior
    global TACTIC_TIMEOUT, STATE_AT_TIMEOUT
    if args.tactic_timeout is not None:
        TACTIC_TIMEOUT = args.tactic_timeout
    if args.state_at_timeout is not None:
        STATE_AT_TIMEOUT = args.state_at_timeout

    if args.verbose:
        logging.basicConfig(
            level=logging.DEBUG,
            format="%(asctime)s %(levelname)s %(name)s: %(message)s",
            stream=sys.stderr,
        )
        logging.getLogger("mcp").setLevel(logging.DEBUG)

    if args.transport == "stdio":
        mcp.run(show_banner=False)
    else:
        print(f"HOL MCP server starting on {args.host}:{args.port} ({args.transport})", file=sys.stderr)
        mcp.run(transport=args.transport, host=args.host, port=args.port, show_banner=False)


if __name__ == "__main__":
    main()
