"""Specification tests for the tactic-cost improvements, now regression tests.

Every test here was written against behaviour that did not exist yet; none
describes a defect. That is the difference between this file and its
``test_repro_*.py`` siblings, which pin real bugs. Each was red under
``xfail(strict=True)`` and the markers came off as the improvements landed.

Design rule followed throughout: a spec test must not invent an output format.
Assertions are therefore made against structured values the code already
carries where one exists, and elsewhere against *tolerant* matchers (any
wording, any 0-/1-based step numbering, seconds or milliseconds) that any
reasonable implementation satisfies.

Improvements specified (background: ``MCP_TACTIC_COST_review.md`` §2-3):

  1  Per-step timing and attribution on ``hol_state_at``'s failure path.
     ``verify_core`` already does per-step ``Timer`` + ``smlTimeout`` + goal
     counts for ``hol_check_proof``; the replay path
     (``_replay_steps_with_fallback``, ``hol_cursor.py:1837-1870``) has the
     per-step boundaries and throws the timing away, so a failed navigation
     cannot say which step consumed the time.

  2  A soft per-step budget: a step that never returns is interrupted at N
     seconds and REPORTED against its own step, instead of the run reaching
     the global timeout with nothing attributed. The only mechanism that
     catches a genuine loop, which by definition never returns on its own.

  3  A loop / blow-up discriminator: a step that FINISHED with a large elapsed
     time was a blow-up; a step that only ever hits the budget is a candidate
     loop. The report must tell the two apart.

  4  ``asms=N`` (assumption count of the goal a step starts from) in the
     ``[Timing:]`` diagnostic line. INFORMATION, NOT PREDICTION: ``fs``,
     ``gs``, ``gvs``, ``simp`` and ``metis_tac`` can all fail to terminate at
     any assumption count, and no context-size threshold detects a loop.
     Nothing here asserts that a large ``asms`` implies anything at all.

  5  One "bad position" message: every bad-position rejection names the valid
     line range (field logs: the useless variant 26x, the useful one 2x).

  6  Disclosing a pending session reinit before paying for it is already
     specified by ``test_broken_chain_edit_discloses_pending_cold_replay`` in
     ``tests/test_repro_checkpoints.py`` and is deliberately NOT duplicated
     here. See the note at the end of this file.

Improvements 1-3 run against a stubbed session that plays a scripted per-step
cost, so no HOL process is needed; 4 runs against a stubbed cursor; 5 needs
neither (the rejection happens before any send).
"""

import asyncio
import re
from pathlib import Path

import pytest

from hol4_mcp import hol_mcp_server as server
from hol4_mcp.hol_mcp_server import hol_state_at
from hol4_mcp.hol_cursor import FileProofCursor, StateAtResult


# ---------------------------------------------------------------------------
# Session stub: a scripted per-step cost model
# ---------------------------------------------------------------------------

ONE_THEOREM_SCRIPT = (
    "open HolKernel Parse boolLib bossLib;\n"        # 1
    "\n"                                             # 2
    'val _ = new_theory "specimprstep";\n'            # 3
    "\n"                                             # 4
    "Theorem spec_target:\n"                         # 5
    "  !x:num. x = x\n"                              # 6
    "Proof\n"                                        # 7
    "  simp[]\n"                                     # 8
    "QED\n"                                          # 9
    "\n"                                             # 10
    "val _ = export_theory();\n"                     # 11
)


class _ScriptedStepSession:
    """HOL session stub that plays a per-command cost/outcome script.

    ``steps`` is an ordered list of ``(marker, cost_secs, reply_or_None)``. A
    send is scanned for the markers IN ORDER, which models both legs of
    ``_replay_steps_with_fallback``: a batch send carries every marker and
    accumulates their costs, a step-by-step send carries exactly one.

    Costs are charged against the granted ``timeout`` exactly as
    ``HOLSession.send``'s ``asyncio.wait_for`` would, so a step whose cost
    exceeds its budget yields the same ``TIMEOUT: ...`` text the real session
    returns. Real sleeping is capped at ``sleep_cap`` so a simulated
    never-returning tactic costs the test milliseconds, not minutes — but a
    cost BELOW the cap is slept in full, so a wall-clock measurement taken by
    an implementation observes the scripted duration.

    Any send carrying no marker (``drop_all();``, ``gf `...`;``) succeeds
    instantly.
    """

    def __init__(self, steps, sleep_cap: float = 0.25):
        self.steps = steps
        self.sleep_cap = sleep_cap
        self.sent: list[tuple[str, float | None]] = []

    async def send(self, command: str, timeout: float | None = None) -> str:
        self.sent.append((command, timeout))
        spent = 0.0
        for marker, cost, reply in self.steps:
            if marker not in command:
                continue
            if timeout is not None and spent + cost > timeout:
                await asyncio.sleep(min(timeout - spent, self.sleep_cap))
                return f"TIMEOUT: no response from HOL after {timeout}s"
            spent += cost
            await asyncio.sleep(min(cost, self.sleep_cap))
            if reply is not None:
                return reply
        return "> val it = () : unit"

    def interrupt(self) -> None:
        pass


def _cmd(marker: str) -> str:
    """The ``ef`` command shape ``_replay_steps_with_fallback`` is handed."""
    return f"ef(goalFrag.expand({marker}));\n"


def _cursor_for(tmp_path: Path, session, tactic_timeout: float = 5.0):
    """Cursor over a one-theorem script, parsed, with no reinit pending."""
    tmp_path.mkdir(parents=True, exist_ok=True)
    script = tmp_path / "specimprstepScript.sml"
    script.write_text(ONE_THEOREM_SCRIPT)
    cursor = FileProofCursor(
        script, session=session, checkpoint_dir=tmp_path / "ckpt",
        tactic_timeout=tactic_timeout,
    )
    cursor._reparse_if_changed()
    cursor._needs_session_reinit = False
    assert cursor._get_theorem("spec_target"), "setup: theorem not parsed"
    return cursor


# ---------------------------------------------------------------------------
# Tolerant matchers — a spec test must not pin an output format
# ---------------------------------------------------------------------------

_NUMBER_RE = re.compile(r"\d+(?:\.\d+)?")


def _containers_snapshot(cursor) -> dict:
    return {k: repr(v) for k, v in vars(cursor).items()
            if isinstance(v, (list, dict, tuple))}


def _attribution_text(error: str | None, cursor, before: dict) -> str:
    """Every channel a per-step attribution could reach the caller through.

    Two are accepted, so the spec constrains the INFORMATION, not its home:
    the error string this call returns (it becomes ``StateAtResult.error``),
    and any list/dict/tuple the call recorded on the cursor (the natural
    structured carrier — ``StateAtResult.timings`` is a plain dict assembled
    one frame up in ``_build_result``).
    """
    parts = [error or ""]
    for key, value in vars(cursor).items():
        if not isinstance(value, (list, dict, tuple)):
            continue
        if before.get(key) == repr(value):
            continue
        parts.append(f"{key}={value!r}")
    return "\n".join(parts)


def _mentions_duration(text: str, seconds: float, tol: float = 0.5) -> bool:
    """True when some number in ``text`` reads as ``seconds``, in either
    seconds or milliseconds, within a relative tolerance."""
    for raw in _NUMBER_RE.findall(text):
        value = float(raw)
        for scale in (1.0, 0.001):
            if abs(value * scale - seconds) <= tol * seconds:
                return True
    return False


def _names_step(text: str, idx: int, marker: str) -> bool:
    """True when ``text`` identifies the step at 0-based ``idx``: by its
    tactic text, or by its index in either numbering convention."""
    if marker in text:
        return True
    return any(
        re.search(rf"(?:step|tactic|cmd|idx)\D{{0,12}}\b{n}\b", text, re.I)
        for n in (idx, idx + 1)
    )


def _marks_timeout(text: str) -> bool:
    """True when ``text`` says a step ran out of its budget rather than
    finishing."""
    low = text.lower()
    return any(w in low for w in
               ("timeout", "timed out", "exceeded", "did not finish"))


# ---------------------------------------------------------------------------
# Improvement 1 — per-step timing/attribution on the state_at failure path
# ---------------------------------------------------------------------------

SLOW_STEP_SECS = 0.4


async def _replay_slow_then_fail(tmp_path: Path):
    """Replay where step 1 is slow but SUCCEEDS and step 3 fails instantly.

    The slow step is deliberately not the failing one: naming the failure is
    already possible (the returned count is its index), naming where the TIME
    went is what does not exist.
    """
    steps = [
        ("cheap_a_tac", 0.01, None),
        ("slow_gvs_tac", SLOW_STEP_SECS, None),
        ("cheap_b_tac", 0.01, None),
        ("broken_tac", 0.01, "Exception- HOL_ERR raised: broken_tac not applicable"),
    ]
    session = _ScriptedStepSession(steps, sleep_cap=SLOW_STEP_SECS + 0.1)
    cursor = _cursor_for(tmp_path, session)
    cmds = [_cmd(marker) for marker, _, _ in steps]
    before = _containers_snapshot(cursor)

    replayed, error = await cursor._replay_steps_with_fallback(
        "spec_target", cmds, cursor._batch_timeout_for(len(cmds))
    )
    assert error is not None, "setup: the replay was expected to fail"
    assert replayed == 3, f"setup: expected to stop at step 3, got {replayed}"
    return _attribution_text(error, cursor, before)


async def test_failed_replay_attributes_elapsed_time_to_its_step(tmp_path: Path):
    """A failed navigation must name the step that consumed the time and how
    long it took.

    Any wording, any 0-/1-based step numbering, seconds or milliseconds; the
    attribution may ride the returned error or a structure recorded on the
    cursor. What must exist is the pairing of A step WITH ITS ELAPSED TIME —
    today the caller gets one aggregate ``[Timing: total=..., replay=...]``
    and cannot tell a 0.4s step from a 180s one.
    """
    text = await _replay_slow_then_fail(tmp_path)

    assert _names_step(text, 1, "slow_gvs_tac"), (
        "the failure report does not identify the expensive step (step 1, "
        f"slow_gvs_tac, {SLOW_STEP_SECS}s) in any form:\n{text}"
    )
    assert _mentions_duration(text, SLOW_STEP_SECS), (
        f"no elapsed time near {SLOW_STEP_SECS}s ({SLOW_STEP_SECS * 1000:.0f}ms) "
        f"is reported for the step that spent it:\n{text}"
    )


# ---------------------------------------------------------------------------
# Improvement 2 — a soft per-step budget, reported against its step
# ---------------------------------------------------------------------------

async def _replay_with_looping_step(tmp_path: Path, budget: float = 5.0):
    """Replay where step 2 never returns (cost far past any budget)."""
    steps = [
        ("cheap_a_tac", 0.01, None),
        ("cheap_b_tac", 0.01, None),
        ("loop_tac", 10_000.0, None),
        ("cheap_c_tac", 0.01, None),
    ]
    session = _ScriptedStepSession(steps)
    cursor = _cursor_for(tmp_path, session, tactic_timeout=budget)
    cmds = [_cmd(marker) for marker, _, _ in steps]
    before = _containers_snapshot(cursor)

    replayed, error = await cursor._replay_steps_with_fallback(
        "spec_target", cmds, cursor._batch_timeout_for(len(cmds))
    )
    assert error is not None, "setup: the looping step was expected to fail"
    return _attribution_text(error, cursor, before)


async def test_step_exceeding_budget_is_reported_against_its_step(tmp_path: Path):
    """A step interrupted at the per-step budget must be named.

    This is the only mechanism that catches a genuine LOOP: a looping tactic
    never returns, so no post-hoc trace of a completed run and no static or
    context-size signal can observe it — only an empirical timer with a
    per-step interrupt turns "the navigation hung" into "step k did not finish
    within Ns".
    """
    budget = 5.0
    text = await _replay_with_looping_step(tmp_path, budget=budget)

    assert _marks_timeout(text), (
        f"the interrupted step is not reported as out of budget:\n{text}"
    )
    assert _names_step(text, 2, "loop_tac"), (
        "the budget was enforced but the report does not say WHICH step "
        f"exceeded it (step 2, loop_tac), so the caller must still guess:\n{text}"
    )
    assert _mentions_duration(text, budget), (
        f"the report does not state the budget ({budget}s) the step "
        f"exceeded:\n{text}"
    )


# ---------------------------------------------------------------------------
# Improvement 3 — loop vs blow-up discriminator
# ---------------------------------------------------------------------------

async def test_report_separates_blowup_from_candidate_loop(tmp_path: Path):
    """The same step, run in the two pathological modes, must produce
    distinguishable reports.

    Blow-up (superlinear but TERMINATING work) eventually returns, so its
    report carries a completed elapsed time and must not read as a timeout.
    A loop never returns, so its report can only ever be "did not finish
    within the budget". One trace line settles which mode occurred — the
    question ``MCP_TACTIC_COST_review.md`` §1 could not answer about the
    field episode.
    """
    blowup = await _replay_slow_then_fail(tmp_path / "blowup")
    loop = await _replay_with_looping_step(tmp_path / "loop")

    assert _mentions_duration(blowup, SLOW_STEP_SECS), (
        "the terminating expensive step reports no completed elapsed time, so "
        f"it cannot be told apart from a step that never returned:\n{blowup}"
    )
    assert not _marks_timeout(blowup), (
        "a step that FINISHED is reported as having run out of budget, which "
        f"is the loop verdict, not the blow-up one:\n{blowup}"
    )
    assert _marks_timeout(loop), (
        f"the step that never returned is not reported as such:\n{loop}"
    )


# ---------------------------------------------------------------------------
# Improvement 4 — asms=N in the [Timing:] line (INFORMATION, NOT PREDICTION)
# ---------------------------------------------------------------------------

class _TimingStubCursor:
    """Minimal cursor for the reporting tail of hol_state_at."""

    file = Path("/nonexistent/specimprtimingScript.sml")

    def __init__(self):
        self._active_theorem = None      # keeps the location/step-plan paths out
        self._content = ""
        self._step_plan = []
        self._failed_proofs = {}
        self._skip_prefix = False

    def _get_theorem(self, name):
        return None


ASM_COUNT = 7


async def test_timing_line_reports_assumption_count(monkeypatch):
    """The ``[Timing:]`` line must carry ``asms=N`` for the goal at the cursor.

    Purely informational: it lets a reader correlate a slow step with the
    context it ran in (``asms=90`` at an arm entry vs ``asms=8`` in the
    original lemma). It predicts NOTHING — ``fs``/``gs``/``gvs``/``simp``/
    ``metis_tac`` can all fail to terminate at any assumption count, and no
    context-size threshold detects a loop. Accordingly this test asserts only
    that the number is REPORTED; it must never grow an assertion that a large
    ``asms`` implies a problem.
    """
    cursor = _TimingStubCursor()

    async def fake_get_cursor(name):
        return cursor

    async def fake_state_at_bounded(cur, line, col=1, **kwargs):
        return StateAtResult(
            goals=[{"asms": [f"h{i}" for i in range(ASM_COUNT)], "goal": "x = x"}],
            tactic_idx=3,
            tactics_replayed=3,
            tactics_total=5,
            file_hash="deadbeef",
            error=None,
            timings={"total": 0.5, "replay": 0.4, "strategy": "replay"},
        )

    monkeypatch.setattr(server, "_get_cursor", fake_get_cursor)
    monkeypatch.setattr(server, "_state_at_bounded", fake_state_at_bounded)

    out = await hol_state_at(line=8, session="spec_impr_timing", max_output=8000)

    timing_lines = [ln for ln in out.split("\n") if ln.startswith("[Timing:")]
    assert timing_lines, f"setup: no [Timing:] line in the output:\n{out}"
    assert any(f"asms={ASM_COUNT}" in ln.lower() for ln in timing_lines), (
        "the [Timing:] line does not report the assumption count of the goal "
        f"at the cursor (asms={ASM_COUNT}); a reader cannot tell what context "
        f"the reported time was spent in: {timing_lines}"
    )


async def test_failed_goal_query_is_not_reported_as_proof_complete(monkeypatch):
    cursor = _TimingStubCursor()

    async def fake_get_cursor(name):
        return cursor

    async def fake_state_at_bounded(cur, line, col=1, **kwargs):
        return StateAtResult(
            goals=[],
            tactic_idx=2,
            tactics_replayed=2,
            tactics_total=2,
            file_hash="deadbeef",
            error="goals_json: Interrupt",
            timings={"total": 1.0, "replay": 0.9, "strategy": "replay"},
        )

    monkeypatch.setattr(server, "_get_cursor", fake_get_cursor)
    monkeypatch.setattr(server, "_state_at_bounded", fake_state_at_bounded)

    out = await hol_state_at(line=8, session="spec_impr_goal_error", max_output=8000)

    assert "proof complete" not in out.lower(), out
    assert "Goals unavailable" in out, out
    assert "ERROR: goals_json: Interrupt" in out, out


# ---------------------------------------------------------------------------
# Improvement 5 — one bad-position message, always naming the valid range
# ---------------------------------------------------------------------------

TWO_THEOREM_SCRIPT = (
    "open HolKernel Parse boolLib bossLib;\n"        # 1
    "\n"                                             # 2
    'val _ = new_theory "specimprpos";\n'             # 3
    "\n"                                             # 4
    "Theorem pos_first:\n"                           # 5
    "  !x:num. x = x\n"                              # 6
    "Proof\n"                                        # 7
    "  simp[]\n"                                     # 8
    "QED\n"                                          # 9
    "\n"                                             # 10
    "Theorem pos_second:\n"                          # 11
    "  !y:num. y + 0 = y\n"                          # 12
    "Proof\n"                                        # 13
    "  simp[]\n"                                     # 14
    "QED\n"                                          # 15
    "\n"                                             # 16
    "val _ = export_theory();\n"                     # 17
)

BETWEEN_THEOREMS_LINE = 10   # the blank line between the two QEDs


def _names_a_valid_range(text: str, cursor) -> bool:
    """True when ``text`` names some parsed theorem together with two of its
    boundary lines — i.e. it tells the caller where a valid position IS.

    Either theorem qualifies (the position lies between them), and any of the
    theorem's boundary lines count, so neither the choice of neighbour nor the
    exact endpoint convention is pinned.
    """
    numbers = set(_NUMBER_RE.findall(text))
    for thm in cursor._theorems:
        if thm.name not in text:
            continue
        bounds = {thm.start_line, thm.proof_start_line - 1, thm.proof_start_line,
                  thm.proof_end_line - 1, thm.proof_end_line}
        if len({str(b) for b in bounds} & numbers) >= 2:
            return True
    return False


async def test_bad_position_rejection_names_a_valid_range(tmp_path: Path):
    """Every bad-position rejection must name a valid line range.

    Field logs: the range-less variant fires 26x against 2x for the useful
    one, so the common case is the one that tells the caller nothing and costs
    a guess-and-retry round trip.
    """
    script = tmp_path / "specimprposScript.sml"
    script.write_text(TWO_THEOREM_SCRIPT)
    cursor = FileProofCursor(script, session=None, checkpoint_dir=tmp_path / "ckpt")
    cursor._reparse_if_changed()
    cursor._needs_session_reinit = False
    assert len(cursor._theorems) == 2, "setup: both theorems must parse"

    result = await cursor.state_at(BETWEEN_THEOREMS_LINE, col=1)

    assert result.error, "setup: the position between two theorems was accepted"
    assert _names_a_valid_range(result.error, cursor), (
        "the rejection names no theorem and no valid line range, so the "
        "caller learns only that this position is wrong: "
        f"{result.error!r}"
    )


# ---------------------------------------------------------------------------
# Improvement 6 — deliberately NOT specified here
# ---------------------------------------------------------------------------
#
# "Disclose a pending session reinit before paying for it" is specified by
# test_broken_chain_edit_discloses_pending_cold_replay in
# tests/test_repro_checkpoints.py, which asserts exactly this: the forced
# reinit is correct and stays (the suspension store is append/consume-only and
# cannot be partially rolled back), and what must change is that the caller is
# TOLD the next navigation now costs a cold replay from dependencies. Nothing
# is added here; a second test over the same claim would only make the fix
# look bigger than it is.
