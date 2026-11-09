"""Regression tests: HOL diagnostics emitted during successful work never
reach the caller.

Finding #7 (severity 1) and its wider class.

Specific instance
=================

HOL4 prints, from its *goal* pretty-printer::

    WARNING: goal contains variables of same name but different types
      x : num, bool

``check_vars`` ($HOLDIR/src/proofman/goalStack.sml:231-259) is reachable
only through ``ppgoal``/``pr_goal`` (:314-343), i.e. only when a *goal* is
printed.  Per user report the flagged condition is always an error in
practice, and because ``term_to_string`` prints no types the colliding
variables are indistinguishable in the goal text the MCP renders --- the
caller cannot even detect the condition by eye.

Two distinct mechanisms, hence two tests:

(a) *Never generated on the rendering path.*  Goal text returned to the
    caller is built by ``goals_json()`` -> ``goal_to_json`` ->
    ``Parse.term_to_string`` (``sml_helpers/tactic_prefix.sml:69-80``),
    which never runs ``ppgoal``, so ``check_vars`` cannot contribute.

(b) *Generated during replay, then discarded.*  Each ``gf``/``ef`` send
    made by the cursor returns a ``proof`` value whose toplevel
    pretty-print goes through the goal printer, so the warning IS present
    in the raw send output --- which Python only error-scans and then
    throws away (``hol_cursor.py:1723-1730``, ``1757-1763``,
    ``1850-1852``).

Wider class
===========

The same mechanism drops *every* HOL diagnostic emitted during successful
navigation or verification (``WARNING:``, ``<<HOL message: ...>>``,
overload-resolution notes): structured channels regenerate their content
from terms and counters, success-path raw output is discarded wholesale,
and ``_is_hol_error`` deliberately classifies diagnostics as non-errors so
they cannot ride the error path either.  Net rule: a HOL diagnostic
reaches the caller iff something *fails* nearby, or the caller bypasses
the workflow tools (raw ``hol_send``, Holmake logs).

Truncation
==========

``hol_state_at`` appends the ``TIMEOUT: step k`` attribution to the body
*before* the goal block (``hol_mcp_server.py:1786-1818``), and
``_truncate_output`` keeps the TAIL --- so the attribution is dropped
exactly when the goal is big enough for the user to need it.

Each test asserts the CORRECT behaviour and is expected to fail today.
"""

import json
import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession
from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp.hol_mcp_server import _truncate_output, DEFAULT_MAX_OUTPUT


FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"

SAME_NAME_WARNING = "WARNING: goal contains variables of same name but different types"

# Proof whose middle state has an assumption mentioning ``x : bool`` while the
# conclusion mentions ``x : num``.  SUBGOAL_THEN parses its term outside the
# goal context, so the two ``x``s really do differ in type; the proof still
# closes cleanly, i.e. nothing fails anywhere near the diagnostic.
SAME_NAME_SCRIPT = """open HolKernel Parse boolLib bossLib;
val _ = new_theory "repro_diag_samename";

Theorem samename_collision:
  !x:num. x = x
Proof
  strip_tac
  >> SUBGOAL_THEN ``(x:bool) \\/ ~x`` assume_tac
  >- simp []
  >> simp []
QED

val _ = export_theory();
"""

# Same shape, but the diagnostic is a parser message rather than a goal-printer
# warning: parsing ``!f y. f y = f y`` invents type variables.
HOL_MESSAGE_SCRIPT = """open HolKernel Parse boolLib bossLib;
val _ = new_theory "repro_diag_message";

Theorem invented_tyvars:
  !x:num. x = x
Proof
  strip_tac
  >> SUBGOAL_THEN ``!f y. f y = f y`` assume_tac
  >- simp []
  >> simp []
QED

val _ = export_theory();
"""

# Line of ``>> simp []``: the cursor lands on the step boundary just after the
# SUBGOAL_THEN step, i.e. on the state carrying the extra assumption.
COLLISION_LINE = 10


@pytest.fixture
async def hol_session():
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    result = await session.send(
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=60
    )
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()


class SendRecorder:
    """Records every raw HOL send made through a session."""

    def __init__(self, session):
        self.session = session
        self.sends: list[tuple[str, str]] = []
        self._orig = session.send

    def install(self):
        async def recording_send(command, timeout=30, **kwargs):
            output = await self._orig(command, timeout=timeout, **kwargs)
            self.sends.append((command, output))
            return output

        self.session.send = recording_send
        return self

    def clear(self):
        self.sends.clear()

    def diagnostic_lines(self, replay_only: bool = False) -> list[str]:
        """Diagnostic lines HOL emitted in the recorded raw output.

        ``replay_only`` keeps just the goal-setup / tactic-execution sends,
        i.e. diagnostics HOL produced while running the caller's own proof.
        """
        found = []
        for cmd, output in self.sends:
            if replay_only and not (cmd.startswith("ef(") or cmd.startswith("gf ")):
                continue
            for line in output.splitlines():
                stripped = line.strip()
                if stripped.startswith("WARNING:") or stripped.startswith("<<HOL message:"):
                    found.append(stripped)
        return found


def caller_visible_text(result) -> str:
    """Everything ``hol_state_at``/``hol_goals`` can put in front of a caller.

    The MCP tool layer renders goals, the error string and nothing else from
    a ``StateAtResult``; a fix that attaches diagnostics would have to add a
    field, so any extra diagnostic-bearing attribute counts as visible too.
    """
    parts = [json.dumps(result.goals, ensure_ascii=False), result.error or ""]
    for extra in ("warnings", "diagnostics", "messages", "hol_messages"):
        value = getattr(result, extra, None)
        if value:
            parts.append(json.dumps(value, ensure_ascii=False, default=str))
    return "\n".join(parts)


async def navigate_to_collision(session, script_path: Path, source: str):
    """Replay ``source`` up to the state with the same-name collision."""
    script_path.write_text(source)
    recorder = SendRecorder(session).install()
    cursor = FileProofCursor(script_path, session)
    await cursor.init()
    recorder.clear()  # keep only the sends made by the navigation itself
    result = await cursor.state_at(line=COLLISION_LINE, col=1)
    assert result.error is None, f"test setup: navigation failed: {result.error}"
    assert result.goals, "test setup: expected an open goal at the collision state"
    return cursor, result, recorder


# ----------------------------------------------------------------------
# #7 (a): the rendering channel cannot express the collision at all
# ----------------------------------------------------------------------


@pytest.mark.asyncio
async def test_goals_json_reports_same_name_different_type_collision(
    hol_session, tmp_path
):
    """``goals_json()`` must report the same-name/different-type collision.

    HOL itself flags this goal (confirmed by printing it with
    ``goalStack.std_pp_goal``).  ``goals_json`` is the only channel
    ``hol_state_at``/``hol_goals`` render from, so unless it replicates
    ``check_vars`` the condition is unreportable by construction --- and
    since ``term_to_string`` hides types, the rendered goal shows ``x`` and
    ``x`` with nothing to tell them apart.
    """
    script = tmp_path / "repro_diag_samenameScript.sml"
    await navigate_to_collision(hol_session, script, SAME_NAME_SCRIPT)

    raw = await hol_session.send("goals_json();", timeout=30)
    payload = next(
        (line for line in raw.splitlines() if line.strip().startswith("{")), None
    )
    assert payload, f"test setup: no JSON line in goals_json output: {raw!r}"
    data = json.loads(payload)
    assert "ok" in data, f"test setup: goals_json failed: {data}"

    rendered = json.dumps(data, ensure_ascii=False)
    assert "x = x" in rendered, f"test setup: unexpected goal rendering: {rendered}"

    exposes_collision = "different types" in raw or bool(data.get("warnings"))
    assert exposes_collision, (
        "goals_json rendered the colliding goal with no indication that its two "
        f"'x' variables have different types (num and bool). Output: {raw!r}"
    )


# ----------------------------------------------------------------------
# #7 (b): HOL generates the warning during replay; it is then discarded
# ----------------------------------------------------------------------


@pytest.mark.asyncio
async def test_state_at_surfaces_same_name_different_type_warning(
    hol_session, tmp_path
):
    """A warning HOL emitted during a successful replay must reach the caller.

    The test first establishes that the warning really is generated (it is
    present in the raw output of the ``ef(...)`` send the cursor issues),
    then requires it to be visible in the ``state_at`` result.
    """
    script = tmp_path / "repro_diag_samenameScript.sml"
    _cursor, result, recorder = await navigate_to_collision(
        hol_session, script, SAME_NAME_SCRIPT
    )

    generated = [
        (cmd, out) for cmd, out in recorder.sends if SAME_NAME_WARNING in out
    ]
    assert generated, (
        "test setup: HOL did not emit the same-name warning during replay; "
        f"sent commands: {[c[:60] for c, _ in recorder.sends]}"
    )

    visible = caller_visible_text(result)
    assert "different types" in visible or getattr(result, "warnings", None), (
        "HOL emitted "
        f"{SAME_NAME_WARNING!r} while replaying "
        f"{generated[0][0][:60]!r}, but state_at returned no trace of it. "
        f"Caller-visible text: {visible!r}"
    )


# ----------------------------------------------------------------------
# Wider class: ANY diagnostic emitted during successful navigation is dropped
# ----------------------------------------------------------------------


@pytest.mark.asyncio
async def test_hol_diagnostics_during_successful_navigation_reach_caller(
    hol_session, tmp_path
):
    """The general rule, pinned with a non-goal-printer diagnostic.

    Parsing ``!f y. f y = f y`` makes HOL print
    ``<<HOL message: inventing new type variable names: 'a, 'b>>``.  It
    arrives in the raw output of the replay send, nothing fails, and the
    caller gets nothing: every diagnostic HOL emitted while doing the work
    the caller asked for should be reported back, not only the ones that
    happen to accompany a failure.
    """
    script = tmp_path / "repro_diag_messageScript.sml"
    script.write_text(HOL_MESSAGE_SCRIPT)
    recorder = SendRecorder(hol_session).install()
    cursor = FileProofCursor(script, hol_session)
    await cursor.init()
    recorder.clear()

    result = await cursor.state_at(line=COLLISION_LINE, col=1)
    assert result.error is None, f"test setup: navigation failed: {result.error}"

    emitted = recorder.diagnostic_lines(replay_only=True)
    assert emitted, (
        "test setup: HOL emitted no diagnostic during navigation; sent: "
        f"{[c[:60] for c, _ in recorder.sends]}"
    )

    visible = caller_visible_text(result)
    dropped = [d for d in emitted if d not in visible]
    assert not dropped, (
        f"HOL emitted {len(emitted)} diagnostic(s) during a fully successful "
        f"navigation and none of them reached the caller: {dropped!r}. "
        f"Caller-visible text: {visible!r}"
    )


# ----------------------------------------------------------------------
# Truncation: TIMEOUT attribution is cut out exactly when the goal is large
# ----------------------------------------------------------------------


def test_timeout_step_attribution_survives_truncation_of_large_goal():
    """``TIMEOUT: step k`` names the slow step; truncation must not eat it.

    ``hol_state_at`` builds its body as
    ``... / TIMEOUT: step k (span) ... / === Goal at failure point === /
    <goal>``, then calls ``_truncate_output``, which keeps the TAIL.  A goal
    bigger than ``max_output`` therefore pushes the attribution --- the one
    line telling the user *which* tactic to shrink --- out of the message,
    precisely in the case where the proof state is too big to eyeball.
    """
    attribution = (
        "TIMEOUT: step 4 (line 120 col 3) exceeded the per-tactic timeout. "
        "If this span is a lumped chain, split it with `>- suspend` to shrink "
        "the replayed unit; a long-running but correct tactic needs a higher "
        "--tactic-timeout."
    )
    big_goal = "\n".join(
        f"  ASM_{i}: some_predicate (f {i} x) /\\ another_predicate (g {i} y)"
        for i in range(400)
    )
    body = "\n".join(
        [
            "Line 120 col 3, Proof position",
            "",
            attribution,
            "",
            "=== Goal at failure point (1 of 1) ===",
            big_goal,
        ]
    )
    footer = (
        "ERROR: PROOF BROKEN at line 120 col 3. "
        "Fix the broken tactic before inspecting later positions."
    )
    assert len(body) > DEFAULT_MAX_OUTPUT, "test setup: body must overflow the budget"

    out = _truncate_output(body, DEFAULT_MAX_OUTPUT, footer=footer)

    assert "TIMEOUT: step 4" in out, (
        "Timeout step attribution was truncated away: with a large goal, "
        "_truncate_output keeps only the tail, so the user is told the proof "
        "timed out but not which step to shrink. "
        f"Kept {len(out)} of {len(body)} bytes."
    )
