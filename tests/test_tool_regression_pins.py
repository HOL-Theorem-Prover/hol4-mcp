"""Regression tests, through the tools callers use, for three fixes: hol_goals
shows the caveats hol_state_at shows; draining after a failed proof does not
race a concurrent reader; hol_state_at discloses a scheduled reinit."""
import asyncio

from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    _sessions,
    hol_goals,
    hol_state_at,
    hol_stop,
)
from hol4_mcp.hol_session import HOLSession

# fail_dep is auto-cheated at load; line 16 lies inside target's two-line
# simp step.
CAVEAT_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "gcav";

Theorem fail_dep:
  T /\\ T
Proof
  FAIL_TAC "nope"
QED

Theorem target:
  !a b. a /\\ b ==> b /\\ a
Proof
  rpt strip_tac >>
  simp[boolTheory.CONJ_COMM,
       boolTheory.AND_CLAUSES]
QED

val _ = export_theory();
"""

CAVEATS = ("NOTE: target line 16 is INSIDE step",
           "[context admission history (not a dependency list):",
           "[prefix-skip mode ON:")


async def test_hol_goals_shows_the_caveats_hol_state_at_shows(tmp_path):
    script = tmp_path / "gcavScript.sml"
    script.write_text(CAVEAT_SCRIPT)
    session = "pin_goal_caveats"
    try:
        await _init_file_cursor(file=str(script), session=session)
        for skip_prefix in (False, True):
            state = await hol_state_at(line=16, col=8, session=session,
                                       skip_prefix=skip_prefix)
            goals = await hol_goals(file=str(script), line=16, col=8, session=session,
                                    skip_prefix=skip_prefix)
            shown = [c for c in CAVEATS if c in state]
            assert shown[:1] == [CAVEATS[0]], state
            assert (CAVEATS[2] in state) == skip_prefix, state
            assert (CAVEATS[1] in state) != skip_prefix, state
            for caveat in shown:
                assert caveat in goals, (caveat, goals)
    finally:
        await hol_stop(session=session)


async def test_failed_proof_drain_waits_for_a_concurrent_reader(tmp_path):
    script = tmp_path / "gcavScript.sml"
    script.write_text(CAVEAT_SCRIPT)
    session = HOLSession(str(tmp_path))
    await session.start()
    try:
        cursor = FileProofCursor(script, session)
        await cursor.init()
        thm = next(t for t in cursor._theorems if t.name == "fail_dep")
        reader = asyncio.create_task(session.send(
            "OS.Process.sleep (Time.fromMilliseconds 400); 42;", timeout=10))
        await asyncio.sleep(0.05)
        error = await cursor._cheat_failed_theorem(thm, "error: pinned")
        assert error is None, error
        assert "42" in await reader
        assert "fail_dep" in cursor._failed_proofs
    finally:
        await session.stop()


async def test_hol_state_at_discloses_a_scheduled_reinit(tmp_path):
    script = tmp_path / "gcavScript.sml"
    script.write_text(CAVEAT_SCRIPT)
    session = "pin_reinit_notice"
    try:
        await _init_file_cursor(file=str(script), session=session)
        await hol_state_at(line=16, col=8, session=session)
        script.write_text(CAVEAT_SCRIPT.replace(
            "bossLib;\n", "bossLib;\nopen arithmeticTheory;\n", 1))
        state = await hol_state_at(line=17, col=8, session=session)
        assert "[Session reinit: the edit at line 2 precedes the first theorem" in state, state
        assert _sessions[session].cursor._needs_session_reinit is False
    finally:
        await hol_stop(session=session)
