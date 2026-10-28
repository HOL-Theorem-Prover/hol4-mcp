"""The goal hol_state_at shows must be the one the file produces, after edits
and errors (P4)."""

from hol4_mcp.hol_mcp_server import _init_file_cursor, hol_state_at, hol_stop

STATEMENT_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "stm";

Theorem st:
  !x:num. x + 0 = x
Proof
  gen_tac >>
  simp[]
QED

val _ = export_theory();
"""


async def test_statement_edit_is_not_replayed_incrementally(tmp_path):
    script = tmp_path / "stmScript.sml"
    script.write_text(STATEMENT_SCRIPT)
    session = "si_statement"
    try:
        await _init_file_cursor(file=str(script), session=session)
        before = await hol_state_at(line=9, col=3, session=session)
        assert "x + 0 = x" in before, before
        script.write_text(STATEMENT_SCRIPT.replace("x + 0 = x", "0 + x = x"))
        after = await hol_state_at(line=9, col=3, session=session)
        assert "0 + x = x" in after and "x + 0 = x" not in after, after
        assert "method=incremental" not in after, after
    finally:
        await hol_stop(session=session)


BROKEN_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "brk";

Theorem br:
  !x y. x + y = y + x
Proof
  gen_tac >>
  FAIL_TAC "boom" >>
  simp[]
QED

val _ = export_theory();
"""


async def test_position_after_a_broken_replay_is_not_reused(tmp_path):
    script = tmp_path / "brkScript.sml"
    script.write_text(BROKEN_SCRIPT)
    session = "si_broken"
    try:
        await _init_file_cursor(file=str(script), session=session)
        broken = await hol_state_at(line=11, col=1, session=session)
        assert "boom" in broken, broken
        at_step = await hol_state_at(line=9, col=3, session=session)
        assert "!y. x + y = y + x" in at_step or "∀y. x + y = y + x" in at_step, at_step
        assert "method=reused" not in at_step, at_step
        # The report's next move: shorten the body, then navigate again.
        script.write_text(BROKEN_SCRIPT.replace('FAIL_TAC "boom" >>\n  simp[]', "cheat"))
        shortened = await hol_state_at(line=9, col=3, session=session)
        assert "!y. x + y = y + x" in shortened or "∀y. x + y = y + x" in shortened, shortened
    finally:
        await hol_stop(session=session)


ABORTED_HEADER_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "abt";

val _ = diminish_srw_ss ["ABBREV"];
val _ = OS.Process.sleep (Time.fromSeconds 4);

Theorem t:
  T
Proof
  simp[]
QED

val _ = export_theory();
"""


async def test_prefix_span_aborted_midway_is_not_run_twice(tmp_path):
    script = tmp_path / "abtScript.sml"
    script.write_text(ABORTED_HEADER_SCRIPT)
    session = "si_aborted_header"
    try:
        await _init_file_cursor(file=str(script), session=session)
        aborted = await hol_state_at(line=11, col=3, session=session, timeout=2)
        assert "TIMEOUT" in aborted, aborted
        again = await hol_state_at(line=11, col=3, session=session)
        assert "prefix error" not in again.lower(), again
        assert "=== Goal" in again, again
    finally:
        await hol_stop(session=session)


ABORTED_DEFINITION_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "abd";

Definition inc_def:
  inc (x:num) = x + 1
End
val _ = OS.Process.sleep (Time.fromSeconds 4);

Theorem inc_pos:
  0 < inc x
Proof
  simp[inc_def]
QED

val _ = export_theory();
"""


async def test_prefix_definition_interrupted_midway_is_defined_once(tmp_path):
    import asyncio
    from hol4_mcp.hol_mcp_server import hol_interrupt, hol_send
    script = tmp_path / "abdScript.sml"
    script.write_text(ABORTED_DEFINITION_SCRIPT)
    session = "si_aborted_definition"
    try:
        await _init_file_cursor(file=str(script), session=session)
        navigation = asyncio.create_task(hol_state_at(line=14, col=1, session=session))
        await asyncio.sleep(2)
        assert not navigation.done()
        await hol_interrupt(session=session)
        assert (await navigation).startswith("INTERRUPTED")
        from hol4_mcp.hol_mcp_server import _sessions
        assert _sessions[session].cursor._context_rewind_pending
        again = await hol_state_at(line=14, col=1, session=session)
        assert "No goals" in again or "proof complete" in again.lower(), again
        assert "prefix error" not in again.lower(), again
        consts = await hol_send('constants "abd";', session=session)
        assert "inc'" not in consts, consts
    finally:
        await hol_stop(session=session)
