"""Test the HOL MCP server tools."""

import asyncio
import os
import shutil
import signal

import pytest
from pathlib import Path

from hol4_mcp.hol_mcp_server import (
    hol_start as _hol_start,
    hol_send as _hol_send,
    hol_sessions as _hol_sessions,
    hol_stop as _hol_stop,
    hol_log as _hol_log,
    hol_logs as _hol_logs,
    holmake as _holmake,
    _init_file_cursor,  # Internal helper (not MCP tool)
    hol_state_at as _hol_state_at,
    hol_file_status as _hol_file_status,
    hol_check_proof as _hol_check_proof,
    _kill_process_group,
    _sessions,
    _SESSION_IDLE_TIMEOUT,
    _file_offset_to_line_col,
)

# In FastMCP 3.x, @mcp.tool() returns the original function unchanged
# (no .fn unwrapping needed). Alias for clarity.
hol_start = _hol_start
hol_send = _hol_send
hol_sessions = _hol_sessions
hol_stop = _hol_stop
hol_log = _hol_log
hol_logs = _hol_logs
holmake = _holmake
hol_file_init = _init_file_cursor
hol_state_at = _hol_state_at
hol_check_proof = _hol_check_proof
hol_file_status = _hol_file_status

FIXTURES_DIR = Path(__file__).parent / "fixtures"


@pytest.fixture
def workdir():
    return str(FIXTURES_DIR)


@pytest.fixture
def isolated_workdir(tmp_path):
    """Copy fixtures to isolated temp directory for tests that modify state."""
    # Copy all fixture files to temp dir
    for f in FIXTURES_DIR.iterdir():
        if f.is_file():
            shutil.copy(f, tmp_path / f.name)
    return str(tmp_path)


async def test_session_lifecycle(workdir):
    """Test basic session start/list/send/stop."""
    result = await hol_start(workdir=workdir, name="test")
    assert "Session 'test' started" in result
    assert "HOL started (PID" in result

    try:
        result = await hol_sessions()
        assert "test" in result
        assert "running" in result

        result = await hol_send(session="test", command="1 + 1;")
        assert "val it = 2" in result
    finally:
        result = await hol_stop(session="test")
        assert "Session 'test' stopped" in result


async def test_hol_start_concurrent_same_name_is_singleton(tmp_path):
    """Concurrent hol_start calls for same name should not leak extra HOL sessions."""
    session = "start_race_test"
    workdir = str(tmp_path)

    await hol_stop(session=session)
    try:
        r1, r2 = await asyncio.gather(
            hol_start(workdir=workdir, name=session),
            hol_start(workdir=workdir, name=session),
        )

        started = sum("started" in r.lower() for r in (r1, r2))
        already = sum("already running" in r.lower() for r in (r1, r2))
        assert started == 1
        assert already == 1

        sessions = await hol_sessions()
        # Exactly one registry entry for this session name
        assert sessions.count(session) == 1
    finally:
        await hol_stop(session=session)


async def test_goaltree_raw_hol_send(workdir):
    """Test goaltree mode via raw hol_send (not cursor - cursor uses goalstack only)."""
    await hol_stop(session="gt_test")
    await hol_start(workdir=workdir, name="gt_test")

    try:
        result = await hol_send(session="gt_test", command="gt `1 + 1 = 2`;")
        assert "Proof manager status: 1 proof" in result
        assert "Initial goal:" in result

        result = await hol_send(session="gt_test", command='etq "EVAL_TAC";')
        assert "OK" in result

        # Check proof state via hol_send
        result = await hol_send(session="gt_test", command="top_goals();")
        assert "val it = []: goal list" in result  # No remaining goals
    finally:
        await hol_stop(session="gt_test")


async def test_p_output_multiline_integration(workdir):
    """Integration test: parse_p_output handles multi-line val it format from real HOL."""
    from hol4_mcp.hol_file_parser import parse_p_output
    from hol4_mcp.hol_mcp_server import _sessions

    await hol_stop(session="p_multi_test")
    await hol_start(workdir=workdir, name="p_multi_test")

    try:
        # Use session.send directly to bypass hol_send proof-state guard
        session = _sessions["p_multi_test"].session
        await session.send("gt `A /\\ B ==> B /\\ A`;")
        await session.send('etq "strip_tac";')
        await session.send('etq "conj_tac";')
        await session.send('etq "first_assum ACCEPT_TAC";')
        await session.send('etq "first_assum ACCEPT_TAC";')

        # p() on complete proof can produce multi-line "val it = ..." format
        result = await session.send("p();")
        # Strip timing suffix that session.send doesn't add but format may include
        result = result.strip()

        # Verify we got multi-line format with ": proof" type annotation
        assert "\n" in result.strip(), f"Expected multi-line output, got: {result!r}"
        assert ": proof" in result, f"Expected complete proof format, got: {result!r}"

        # Check for multi-line val it format: "val it =" on its own line or
        # single-line format with content after "val it = "
        has_multiline_val_it = "val it =\n" in result or "val it = \n" in result
        has_singleline_val_it = "val it = " in result and ": proof" in result

        # Either format is valid - the key is parse_p_output handles it
        assert has_multiline_val_it or has_singleline_val_it, (
            f"Expected val it format, got: {result!r}"
        )

        # Verify parse_p_output handles whatever format HOL produced
        parsed = parse_p_output(result)
        assert parsed is not None, f"parse_p_output failed on: {result!r}"
        assert "strip_tac" in parsed
        assert "conj_tac" in parsed
        assert ": proof" not in parsed  # Type annotation stripped
    finally:
        await hol_stop(session="p_multi_test")


async def test_db_search(workdir):
    """Test theorem database search."""
    await hol_stop(session="db_test")
    await hol_start(workdir=workdir, name="db_test")

    try:
        result = await hol_send(session="db_test", command='DB.find "ADD";', timeout=15)
        assert "ADD" in result
        assert "⊢" in result  # Theorem statements contain turnstile
    finally:
        await hol_stop(session="db_test")


async def test_build_and_logs(isolated_workdir):
    """Test holmake generates logs, then test hol_logs/hol_log."""
    result = await holmake(workdir=isolated_workdir, target="testTheory")
    assert "Build succeeded" in result
    assert "testTheory" in result

    result = await hol_logs(workdir=isolated_workdir)
    assert "Build logs:" in result
    assert "testTheory" in result

    result = await hol_log(workdir=isolated_workdir, theory="testTheory", limit=500)
    assert 'theory "test"' in result.lower()

    result = await hol_log(workdir=isolated_workdir, theory="test", limit=500)
    assert 'theory "test"' in result.lower()


async def test_build_failure_includes_logs(isolated_workdir):
    """Test that build failure includes log output."""
    result = await holmake(workdir=isolated_workdir, target="failTheory")
    assert "Build failed" in result
    assert "=== Build Logs ===" in result
    assert "failTheory" in result


async def test_log_nonexistent(workdir):
    """Test hol_log for non-existent theory."""
    result = await hol_log(workdir=workdir, theory="nonexistent")
    assert "Log not found: nonexistent" in result
    assert "Available:" in result


async def test_holmake_env_in_output(isolated_workdir):
    """Test that holmake returns env in output on success."""
    import json

    # Build with env - should include in output
    test_env = {"TEST_VAR": "test_value"}
    result = await holmake(workdir=isolated_workdir, target="testTheory", env=test_env)
    assert "Build succeeded" in result
    assert "HOLMAKE_ENV: " in result

    # Parse env from output
    import re
    match = re.search(r"HOLMAKE_ENV: (\{.*\})", result)
    assert match is not None
    parsed_env = json.loads(match.group(1))
    assert parsed_env == test_env

    # Build without env - no HOLMAKE_ENV line
    result = await holmake(workdir=isolated_workdir, target="testTheory", env=None)
    assert "Build succeeded" in result
    assert "HOLMAKE_ENV: " not in result


# =============================================================================
# File Cursor MCP Tool Tests
# =============================================================================


async def test_file_init_lists_theorems(tmp_path):
    """Test hol_file_init parses file and lists theorems."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        result = await hol_file_init(file=str(test_file), session="file_init_test")
        assert "Theorems:" in result
        assert "cheats" in result.lower()
        # Should list cheats to fix
        assert "needs_proof" in result
        assert "partial_proof" in result
    finally:
        await hol_stop(session="file_init_test")


async def test_file_status_shows_cheats(tmp_path):
    """Test hol_file_status lists cheats and active theorem."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="status_test")
        result = await hol_file_status(session="status_test")

        # Should show file info
        assert "File:" in result
        assert "Progress:" in result
        # Should list cheats
        assert "needs_proof" in result
        assert "partial_proof" in result
    finally:
        await hol_stop(session="status_test")


async def test_file_init_restarts_on_workdir_change(tmp_path):
    """Test hol_file_init restarts session when workdir changes.

    Regression test for BUG_workdir_mismatch: when hol_file_init was called
    with a different workdir, the session kept using the old workdir.
    """
    # Create two directories with test files
    dir_a = tmp_path / "dirA"
    dir_b = tmp_path / "dirB"
    dir_a.mkdir()
    dir_b.mkdir()

    file_a = dir_a / "testScript.sml"
    file_b = dir_b / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", file_a)
    shutil.copy(FIXTURES_DIR / "testScript.sml", file_b)

    try:
        # Start session in dir_a
        result = await hol_file_init(file=str(file_a), session="workdir_test")
        assert "Theorems:" in result

        # Check workdir via sessions list
        sessions = await hol_sessions()
        assert "dirA" in sessions

        # Now init for file in dir_b - should restart session
        result = await hol_file_init(file=str(file_b), session="workdir_test", workdir=str(dir_b))
        assert "Theorems:" in result

        # Check workdir changed
        sessions = await hol_sessions()
        assert "dirB" in sessions
        # Old workdir should not be present (session was restarted)
        assert "dirA" not in sessions or "workdir_test" not in sessions.split("dirA")[0]
    finally:
        await hol_stop(session="workdir_test")


async def test_file_init_restart_preserves_session_env(tmp_path):
    """Auto-restart in hol_file_init should preserve session env (e.g., VFMDIR)."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    session = "env_preserve_test"
    env = {"VFMDIR": "/tmp/vfm"}

    await hol_stop(session=session)
    try:
        # Start with env and initialize cursor
        start_result = await hol_start(workdir=str(tmp_path), name=session, env=env)
        assert "started" in start_result.lower()

        init_result = await hol_file_init(file=str(test_file), session=session)
        assert "Theorems:" in init_result
        assert _sessions[session].env == env

        # Edit file to trigger auto-restart path in _init_file_cursor
        content = test_file.read_text()
        test_file.write_text(content + "\n(* trigger restart *)\n")

        init_result2 = await hol_file_init(file=str(test_file), session=session)
        assert "Theorems:" in init_result2

        # Env must survive restart.
        assert _sessions[session].env == env
    finally:
        await hol_stop(session=session)


async def test_state_at_returns_goals(tmp_path):
    """Test hol_state_at returns goals when called on a line inside a theorem."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="state_at_test")

        # needs_proof theorem starts at line 18, Proof at line 20, cheat at line 21
        # Get state at line 21 (inside the proof, at the cheat line)
        result = await hol_state_at(session="state_at_test", line=21, col=1)

        # Should show tactic info (even if 0/N since cheat is the only tactic)
        assert "Tactic" in result
        # Should show goals (proof is not complete since cheat doesn't prove anything)
        assert "Goal" in result or "goal" in result.lower()
        # Should NOT have error about position outside theorem
        assert "not within any theorem" not in result
    finally:
        await hol_stop(session="state_at_test")


async def test_state_at_outside_theorem(tmp_path):
    """Test hol_state_at returns error when called outside any theorem."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="outside_test")

        # Line 8 is 'val _ = new_theory "test";' - outside any theorem
        result = await hol_state_at(session="outside_test", line=8, col=1)

        # Should return an error about position not being in a theorem
        assert "ERROR" in result
        assert "not within any theorem" in result
    finally:
        await hol_stop(session="outside_test")


async def test_state_at_qed_line(tmp_path):
    """Test hol_state_at on QED line shows final state (proof complete)."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="qed_test")

        # add_zero theorem: Proof at line 14, simp[] at line 14, QED at line 15
        # Querying QED line should show final state with all tactics replayed
        result = await hol_state_at(session="qed_test", line=15, col=1)

        # Should show all tactics replayed
        assert "Tactic" in result
        # Should show proof complete (no goals)
        assert "proof complete" in result.lower()
        # Should NOT have error about position
        assert "ERROR" not in result
    finally:
        await hol_stop(session="qed_test")


async def test_state_at_after_qed_line(tmp_path):
    """Test hol_state_at after QED line returns error."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="after_qed_test")

        # add_zero theorem ends at QED on line 15
        # Line 16 is blank, line 17 starts next theorem
        # Querying line 16 should give an error (outside theorem bounds)
        result = await hol_state_at(session="after_qed_test", line=16, col=1)

        # Should have error about position not in theorem
        assert "ERROR" in result or "not within any theorem" in result
        # Should NOT say "proof complete" since this is an error case
        assert "proof complete" not in result.lower() or "ERROR" in result
    finally:
        await hol_stop(session="after_qed_test")


async def test_state_at_auto_init(tmp_path):
    """Test hol_state_at with file parameter auto-calls hol_file_init."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    session_name = "auto_init_test"
    await hol_stop(session=session_name)  # Ensure clean state

    try:
        # Call hol_state_at with file parameter - should auto-init
        result = await hol_state_at(
            session=session_name, line=21, col=1, file=str(test_file)
        )

        # Should work without explicit hol_file_init
        assert "Tactic" in result
        assert "ERROR: No cursor" not in result
    finally:
        await hol_stop(session=session_name)


async def test_file_init_auto_starts_session(tmp_path):
    """Test hol_file_init auto-starts HOL session if not running."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    session_name = "auto_start_test"

    # Ensure session doesn't exist
    await hol_stop(session=session_name)

    try:
        # hol_file_init should auto-start session
        result = await hol_file_init(file=str(test_file), session=session_name)

        # Should succeed and show theorem count
        assert "Theorems:" in result

        # Verify session is now running
        sessions_result = await hol_sessions()
        assert session_name in sessions_result
        assert "running" in sessions_result
    finally:
        await hol_stop(session=session_name)


async def test_state_at_after_file_edit(tmp_path):
    """Test hol_state_at works correctly after file content changes."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="edit_test")

        # First call to state_at - get state at needs_proof theorem
        result1 = await hol_state_at(session="edit_test", line=21, col=1)
        assert "Tactic" in result1

        # Modify the file - add a comment (cursor should detect change and reparse)
        content = test_file.read_text()
        new_content = content.replace(
            "(* Theorem with cheat for testing cheat detection *)",
            "(* MODIFIED: Theorem with cheat for testing cheat detection *)"
        )
        test_file.write_text(new_content)

        # Call state_at again - cursor should reparse the file
        result2 = await hol_state_at(session="edit_test", line=21, col=1)

        # Should still work (reparse successful)
        assert "Tactic" in result2
        # Should NOT error out
        assert "ERROR" not in result2 or "not within any theorem" not in result2
    finally:
        await hol_stop(session="edit_test")


async def test_state_at_reinitializes_on_prelude_change(tmp_path):
    """Changing open/Theory/Ancestors prelude must invalidate cached context.

    Regression: prelude edits were reparsed but HOL session context stayed stale,
    so removed opens still appeared to work.
    """
    with_open = '''\
open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val _ = new_theory "cachetest";

Theorem t:
  !n:num. n + 1 = SUC n
Proof
  simp[ADD1]
QED

val _ = export_theory();
'''
    without_open = with_open.replace("open arithmeticTheory;\n", "")

    test_file = tmp_path / "cacheScript.sml"
    test_file.write_text(with_open)
    session = "prelude_inval_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # Baseline: with arithmeticTheory open, proof replays to completion.
        qed_line_with_open = next(
            i + 1 for i, line in enumerate(with_open.splitlines()) if line.strip() == "QED"
        )
        r1 = await hol_state_at(session=session, line=qed_line_with_open, col=1)
        assert "proof complete" in r1.lower(), f"Expected proof complete before edit: {r1}"

        # Edit prelude: remove open arithmeticTheory; ADD1 should no longer resolve.
        test_file.write_text(without_open)

        qed_line_without_open = next(
            i + 1 for i, line in enumerate(without_open.splitlines()) if line.strip() == "QED"
        )
        r2 = await hol_state_at(session=session, line=qed_line_without_open, col=1)

        assert "ERROR" in r2, f"Expected replay error after prelude change: {r2}"
        assert "proof complete" not in r2.lower(), f"Should not still be complete after removing open: {r2}"
        assert (
            "ADD1" in r2
            or "has not been declared" in r2
            or "Tactic replay failed" in r2
        ), f"Expected missing ADD1-style failure after prelude change: {r2}"
    finally:
        await hol_stop(session=session)


async def test_state_at_with_val_fun_definition_between_theorems(tmp_path):
    """Regression: hol_state_at should work with val/fun/Definition between theorems."""
    script = tmp_path / "middefsScript.sml"
    content = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "middefs";

Theorem first_thm:
  T
Proof
  simp[]
QED

val mid = TRUTH;
fun midfun x = x;
Definition mid_def:
  mid_const = T
End

Theorem second_thm:
  mid_const
Proof
  simp[mid_def]
QED

val _ = export_theory();
'''
    script.write_text(content)
    session = "state_at_middefs_test"

    # Compute key lines dynamically so edits to fixture text don't break the test.
    lines = content.splitlines()
    simp_line = next(i + 1 for i, line in enumerate(lines) if "simp[mid_def]" in line)
    qed_lines = [i + 1 for i, line in enumerate(lines) if line.strip() == "QED"]
    second_qed_line = qed_lines[-1]

    try:
        init_result = await hol_file_init(file=str(script), session=session)
        assert "Theorems: 2" in init_result

        # Inside second theorem proof body.
        r1 = await hol_state_at(session=session, line=simp_line, col=3)
        assert "Theorem: second_thm" in r1
        assert "ERROR" not in r1

        # QED line of second theorem should show completed proof.
        r2 = await hol_state_at(session=session, line=second_qed_line, col=1)
        assert "Theorem: second_thm" in r2
        assert "proof complete" in r2.lower()
    finally:
        await hol_stop(session=session)


async def test_check_proof_cheat_reports_not_replayed_note(tmp_path):
    """hol_check_proof should clarify that cheat proofs are not replayed."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)
    session = "check_cheat_note_test"

    try:
        await hol_file_init(file=str(test_file), session=session)
        r = await hol_check_proof(theorem="needs_proof", session=session)
        assert "Status: CHEAT (not verified)" in r
        assert "not replayed" in r
    finally:
        await hol_stop(session=session)


async def test_check_proof_deleted_file_returns_error(tmp_path):
    """Regression: hol_check_proof should return an ERROR, not raise, when file was deleted."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    session = "deleted_file_check_test"
    try:
        await hol_file_init(file=str(test_file), session=session)
        test_file.unlink()

        result = await hol_check_proof(
            theorem="add_zero", file=str(test_file), session=session
        )
        assert result.startswith("ERROR: File not found:")
    finally:
        await hol_stop(session=session)


async def test_state_at_uses_checkpoint_on_repeat(tmp_path):
    """Test that state_at uses checkpoint on second call (O(1) access)."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)

    try:
        await hol_file_init(file=str(test_file), session="checkpoint_test")

        # First call - builds checkpoint
        result1 = await hol_state_at(session="checkpoint_test", line=15, col=1)
        assert "Tactic" in result1

        # Second call to same position - should use checkpoint
        result2 = await hol_state_at(session="checkpoint_test", line=15, col=1)
        assert "Tactic" in result2

        # Both should succeed (proof complete for add_zero theorem)
        assert "proof complete" in result1.lower() or "Goals remaining: 0" in result1
        assert "proof complete" in result2.lower() or "Goals remaining: 0" in result2
    finally:
        await hol_stop(session="checkpoint_test")


async def test_state_at_reuses_session_state(tmp_path):
    """Test that state_at reuses session state for same/forward positions."""
    # Simple proof: simp[] solves T. Navigate via Proof line (tactic_idx=0)
    # and QED line (tactic_idx=total) to stay on step boundaries.
    test_file = tmp_path / "testScript.sml"
    test_file.write_text(
        'open HolKernel boolLib bossLib;\n'       # line 1
        '\n'                                       # line 2
        'val _ = new_theory "test";\n'             # line 3
        '\n'                                       # line 4
        'Theorem simple:\n'                         # line 5
        '  T\n'                                     # line 6
        'Proof\n'                                    # line 7
        '  simp[]\n'                                 # line 8: step 0
        'QED\n'                                      # line 9
        '\n'
        'val _ = export_theory();\n'
    )

    try:
        await hol_file_init(file=str(test_file), session="reuse_test")

        # Navigate to QED to build checkpoint (all steps replayed)
        result_qed = await hol_state_at(session="reuse_test", line=9, col=1)
        assert "proof complete" in result_qed.lower() or "Goals remaining: 0" in result_qed

        # Navigate to Proof line (tactic_idx=0) via checkpoint
        result1 = await hol_state_at(session="reuse_test", line=7, col=1)
        assert "method=checkpoint" in result1, f"Expected checkpoint: {result1}"

        # Same position again — should reuse (exact match)
        result2 = await hol_state_at(session="reuse_test", line=7, col=1)
        assert "method=reused" in result2, f"Expected reused: {result2}"

        # Forward to QED (tactic_idx=total) — incremental forward
        result3 = await hol_state_at(session="reuse_test", line=9, col=1)
        assert "method=reused" in result3, f"Expected reused (forward): {result3}"

        # Backward to Proof line — can't reuse, needs checkpoint
        result4 = await hol_state_at(session="reuse_test", line=7, col=1)
        assert "method=reused" not in result4, f"Backward should not reuse: {result4}"
    finally:
        await hol_stop(session="reuse_test")


async def test_state_at_reuse_invalidation_on_edit(tmp_path):
    """File edit must invalidate session state reuse — stale goals are wrong."""
    test_file = tmp_path / "testScript.sml"
    test_file.write_text(
        'open HolKernel boolLib bossLib;\n'
        '\n'
        'val _ = new_theory "test";\n'
        '\n'
        'Theorem simple:\n'
        '  T\n'
        'Proof\n'
        '  simp[]\n'
        'QED\n'
        '\n'
        'val _ = export_theory();\n'
    )

    try:
        await hol_file_init(file=str(test_file), session="reuse_inval")

        # Navigate to Proof line — establishes session state
        result1 = await hol_state_at(session="reuse_inval", line=7, col=1)
        assert "method=reused" in result1 or "method=checkpoint" in result1 or "method=replay" in result1

        # Same position again — should reuse
        result2 = await hol_state_at(session="reuse_inval", line=7, col=1)
        assert "method=reused" in result2, f"Expected reused: {result2}"

        # Edit file on disk — change simp[] to strip_tac (breaks proof)
        content = test_file.read_text()
        test_file.write_text(content.replace('simp[]', 'strip_tac'))

        # Same position — MUST NOT reuse (file changed)
        result3 = await hol_state_at(session="reuse_inval", line=7, col=1)
        assert "method=reused" not in result3, f"Reuse after file edit! {result3}"
    finally:
        await hol_stop(session="reuse_inval")


async def test_state_at_reuse_partial_offset(tmp_path):
    """Partial offset reuse: navigating to same mid-step position twice reuses."""
    test_file = tmp_path / "testScript.sml"
    # Proof with `by` creates a partial position inside the step
    test_file.write_text(
        'open HolKernel boolLib bossLib;\n'
        '\n'
        'val _ = new_theory "test";\n'
        '\n'
        'Theorem by_test:\n'
        '  T /\\ T\n'
        'Proof\n'
        '  `T` by simp[] >> simp[]\n'
        'QED\n'
        '\n'
        'val _ = export_theory();\n'
    )

    try:
        await hol_file_init(file=str(test_file), session="reuse_partial")

        # First navigation to partial position (inside `by` step)
        # Line 9 col 3 lands inside the `by` substep
        result1 = await hol_state_at(session="reuse_partial", line=9, col=3)
        assert "ERROR" not in result1

        # Same partial position again — should reuse (exact offset match)
        result2 = await hol_state_at(session="reuse_partial", line=9, col=3)
        assert "method=reused" in result2, f"Expected reused for same partial: {result2}"

        # Step boundary (Proof line, tactic_idx=0) — currently at partial, can't reuse
        result3 = await hol_state_at(session="reuse_partial", line=8, col=1)
        assert "method=reused" not in result3, f"Partial->boundary should not reuse: {result3}"
    finally:
        await hol_stop(session="reuse_partial")


async def test_state_at_reuse_multi_step_forward(tmp_path):
    """Forward delta: multi-step forward reuses by executing only delta commands."""
    test_file = tmp_path / "testScript.sml"
    # 2-step proof: conj_tac >- conj_tac, simp[]
    test_file.write_text(
        'open HolKernel boolLib bossLib;\n'
        '\n'
        'val _ = new_theory "test";\n'
        '\n'
        'Theorem multi:\n'
        '  T /\\ T\n'
        'Proof\n'
        '  conj_tac >> simp[]\n'
        'QED\n'
        '\n'
        'val _ = export_theory();\n'
    )

    try:
        await hol_file_init(file=str(test_file), session="reuse_fwd")

        # Go to QED (tactic_idx=total) first to ensure full proof replayed
        result_qed = await hol_state_at(session="reuse_fwd", line=9, col=1)

        # Navigate to Proof line (tactic_idx=0, before any tactic)
        result0 = await hol_state_at(session="reuse_fwd", line=8, col=1)
        # Should use checkpoint (backward from end)

        # Same position — exact match reuse
        result1 = await hol_state_at(session="reuse_fwd", line=8, col=1)
        assert "method=reused" in result1, f"Expected reused: {result1}"

        # Forward to QED (multi-step: tactic_idx 0 -> total) — reuse via delta
        result2 = await hol_state_at(session="reuse_fwd", line=9, col=1)
        assert "method=reused" in result2, f"Expected reused (multi-step forward): {result2}"
    finally:
        await hol_stop(session="reuse_fwd")


async def test_checkpoint_with_then_chain(tmp_path):
    """Test O(1) checkpoint navigation with THEN chain (>>) treats it as one step.

    Regression test: Previously step_positions gave 3 positions for "a >> b >> c"
    but step_commands gave 1 e() call, causing backup_n(3-idx) to fail.
    Now we use step_plan which gives consistent step count.
    """
    # Create test file with THEN chain
    test_file = tmp_path / "testScript.sml"
    test_file.write_text('''
open HolKernel boolLib bossLib;

val _ = new_theory "test";

Theorem then_chain:
  T /\\ T
Proof
  conj_tac >> simp[] >> simp[]
QED

val _ = export_theory();
''')

    try:
        result = await hol_file_init(file=str(test_file), session="then_test")
        assert "error" not in str(result).lower()

        # Request state at QED line (line 10) - builds checkpoint
        result1 = await hol_state_at(session="then_test", line=10, col=1)
        assert "error" not in result1.lower(), f"First call failed: {result1}"

        # Request state at start of proof (line 9) - should use checkpoint
        result2 = await hol_state_at(session="then_test", line=9, col=3)
        assert "error" not in result2.lower(), f"Second call failed: {result2}"

        # Should show goal at start (before THEN chain executes)
        # The THEN chain is ONE step, so position inside it maps to before it
        assert "Goal" in result2 or "goal" in result2.lower()
    finally:
        await hol_stop(session="then_test")


# =============================================================================
# by / sg Integration Tests
# =============================================================================

# Test script with `by` and `sg` proofs (written inline since fixtures are shared)
BY_SG_SCRIPT = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "bysg";

(* `by` in a >> chain: 3 steps *)
Theorem by_in_chain:
  (P ==> Q) ==> P ==> Q /\\ T
Proof
  rpt strip_tac >>
  `Q` by (res_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* `sg` with >- in a >> chain: 2 steps *)
Theorem sg_test:
  (P ==> Q) ==> P ==> Q /\\ T
Proof
  rpt strip_tac >>
  sg `Q` >-
    (res_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* Top-level `by`: 1 atomic step *)
Theorem by_toplevel:
  T /\\ T
Proof
  `T` by simp[] >> simp[]
QED

val _ = export_theory();
'''


async def test_state_at_by_in_chain(tmp_path):
    """Test hol_state_at navigates through a proof with `by` in a >> chain.

    `by` creates a ThenLT wrapped in a Group, so step_plan gives 3 steps:
    rpt strip_tac, `Q` by (...), simp[].
    """
    test_file = tmp_path / "bysgScript.sml"
    test_file.write_text(BY_SG_SCRIPT)
    session = "by_chain_test"

    try:
        result = await hol_file_init(file=str(test_file), session=session)
        assert "Theorems: 3" in result

        # Line 9: rpt strip_tac (before `by` clause)
        r = await hol_state_at(session=session, line=9, col=3)
        assert "Tactic" in r
        assert "ERROR" not in r

        # Line 10: `Q` by (...) — at the by clause
        r = await hol_state_at(session=session, line=10, col=3)
        assert "Tactic" in r
        assert "ERROR" not in r
        # Should show goals (some remain since simp[] hasn't run yet)
        assert "Goal" in r

        # Line 11: simp[] — after by clause
        r = await hol_state_at(session=session, line=11, col=3)
        assert "Tactic" in r
        assert "ERROR" not in r

        # QED line (line 12): proof complete
        r = await hol_state_at(session=session, line=12, col=1)
        assert "proof complete" in r.lower()
    finally:
        await hol_stop(session=session)


async def test_state_at_sg_with_subgoal_tactic(tmp_path):
    """Test hol_state_at navigates through a proof with `sg` and >-.

    `sg` + >- creates a ThenLT at top of the >> chain, so step_plan gives 2 steps:
    (rpt strip_tac >> sg `Q` >- ...), simp[].
    """
    test_file = tmp_path / "bysgScript.sml"
    test_file.write_text(BY_SG_SCRIPT)
    session = "sg_test"

    try:
        result = await hol_file_init(file=str(test_file), session=session)
        assert "Theorems: 3" in result

        # Line 18: rpt strip_tac (start of proof body)
        r = await hol_state_at(session=session, line=18, col=3)
        assert "Tactic" in r
        assert "ERROR" not in r

        # Line 21: simp[] — after the sg block
        r = await hol_state_at(session=session, line=21, col=3)
        assert "Tactic" in r
        assert "ERROR" not in r

        # QED line (line 22): proof complete
        r = await hol_state_at(session=session, line=22, col=1)
        assert "proof complete" in r.lower()
    finally:
        await hol_stop(session=session)


async def test_state_at_by_toplevel(tmp_path):
    """Test hol_state_at with top-level `by` (entire proof is 1 atomic step).

    Prefix path provides fine-grained navigation within the single step.
    """
    test_file = tmp_path / "bysgScript.sml"
    test_file.write_text(BY_SG_SCRIPT)
    session = "by_top_test"

    try:
        result = await hol_file_init(file=str(test_file), session=session)
        assert "Theorems: 3" in result

        # Line 28: `T` by simp[] >> simp[] — the entire proof body
        r = await hol_state_at(session=session, line=28, col=1)
        assert "Tactic" in r
        assert "ERROR" not in r

        # QED line (line 29): proof complete
        r = await hol_state_at(session=session, line=29, col=1)
        assert "proof complete" in r.lower()
    finally:
        await hol_stop(session=session)


async def test_check_proof_by_sg_theorems(tmp_path):
    """Test hol_check_proof works for theorems using `by` and `sg`."""
    test_file = tmp_path / "bysgScript.sml"
    test_file.write_text(BY_SG_SCRIPT)
    session = "check_by_test"

    try:
        for thm_name in ["by_in_chain", "sg_test", "by_toplevel"]:
            r = await hol_check_proof(
                theorem=thm_name, file=str(test_file), session=session
            )
            assert "OK" in r, f"{thm_name} should pass: {r}"
            assert "FAILED" not in r, f"{thm_name} should not fail: {r}"
    finally:
        await hol_stop(session=session)


async def test_state_at_nested_subgoal_suggestion(tmp_path):
    """state_at inside a `by` step shows suspend/Resume suggestion."""
    test_file = tmp_path / "bysgScript.sml"
    test_file.write_text(BY_SG_SCRIPT)
    session = "nested_sg_test"

    try:
        result = await hol_file_init(file=str(test_file), session=session)
        assert "Theorems: 3" in result

        # Line 10 col 30 is inside the `by` clause of by_in_chain,
        # within `first_assum ACCEPT_TAC`. This is inside a step with
        # goal routing — should suggest suspend/Resume.
        r = await hol_state_at(session=session, line=10, col=30)
        assert "suspend" in r.lower() or "Resume" in r, (
            f"Should suggest suspend/Resume for nested subgoal: {r}"
        )

        # Step boundary (line 9 col 3 = start of rpt strip_tac) should NOT suggest.
        r = await hol_state_at(session=session, line=9, col=3)
        assert "suspend" not in r.lower() and "Resume" not in r, (
            f"Should NOT suggest suspend/Resume at step boundary: {r}"
        )
    finally:
        await hol_stop(session=session)


# Test script with a broken ThenLT proof (1 coarse step, failure at FAIL_TAC)
# strip_tac >> conj_tac >- arm1 >- FAIL_TAC gives 1 atomic step.
# Uses strip_tac (not rpt) so conj_tac is the intended splitter.
BROKEN_THENLT_SCRIPT = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "broken";

Theorem broken_thenlt:
  (A:bool) /\\ B ==> B /\\ A
Proof
  strip_tac >> conj_tac >-
    (first_assum ACCEPT_TAC) >-
    FAIL_TAC "intentional failure"
QED

val _ = export_theory();
'''


async def test_check_proof_substep_pinpoints_failure(tmp_path):
    """Test hol_check_proof pinpoints the failing tactic in a ThenLT proof.

    Proof: strip_tac >> conj_tac >- ACCEPT >- FAIL_TAC
    ThenLT arm decomposition gives 4 steps, directly pinpointing FAIL_TAC.
    """
    test_file = tmp_path / "brokenScript.sml"
    test_file.write_text(BROKEN_THENLT_SCRIPT)
    session = "narrow_test"

    try:
        r = await hol_check_proof(
            theorem="broken_thenlt", file=str(test_file), session=session, trace=False
        )
        assert "FAILED" in r, f"Should fail: {r}"
        # ThenLT decomposition pinpoints FAIL_TAC directly as its own step
        assert "FAIL_TAC" in r, f"Should identify FAIL_TAC as failing: {r}"
        # hol_state_at hint should point to the failure location
        assert "hol_state_at" in r

        # Also verify trace=True shows FAIL_TAC
        r2 = await hol_check_proof(
            theorem="broken_thenlt", file=str(test_file), session=session, trace=True
        )
        assert "FAIL_TAC" in r2, f"Trace mode should identify FAIL_TAC: {r2}"
    finally:
        await hol_stop(session=session)


# Broken replay script: first tactic succeeds, second tactic fails.
BROKEN_TWO_STEP_SCRIPT = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "broken2";

Theorem broken_two_step:
  T /\\ T
Proof
  conj_tac
  >> FAIL_TAC "boom"
QED

val _ = export_theory();
'''


async def test_state_at_broken_two_step_start_does_not_over_replay(tmp_path):
    """state_at at proof start should not run later failing tactics.

    Regression: checkpoint-building path replayed whole proof, so a failure in
    a later tactic polluted the state at an earlier position.
    """
    test_file = tmp_path / "brokenTwoStepScript.sml"
    test_file.write_text(BROKEN_TWO_STEP_SCRIPT)
    session = "broken_two_step_start_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # Start of proof body (before any tactic)
        r = await hol_state_at(session=session, line=8, col=3)
        assert "Tactic 0/2" in r
        assert "ERROR: Tactic replay failed" not in r
        # Should show the original single goal, not post-conj_tac subgoals
        assert "T /\\ T" in r or "T ∧ T" in r
    finally:
        await hol_stop(session=session)


async def test_state_at_broken_two_step_qed_reports_stuck_location(tmp_path):
    """state_at on QED for broken proof should refuse to show goals (strict mode).

    When replay fails before reaching the requested position, the default
    behavior is to refuse to show goals and point the user to the failure.
    """
    test_file = tmp_path / "brokenTwoStepScript.sml"
    test_file.write_text(BROKEN_TWO_STEP_SCRIPT)
    session = "broken_two_step_qed_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # QED line: replay should fail at second tactic.
        # Strict mode (default): no goals shown, clear PROOF BROKEN message.
        r = await hol_state_at(session=session, line=10, col=1)
        assert "PROOF BROKEN" in r
        assert "ERROR" in r
        assert "=== Goals ===" not in r  # Goals section suppressed in strict mode
        assert "hol_state_at" in r  # Suggests inspecting failure point
    finally:
        await hol_stop(session=session)


async def test_state_at_broken_show_partial(tmp_path):
    """state_at with show_partial=True shows best-effort goals on broken proof."""
    test_file = tmp_path / "brokenTwoStepScript.sml"
    test_file.write_text(BROKEN_TWO_STEP_SCRIPT)
    session = "broken_partial_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # QED line with show_partial=True: should show partial goals
        r = await hol_state_at(
            session=session, line=10, col=1, show_partial=True
        )
        assert "PROOF BROKEN" in r
        assert "Goal" in r and "failure point" in r
        # conj_tac succeeded, so we should see 2 subgoals (T and T)
    finally:
        await hol_stop(session=session)


async def test_state_at_broken_error_survives_truncation(tmp_path):
    """Error info must survive output truncation (GH issue #4 comment)."""
    test_file = tmp_path / "brokenTwoStepScript.sml"
    test_file.write_text(BROKEN_TWO_STEP_SCRIPT)
    session = "broken_truncation_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # Request with very small max_output to force truncation
        r = await hol_state_at(
            session=session, line=10, col=1, max_output=200
        )
        # Error must be visible even when truncated
        assert "ERROR" in r
        assert "PROOF BROKEN" in r
    finally:
        await hol_stop(session=session)


async def test_state_at_broken_before_failure_shows_goals(tmp_path):
    """state_at BEFORE the broken tactic should still show goals normally."""
    test_file = tmp_path / "brokenTwoStepScript.sml"
    test_file.write_text(BROKEN_TWO_STEP_SCRIPT)
    session = "broken_before_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # Line 8 is at/before conj_tac (first tactic) — should work fine
        r = await hol_state_at(session=session, line=8, col=3)
        assert "PROOF BROKEN" not in r
        assert "Goal" in r
    finally:
        await hol_stop(session=session)


# Repro from GH issue #2: reverse + >- inside >> chain.
# This script is intentionally brittle in replay; state_at should still recover
# nearest valid prefix state instead of falling back to the original goal.
ISSUE2_REVERSE_SCRIPT = '''\
open HolKernel Parse boolLib bossLib arithmeticTheory;

val _ = new_theory "issue2";

Theorem foo:
  (!n. n < 5 ==> n + 1 <= 5) /\\ (!n. n < 10 ==> n * 2 < 20) /\\ (!n m. n + m = m + n)
Proof
  reverse conj_tac >- simp[] >>
  reverse conj_tac >- (
    rpt strip_tac >>
    cheat ) >>
  simp[]
QED

val _ = export_theory();
'''


async def test_state_at_reverse_modifier_recovers_nearest_prefix_state(tmp_path):
    """Regression for issue #2: broken prefix replay should recover best-effort goals.

    At the `cheat` line, prefix replay can fail deep in a compound tactic.
    We should back off to the nearest executable prefix and show that state,
    rather than the original theorem goal.
    """
    test_file = tmp_path / "issue2Script.sml"
    test_file.write_text(ISSUE2_REVERSE_SCRIPT)
    session = "issue2_reverse_test"

    # Find the line containing cheat in the test script
    cheat_line = next(
        i + 1 for i, line in enumerate(ISSUE2_REVERSE_SCRIPT.splitlines())
        if "cheat" in line
    )

    try:
        await hol_file_init(file=str(test_file), session=session)

        r = await hol_state_at(session=session, line=cheat_line, col=5)

        assert "Prefix replay failed" in r
        assert "using nearest valid prefix" in r
        # Recovered state should not be the original 3-way conjunction goal
        assert "n < 5" in r
        assert "n < 10" not in r
    finally:
        await hol_stop(session=session)


# =============================================================================
# Process Group Tests
# =============================================================================


async def test_kill_process_group_kills_children(tmp_path):
    """Test that _kill_process_group kills child processes, not just parent.

    This is a regression test for the holmake OOM issue where timeout killed
    only the parent Holmake process, leaving child buildheap processes as
    orphans that consumed 10-30GB RAM each.
    """
    # Create a script that spawns a child and sleeps
    script = tmp_path / "spawn_child.sh"
    script.write_text("""\
#!/bin/bash
# Spawn a child that also sleeps
sleep 300 &
CHILD_PID=$!
echo "CHILD_PID=$CHILD_PID"
# Parent also sleeps
sleep 300
""")
    script.chmod(0o755)

    # Start the process in its own session (like holmake does)
    proc = await asyncio.create_subprocess_exec(
        str(script),
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        start_new_session=True,
    )

    # Wait for child PID to be printed
    line = await asyncio.wait_for(proc.stdout.readline(), timeout=5.0)
    child_pid = int(line.decode().strip().split("=")[1])
    parent_pid = proc.pid

    # Verify both processes are running
    assert _pid_exists(parent_pid), "Parent should be running"
    assert _pid_exists(child_pid), "Child should be running"

    # Kill the process group
    await _kill_process_group(proc)

    # Give OS a moment to clean up
    await asyncio.sleep(0.1)

    # Verify BOTH are dead
    assert not _pid_exists(parent_pid), "Parent should be dead after killpg"
    assert not _pid_exists(child_pid), "Child should be dead after killpg"


async def test_kill_process_group_no_leak_on_none():
    """Test that _kill_process_group handles None gracefully."""
    # Should not raise
    await _kill_process_group(None)


async def test_kill_process_group_no_leak_on_exited(tmp_path):
    """Test that _kill_process_group handles already-exited process."""
    script = tmp_path / "exit_immediately.sh"
    script.write_text("#!/bin/bash\nexit 0\n")
    script.chmod(0o755)

    proc = await asyncio.create_subprocess_exec(
        str(script),
        start_new_session=True,
    )
    await proc.wait()  # Let it exit

    # Should not raise on already-exited process
    await _kill_process_group(proc)


def _pid_exists(pid: int) -> bool:
    """Check if a process with given PID exists."""
    try:
        os.kill(pid, 0)  # Signal 0 just checks existence
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True  # Process exists but we can't signal it


# =============================================================================
# CLI Tests
# =============================================================================


import subprocess


def test_parse_goals_json():
    """Test _parse_goals_json parses goals_json() output correctly."""
    from hol4_mcp.hol_cursor import FileProofCursor
    from hol4_mcp.hol_file_parser import HOLParseError

    # Create a minimal cursor just to test the parsing method
    class MockCursor(FileProofCursor):
        def __init__(self):
            pass  # Skip normal init

    cursor = MockCursor()

    # Empty goals
    assert cursor._parse_goals_json('{"ok":[]}\n') == []

    # New format with assumptions
    result = cursor._parse_goals_json('{"ok":[{"asms":["P","Q"],"goal":"R"}]}\n')
    assert result == [{"asms": ["P", "Q"], "goal": "R"}]

    # Multiple goals with assumptions
    result = cursor._parse_goals_json('{"ok":[{"asms":[],"goal":"A"},{"asms":["X"],"goal":"B"}]}\n')
    assert result == [{"asms": [], "goal": "A"}, {"asms": ["X"], "goal": "B"}]

    # Old format (just strings) for backwards compat
    result = cursor._parse_goals_json('{"ok":["A ⇒ A"]}\n')
    assert result == [{"asms": [], "goal": "A ⇒ A"}]

    # Error case - should raise exception
    with pytest.raises(HOLParseError, match="NO_PROOFS"):
        cursor._parse_goals_json('{"err":"NO_PROOFS"}\n')

    # With trailing val it = (): unit
    result = cursor._parse_goals_json('{"ok":[{"asms":[],"goal":"goal"}]}\nval it = (): unit\n')
    assert result == [{"asms": [], "goal": "goal"}]

    # Invalid JSON should raise exception
    with pytest.raises(HOLParseError):
        cursor._parse_goals_json('not json at all')


def test_cli_help():
    """Test that hol4-mcp --help works."""
    result = subprocess.run(
        ["hol4-mcp", "--help"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0
    assert "HOL4 MCP Server" in result.stdout
    # CLI uses subcommands - transport/port are in 'serve' subcommand
    assert "serve" in result.stdout
    assert "install-pi" in result.stdout


def test_cli_main_function():
    """Test the main() function can be imported and called with --help."""
    from hol4_mcp.hol_mcp_server import main
    import sys

    # Temporarily replace sys.argv
    old_argv = sys.argv
    try:
        sys.argv = ["hol4-mcp", "--help"]
        with pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0
    finally:
        sys.argv = old_argv


# =============================================================================
# Trace tests (hol_check_proof with trace=True)
# =============================================================================


async def test_check_proof_trace_ok(tmp_path):
    """trace=True on a passing proof shows per-step timing."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)
    session = "trace_ok_test"

    try:
        r = await hol_check_proof(
            theorem="add_zero", file=str(test_file), session=session, trace=True
        )
        assert "Status: OK" in r
        assert "Step 1" in r
        assert "ms" in r
        assert "Goals:" in r
    finally:
        await hol_stop(session=session)


async def test_check_proof_trace_false_omits_steps(tmp_path):
    """trace=False on a passing proof omits per-step detail."""
    test_file = tmp_path / "testScript.sml"
    shutil.copy(FIXTURES_DIR / "testScript.sml", test_file)
    session = "trace_false_test"

    try:
        r = await hol_check_proof(
            theorem="add_zero", file=str(test_file), session=session, trace=False
        )
        assert "Status: OK" in r
        assert "Step 1" not in r
    finally:
        await hol_stop(session=session)


async def test_check_proof_trace_failure(tmp_path):
    """trace=True on a failing proof shows steps up to failure."""
    test_file = tmp_path / "brokenTwoStepScript.sml"
    test_file.write_text(BROKEN_TWO_STEP_SCRIPT)
    session = "trace_fail_test"

    try:
        r = await hol_check_proof(
            theorem="broken_two_step", file=str(test_file), session=session, trace=True
        )
        assert "FAILED" in r or "INCOMPLETE" in r
        assert "Step 1" in r
        assert "Goals:" in r
    finally:
        await hol_stop(session=session)


async def test_check_proof_trace_multi_step(tmp_path):
    """trace=True on a multi-step proof shows all steps with goal transitions."""
    script = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "multi";

Theorem conj_swap:
  (A:bool) /\\ B ==> B /\\ A
Proof
  strip_tac >>
  conj_tac >- (fs[]) >>
  fs[]
QED

val _ = export_theory();
'''
    test_file = tmp_path / "multiScript.sml"
    test_file.write_text(script)
    session = "trace_multi_test"

    try:
        r = await hol_check_proof(
            theorem="conj_swap", file=str(test_file), session=session, trace=True
        )
        assert "Status: OK" in r
        assert "Step 1" in r
        # Should show goal count transitions
        assert "-> 0" in r  # final step resolves all goals
    finally:
        await hol_stop(session=session)


def test_session_idle_timeout_is_30_minutes():
    """Session idle timeout should be 30 minutes (1800s), not 2 hours."""
    assert _SESSION_IDLE_TIMEOUT == 1800


# --- Tests for absolute line/col reporting ---

def test_file_offset_to_line_col_basic():
    """_file_offset_to_line_col converts byte offset to 1-indexed (line, col)."""
    content = "abc\ndef\nghi"
    # offset 0 = 'a' -> line 1, col 1
    assert _file_offset_to_line_col(0, content) == (1, 1)
    # offset 3 = '\n' -> line 1, col 4
    assert _file_offset_to_line_col(3, content) == (1, 4)
    # offset 4 = 'd' -> line 2, col 1
    assert _file_offset_to_line_col(4, content) == (2, 1)
    # offset 7 = '\n' -> line 2, col 4
    assert _file_offset_to_line_col(7, content) == (2, 4)
    # offset 8 = 'g' -> line 3, col 1
    assert _file_offset_to_line_col(8, content) == (3, 1)


def test_file_offset_to_line_col_first_char():
    """Edge case: offset 0 with no preceding newline."""
    assert _file_offset_to_line_col(0, "x") == (1, 1)


# Script with blank line between Proof and first tactic
BLANK_LINE_AFTER_PROOF_SCRIPT = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "blankline";

Theorem first_thm:
  T
Proof
  simp[]
QED

Theorem second_thm:
  !a b. a /\\ b ==> b /\\ a
Proof

  rpt strip_tac >>
  simp[bad_theorem] >>
  decide_tac
QED

val _ = export_theory();
'''

# Script without blank line after Proof (normal case)
NORMAL_PROOF_SCRIPT = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "normalproof";

Theorem first_thm:
  T
Proof
  simp[]
QED

Theorem second_thm:
  !a b. a /\\ b ==> b /\\ a
Proof
  rpt strip_tac >>
  simp[bad_theorem] >>
  decide_tac
QED

val _ = export_theory();
'''


@pytest.mark.asyncio
async def test_check_proof_absolute_lines_with_blank_line(tmp_path):
    """hol_check_proof reports absolute file line numbers even when
    there's a blank line between Proof and the first tactic.

    File layout (BLANK_LINE_AFTER_PROOF_SCRIPT):
      Line 13: Proof
      Line 14: (blank)
      Line 15: "  rpt strip_tac >>"   <- first tactic
      Line 16: "  simp[bad_theorem] >>"
    """
    test_file = tmp_path / "blanklineScript.sml"
    test_file.write_text(BLANK_LINE_AFTER_PROOF_SCRIPT)
    session = "abs_line_blank_test"

    try:
        r = await hol_check_proof(
            theorem="second_thm", file=str(test_file), session=session, trace=True
        )
        assert "FAILED" in r
        # First tactic is at line 15 (after blank line 14), NOT line 14
        assert "line/col 15:" in r, f"Expected line 15 (first tactic), got: {r}"
        # The suggested hol_state_at line must also be absolute
        assert "hol_state_at(line=15" in r, f"Suggested line should be 15: {r}"
    finally:
        await hol_stop(session=session)


@pytest.mark.asyncio
async def test_check_proof_absolute_lines_normal(tmp_path):
    """hol_check_proof reports absolute file line numbers (no blank line case).

    File layout (NORMAL_PROOF_SCRIPT):
      Line 13: Proof
      Line 14: "  rpt strip_tac >>"   <- first tactic
      Line 15: "  simp[bad_theorem] >>"
    """
    test_file = tmp_path / "normalproofScript.sml"
    test_file.write_text(NORMAL_PROOF_SCRIPT)
    session = "abs_line_normal_test"

    try:
        r = await hol_check_proof(
            theorem="second_thm", file=str(test_file), session=session, trace=True
        )
        assert "FAILED" in r
        # First tactic at line 14 (right after Proof on line 13)
        assert "line/col 14:" in r, f"Expected line 14, got: {r}"
        assert "hol_state_at(line=14" in r, f"Suggested line should be 14: {r}"
    finally:
        await hol_stop(session=session)


@pytest.mark.asyncio
async def test_check_proof_absolute_columns(tmp_path):
    """hol_check_proof columns are absolute in the file, not relative to proof body.

    "  rpt strip_tac" is indented 2 spaces -> col 3 (1-indexed).
    """
    test_file = tmp_path / "normalproofScript.sml"
    test_file.write_text(NORMAL_PROOF_SCRIPT)
    session = "abs_col_test"

    try:
        r = await hol_check_proof(
            theorem="second_thm", file=str(test_file), session=session, trace=True
        )
        # "  rpt strip_tac" starts at col 3 (2 spaces + 'r')
        # Must NOT be col 1 (which would mean relative to stripped proof_body)
        assert "14:3" in r, f"Expected col 3 for indented tactic, got: {r}"
    finally:
        await hol_stop(session=session)


@pytest.mark.asyncio
async def test_state_at_absolute_lines_with_blank_line(tmp_path):
    """hol_state_at reports absolute line numbers with blank line after Proof.

    File layout (BLANK_LINE_AFTER_PROOF_SCRIPT):
      Line 13: Proof
      Line 14: (blank)
      Line 15: "  rpt strip_tac >>"
      Line 18: QED
    """
    test_file = tmp_path / "blanklineScript.sml"
    test_file.write_text(BLANK_LINE_AFTER_PROOF_SCRIPT)
    session = "abs_line_state_at_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # Request state at QED line (line 18). Proof is broken, so PROOF BROKEN.
        r = await hol_state_at(session=session, line=18, col=1)
        assert "PROOF BROKEN" in r
        # The failure location must be line 15 (rpt strip_tac), not line 14 (blank)
        assert "line 15" in r, f"Expected failure at line 15, got: {r}"
        assert "hol_state_at(line=15" in r, f"Suggested line should be 15: {r}"
    finally:
        await hol_stop(session=session)


# Script where the FIRST tactic fails (exercises tactic_to_loc(0) fallback)
FIRST_TAC_FAILS_BLANK_LINE_SCRIPT = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "firstfail";

Theorem first_tac_fails:
  !a b. a /\\ b ==> b /\\ a
Proof

  FAIL_TAC "boom" >>
  simp[]
QED

val _ = export_theory();
'''


@pytest.mark.asyncio
async def test_state_at_first_tac_fails_blank_line(tmp_path):
    """tactic_to_loc(0) uses proof_body_offset when first tactic fails.

    File layout:
      Line 7: Proof
      Line 8: (blank)
      Line 9: "  FAIL_TAC \\"boom\\" >>"  <- first tactic (fails)
      Line 11: QED
    """
    test_file = tmp_path / "firstfailScript.sml"
    test_file.write_text(FIRST_TAC_FAILS_BLANK_LINE_SCRIPT)
    session = "first_tac_fail_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # Request state at QED line. First tactic fails → PROOF BROKEN.
        r = await hol_state_at(session=session, line=11, col=1)
        assert "PROOF BROKEN" in r
        # Failure at line 9 (FAIL_TAC), not line 8 (blank after Proof)
        assert "line 9" in r, f"Expected failure at line 9, got: {r}"
        assert "hol_state_at(line=9" in r, f"Suggested line should be 9: {r}"
    finally:
        await hol_stop(session=session)


# --- Tests for `by` clause substep pinpointing ---

BY_SUBSTEP_SCRIPT = '''\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "by_substep";

Theorem by_tac_fails:
  T /\\ T
Proof
  `T` by FAIL_TAC "boom" >>
  simp[]
QED

val _ = export_theory();
'''


@pytest.mark.asyncio
async def test_by_substep_pinpoints_tactic_failure(tmp_path):
    """When `by` tactic fails, substep pinpointing identifies the tactic (not sg).

    `T` by FAIL_TAC "boom" → sg succeeds, FAIL_TAC fails.
    find_failing_substep should report substep 2/2 (the tactic), not 1/2 (sg).
    """
    test_file = tmp_path / "by_substepScript.sml"
    test_file.write_text(BY_SUBSTEP_SCRIPT)
    session = "by_substep_test"

    try:
        r = await hol_check_proof(
            theorem="by_tac_fails", file=str(test_file), session=session, trace=False
        )
        assert "FAILED" in r
        # Must identify the tactic as the failing part, not sg
        assert "Failing substep 2/2" in r, f"Expected substep 2/2 (tactic), got: {r}"
        assert "FAIL_TAC" in r, f"Should mention FAIL_TAC: {r}"
    finally:
        await hol_stop(session=session)
