"""Tests for proof verification (hol_file_status, verify_all_proofs)."""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import FileProofCursor, _format_context_error
from hol4_mcp.hol_session import HOLSession


SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session_tmpdir(tmp_path):
    """Create a HOL session with tmp_path as workdir."""
    session = HOLSession(str(tmp_path))
    await session.start()
    # Load tactic_prefix.sml which defines timing functions
    await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
    yield session
    await session.stop()


@pytest.mark.asyncio
async def test_verify_detects_incomplete_proof(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verify_all_proofs detects incomplete proofs (goals_after != 0)."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem incomplete_proof:
  !x:num. x < x + 1 /\\ x < x + 2
Proof
  strip_tac
QED
""")
    # strip_tac removes the quantifier but leaves conjuncts unsolved
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    assert "incomplete_proof" in results
    trace = results["incomplete_proof"]
    assert len(trace) > 0
    # Should have goals remaining (incomplete) - proof not finished
    final = trace[-1]
    assert final.goals_after != 0, f"Expected incomplete proof, got goals_after={final.goals_after}"


@pytest.mark.asyncio
async def test_verify_detects_tactic_error(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verify_all_proofs detects tactic errors."""
    script = tmp_path / "testScript.sml"
    # Use a tactic that will definitely error
    script.write_text("""
Theorem bad_tactic:
  T
Proof
  ACCEPT_TAC (ASSUME ``F``)
QED
""")
    # ACCEPT_TAC with wrong theorem type should fail
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    assert "bad_tactic" in results
    trace = results["bad_tactic"]
    assert len(trace) > 0
    # Should either have error or incomplete (goals remaining)
    final = trace[-1]
    assert final.error is not None or final.goals_after != 0


@pytest.mark.asyncio
async def test_verify_complete_proof_succeeds(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verify_all_proofs correctly identifies complete proofs."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem complete_proof:
  T
Proof
  simp[]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    assert "complete_proof" in results
    trace = results["complete_proof"]
    assert len(trace) > 0
    final = trace[-1]
    # Should complete with no goals and no error
    assert final.goals_after == 0
    assert final.error is None


@pytest.mark.asyncio
async def test_verify_stores_theorem_for_next(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that verified theorems are stored so subsequent proofs can use them."""
    script = tmp_path / "testScript.sml"
    # Use MATCH_MP_TAC which works with implication theorems
    script.write_text("""
Theorem first_thm:
  !x. x ==> x
Proof
  simp[]
QED

Theorem uses_first:
  T ==> T
Proof
  MATCH_MP_TAC first_thm >> simp[]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # First should succeed
    first_trace = results["first_thm"]
    assert len(first_trace) > 0
    assert first_trace[-1].goals_after == 0
    assert first_trace[-1].error is None
    
    # Second should also succeed (can use first_thm)
    uses_trace = results["uses_first"]
    assert len(uses_trace) > 0
    # Either completes or at least doesn't error on first_thm reference
    assert uses_trace[-1].goals_after == 0 or uses_trace[-1].error is None


@pytest.mark.asyncio
async def test_verify_failed_theorem_not_stored(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that failed theorems are not stored (no QED on error)."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem broken:
  F
Proof
  simp[]
QED

Theorem tries_to_use_broken:
  !x. x ==> x
Proof
  MATCH_MP_TAC broken
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # First should fail (ALL_TAC leaves goal unchanged)
    broken_trace = results["broken"]
    assert broken_trace[-1].goals_after != 0, "broken proof should be incomplete"
    
    # Second should fail because broken wasn't stored (or MATCH_MP_TAC fails)
    uses_trace = results["tries_to_use_broken"]
    # Either errors (broken not found) or doesn't complete
    assert uses_trace[-1].error is not None or uses_trace[-1].goals_after != 0


@pytest.mark.asyncio
async def test_verify_cheats_skipped(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that cheat theorems are loaded but not verified."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Theorem has_cheat:
  F
Proof
  cheat
QED

Theorem after_cheat:
  T
Proof
  simp[]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # Cheat theorem should have empty trace
    assert results["has_cheat"] == []
    
    # Following theorem should still work
    assert results["after_cheat"][-1].goals_after == 0


@pytest.mark.asyncio
async def test_verify_loads_definitions_between_theorems(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that definitions between theorems are loaded."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Definition my_true_def:
  my_true = T
End

Theorem uses_def:
  my_true
Proof
  simp[my_true_def]
QED
""")
    
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    
    results = await cursor.verify_all_proofs()
    
    # Should succeed using the definition
    trace = results["uses_def"]
    assert len(trace) > 0
    assert trace[-1].goals_after == 0
    assert trace[-1].error is None


@pytest.mark.asyncio
async def test_loads_content_immediately_after_qed(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Regression: val bindings and Definitions on lines right after QED must be loaded.

    _load_remaining_content and _load_context_to_line had an off-by-one that
    skipped lines immediately following each theorem's QED.

    Tests both "before first theorem" and "between theorems" positions for both
    val bindings and Definition blocks.
    """
    script = tmp_path / "testScript.sml"
    script.write_text("""\
val pre_val = TRUTH;
Definition pre_def:
  pre_const = T
End
Theorem first_thm:
  pre_const
Proof
  simp[pre_def]
QED
val post_val = TRUTH;
Definition post_def:
  post_const = T
End
Theorem uses_post_qed_content:
  post_const
Proof
  simp[post_def]
QED
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # state_at on the second theorem should work (needs post_def loaded via init)
    result = await cursor.state_at(line=17, col=1)
    assert result.error is None, f"state_at failed: {result.error}"

    # verify_all_proofs should also succeed for both theorems
    results = await cursor.verify_all_proofs()

    trace1 = results["first_thm"]
    assert len(trace1) > 0
    assert trace1[-1].goals_after == 0, "first_thm proof failed (pre-theorem content not loaded)"
    assert trace1[-1].error is None

    trace2 = results["uses_post_qed_content"]
    assert len(trace2) > 0
    assert trace2[-1].goals_after == 0, "post-QED content not loaded (Definition/val after QED skipped)"
    assert trace2[-1].error is None


@pytest.mark.asyncio
async def test_fatal_pre_theorem_load_error(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Regression: fatal pre-theorem load errors must be reported (not silently advance loaded_to_line).

    With lazy loading, init() succeeds but the error surfaces when entering a theorem.
    """
    script = tmp_path / "testScript.sml"
    script.write_text("""\
open definitelyMissingTheory;

Definition pre_def:
  pre_const = T
End

Theorem uses_pre_def:
  pre_const
Proof
  simp[pre_def]
QED
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    result = await cursor.init()

    # init() succeeds with lazy loading — error surfaces on enter_theorem
    assert "error" not in result

    result = await cursor.enter_theorem("uses_pre_def")
    assert "error" in result
    assert "Missing dependency:" in result["error"]


@pytest.mark.asyncio
async def test_missing_file_load_statement(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Regression: `load "..."` missing-file errors must be treated as fatal context failures.

    With lazy loading, init() succeeds but the error surfaces on enter_theorem.
    """
    script = tmp_path / "testScript.sml"
    script.write_text("""\
load "definitely_missing";

Theorem t:
  T
Proof
  simp[]
QED
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    result = await cursor.init()

    # init() succeeds with lazy loading
    assert "error" not in result

    result = await cursor.enter_theorem("t")
    assert "error" in result
    assert "Missing dependency file:" in result["error"]
    assert "definitely_missing.ui" in result["error"]


def test_format_context_error_timeout_message():
    """Timeout message should mention file content, not just 'loading context'."""
    msg = _format_context_error("TIMEOUT after 60s")
    assert "file content" in msg.lower() or "definition or proof" in msg.lower()
    assert "Hint:" in msg


def test_format_context_error_includes_env_var_recovery_steps():
    output = '''
error in load stableswapDefsTheory : Fail "Cannot find file $(VFMDIR)/spec/prop/vfmComputeTheory.ui"
Exception- Fail "Cannot find file $(VFMDIR)/spec/prop/vfmComputeTheory.ui" raised
'''
    msg = _format_context_error(output)

    assert "Missing dependency file:" in msg
    assert "$(VFMDIR)" in msg
    assert "holmake(workdir=..., env={\"VFMDIR\": \"/abs/path\"})" in msg
    assert "hol_setenv(env={\"VFMDIR\": \"/abs/path\"})" in msg
    assert "hol_restart(session=...)" in msg


def test_format_context_error_structure_fallback_mentions_env_vars():
    output = "poly: : error: Structure (fooTheory) has not been declared\nStatic Errors"
    msg = _format_context_error(output)

    assert "Missing dependency: fooTheory" in msg
    assert "hol_setenv" in msg


def test_format_context_error_value_constructor_forward_ref_hint():
    output = (
        "/tmp/fwdNameScript.sml:11: error: Value or constructor (later) has not been declared "
        "Found near later\n"
        "error in quse /tmp/fwdNameScript.sml : Fail \"Static Errors\""
    )
    msg = _format_context_error(output)

    assert "Unknown identifier: later" in msg
    assert "line 11" in msg
    assert "forward reference" in msg
    assert "hol_check_proof" in msg


# =============================================================================
# Definition ... Termination ... End
# =============================================================================


@pytest.mark.asyncio
async def test_definition_termination_state_at(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test that state_at works for Definition ... Termination ... End blocks."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Definition fact_def:
  fact (n:num) = if n = 0 then 1 else n * fact (n - 1)
Termination
  WF_REL_TAC `measure I`
End
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # state_at before tactic: should show TC goal
    # (TC goal is extracted lazily when entering the theorem)
    result = await cursor.state_at(4, col=1)  # Termination line

    # TC goal should have been extracted during lazy load
    assert "fact_def" in cursor._tc_goals
    assert "WF" in cursor._tc_goals["fact_def"]
    assert not result.error or "no goals" in (result.error or "")
    assert result.tactics_total >= 1

    # state_at after tactic: should be complete
    result = await cursor.state_at(6, col=1)  # End line
    # Either goals is empty or error says "no goals" (proof complete)
    assert not result.goals or "no goals" in (result.error or "")


@pytest.mark.asyncio
async def test_definition_termination_verify_all(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test verify_all_proofs with Definition blocks."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Definition fact_def:
  fact (n:num) = if n = 0 then 1 else n * fact (n - 1)
Termination
  WF_REL_TAC `measure I`
End

Theorem fact_0:
  fact 0 = 1
Proof
  simp[Once fact_def]
QED
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    results = await cursor.verify_all_proofs()

    # Definition block: timed via TC goal
    assert "fact_def" in results
    fact_trace = results["fact_def"]
    assert len(fact_trace) > 0
    # First (and only) step should have completed the proof
    assert fact_trace[0].goals_before > 0
    assert fact_trace[0].goals_after == 0

    # Theorem using definition should succeed
    assert "fact_0" in results
    trace = results["fact_0"]
    assert len(trace) > 0
    assert trace[-1].goals_after == 0  # proof complete


@pytest.mark.asyncio
async def test_definition_termination_trace(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test execute_proof_traced works for Definition termination proofs."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Definition fact_def:
  fact (n:num) = if n = 0 then 1 else n * fact (n - 1)
Termination
  WF_REL_TAC `measure I`
End
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    trace = await cursor.execute_proof_traced("fact_def")
    assert len(trace) > 0
    assert trace[0].real_ms >= 0
    assert trace[0].goals_before > 0
    assert trace[0].goals_after == 0


@pytest.mark.asyncio
async def test_definition_termination_wrong_tactic(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test state_at shows TC goal when termination tactic is wrong."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Definition bad_def:
  bad_fn (n:num) = if n = 0 then 1 else n * bad_fn (n - 1)
Termination
  simp[]
End
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # Before the wrong tactic: should show TC goal with WF
    result = await cursor.state_at(4, col=1)  # Termination line
    assert result.goals, "Should have goals before tactic"
    tc_goal = result.goals[0]["goal"]
    assert "WF" in tc_goal, f"TC goal should mention WF, got: {tc_goal}"

    # After the wrong tactic: simp[] doesn't solve TCs, goal should remain
    result = await cursor.state_at(6, col=1)  # End line
    # simp[] on TC goal doesn't fail but also doesn't solve it
    assert result.goals, "Should still have goals after wrong tactic"


@pytest.mark.asyncio
async def test_definition_termination_incomplete(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Test state_at with incomplete termination proof (cheat)."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
Definition cheat_def:
  cheat_fn (n:num) (m:num) =
    if n = 0 then m else cheat_fn (n - 1) (m + 1)
Termination
  WF_REL_TAC `measure FST` >>
  cheat
End

Theorem uses_cheat:
  cheat_fn 0 5 = 5
Proof
  simp[Once cheat_def]
QED
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # Before tactic: TC goal should be shown
    result = await cursor.state_at(5, col=1)  # Termination line
    assert result.goals
    assert "WF" in result.goals[0]["goal"]

    # Theorem referencing cheated definition should still work
    # (HOL processes the full Definition block including cheat)
    result = await cursor.state_at(12, col=1)  # Inside uses_cheat proof
    assert result.tactics_total >= 1


# ===========================================================================
# Cascade prevention: cheat failed proofs during loading
# ===========================================================================

CASCADE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;
val _ = new_theory "testCascade";

Theorem thm_a:
  T ==> T
Proof
  strip_tac
QED

Theorem thm_b:
  T /\\ T
Proof
  FAIL_TAC "intentional"
QED

Theorem thm_c:
  T ==> T /\\ T
Proof
  strip_tac >> ACCEPT_TAC thm_b
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_cascade_prevented_init(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """T1: Init succeeds despite broken proof; cascade prevented by auto-cheat.

    With lazy loading, failed proofs are detected when loading context for
    a later theorem (not during init).
    """
    script = tmp_path / "testCascadeScript.sml"
    script.write_text(CASCADE_SCRIPT)
    cursor = FileProofCursor(script, hol_session_tmpdir)
    result = await cursor.init()

    # Init should succeed (no error), all 3 theorems found
    assert "error" not in result
    assert len(result["theorems"]) == 3

    # Trigger lazy load by entering thm_c (loads thm_a and thm_b as context)
    enter_result = await cursor.enter_theorem("thm_c")
    assert "error" not in enter_result

    # thm_b should be in _failed_proofs and marked proof_failed in status
    assert "thm_b" in cursor._failed_proofs
    status = cursor.status
    thm_b_status = next(t for t in status["theorems"] if t["name"] == "thm_b")
    assert thm_b_status.get("proof_failed") is True

    # thm_a should NOT be marked proof_failed
    thm_a_status = next(t for t in status["theorems"] if t["name"] == "thm_a")
    assert "proof_failed" not in thm_a_status

    # thm_c should NOT be marked proof_failed (its proof uses the cheated thm_b)
    thm_c_status = next(t for t in status["theorems"] if t["name"] == "thm_c")
    assert "proof_failed" not in thm_c_status


@pytest.mark.asyncio
async def test_state_at_after_cheated_theorem(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """T3: state_at works on theorem after a cheated one."""
    script = tmp_path / "testCascadeScript.sml"
    script.write_text(CASCADE_SCRIPT)
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # state_at on thm_c should work - it uses thm_b which was cheated to TRUTH
    result = await cursor.state_at(19, col=1)  # "strip_tac >> ACCEPT_TAC thm_b"
    assert result.error is None, f"state_at failed: {result.error}"
    assert result.tactics_total >= 1


@pytest.mark.asyncio
async def test_enter_theorem_after_cheated(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """T4: enter_theorem loads context with cheated intermediate theorem."""
    script = tmp_path / "testCascadeScript.sml"
    script.write_text(CASCADE_SCRIPT)
    # Use a fresh cursor — don't call init first, to test _load_context_to_line
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # Entering thm_c should work - it triggers _load_context_to_line
    # which must cheat thm_b to proceed
    result = await cursor.enter_theorem("thm_c")
    assert "error" not in result, f"enter_theorem failed: {result.get('error')}"
    assert result["theorem"] == "thm_c"
    assert result["tactics"] >= 1


@pytest.mark.asyncio
async def test_failed_proofs_cleared_on_header_change(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """T5: _failed_proofs cleared when pre-theorem content changes (triggers reinit)."""
    script = tmp_path / "testCascadeScript.sml"
    script.write_text(CASCADE_SCRIPT)
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # Trigger lazy load to populate _failed_proofs
    await cursor.enter_theorem("thm_c")

    # Verify thm_b is in failed_proofs after lazy load
    assert "thm_b" in cursor._failed_proofs

    # Change pre-theorem content (triggers full session reinit path)
    fixed_script = CASCADE_SCRIPT.replace(
        'val _ = new_theory "testCascade";',
        'val _ = new_theory "testCascade";\n(* changed *)',
    )
    script.write_text(fixed_script)

    # status() triggers reparse; pre-theorem change clears _failed_proofs
    status = cursor.status
    assert "thm_b" not in cursor._failed_proofs


@pytest.mark.asyncio
async def test_cascade_multiple_failures(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Multiple broken proofs should all be cheated; later theorems still load."""
    script = tmp_path / "testMultiFailScript.sml"
    script.write_text("""\
open HolKernel Parse boolLib bossLib;
val _ = new_theory "testMultiFail";

Theorem ok1:
  T ==> T
Proof
  strip_tac
QED

Theorem fail1:
  T /\\ T
Proof
  FAIL_TAC "fail1"
QED

Theorem fail2:
  T
Proof
  FAIL_TAC "fail2"
QED

Theorem ok2:
  T ==> T /\\ T
Proof
  strip_tac >> ACCEPT_TAC fail1
QED

val _ = export_theory();
""")
    cursor = FileProofCursor(script, hol_session_tmpdir)
    result = await cursor.init()

    assert "error" not in result
    assert len(result["theorems"]) == 4

    # Trigger lazy load by entering ok2 (loads fail1, fail2 as context)
    enter_result = await cursor.enter_theorem("ok2")
    assert "error" not in enter_result

    assert cursor._failed_proofs == {"fail1", "fail2"}

    # ok2 references fail1 (cheated to TRUTH) — should still load
    status = cursor.status
    ok2_status = next(t for t in status["theorems"] if t["name"] == "ok2")
    assert "proof_failed" not in ok2_status


@pytest.mark.asyncio
async def test_definition_failure_reported_clearly(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """T6: Failed Definition is reported as error, not silently swallowed.

    Definitions create constants + def/ind theorems as a unit.
    They can't be cheated. A failed Definition should produce a clear error.
    """
    script = tmp_path / "testDefFailScript.sml"
    script.write_text("""\
open HolKernel Parse boolLib bossLib;
val _ = new_theory "testDefFail";

Definition bad_def:
  bad (n:num) = bad n + 1
Termination
  FAIL_TAC "broken"
End

Theorem uses_bad:
  bad 0 = 1
Proof
  simp[Once bad_def]
QED

val _ = export_theory();
""")
    cursor = FileProofCursor(script, hol_session_tmpdir)
    result = await cursor.init()

    # init() succeeds with lazy loading — error surfaces on enter_theorem
    assert "error" not in result

    result = await cursor.enter_theorem("uses_bad")
    assert "error" in result
    assert "bad_def" in result["error"]
    # Definition should NOT be in _failed_proofs (not cheated)
    assert "bad_def" not in cursor._failed_proofs


@pytest.mark.asyncio
async def test_verify_all_proofs_cascade(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """T7: verify_all_proofs cheats failed proofs to prevent cascade."""
    script = tmp_path / "testVerifyCascadeScript.sml"
    script.write_text("""\
open HolKernel Parse boolLib bossLib;
val _ = new_theory "testVerifyCascade";

Theorem good_a:
  T ==> T
Proof
  strip_tac
QED

Theorem broken_b:
  T /\\ T
Proof
  FAIL_TAC "intentional"
QED

Theorem uses_b:
  T
Proof
  metis_tac[broken_b]
QED

val _ = export_theory();
""")
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    results = await cursor.verify_all_proofs()

    # All 3 theorems should have results (no crash from cascade)
    assert len(results) == 3, f"Expected 3, got {list(results.keys())}"

    # good_a should verify cleanly
    assert results["good_a"]
    assert not any(e.error for e in results["good_a"])

    # broken_b should have an error in its trace
    assert results["broken_b"]
    assert any(e.error for e in results["broken_b"])

    # uses_b should succeed — broken_b cheated, metis_tac[broken_b] works
    assert "uses_b" in results
    assert results["uses_b"]
    assert not any(e.error for e in results["uses_b"]), \
        f"uses_b should succeed: {[e.error for e in results['uses_b']]}"


@pytest.mark.asyncio
async def test_verify_all_proofs_incomplete_cheated(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """verify_all_proofs cheats incomplete proofs (goals remain) too."""
    script = tmp_path / "testVerifyIncompleteScript.sml"
    script.write_text("""\
open HolKernel Parse boolLib bossLib;
val _ = new_theory "testVerifyIncomplete";

Theorem incomplete_b:
  T /\\ T
Proof
  conj_tac
QED

Theorem uses_incomplete:
  T ==> T /\\ T
Proof
  strip_tac >> ACCEPT_TAC incomplete_b
QED

val _ = export_theory();
""")
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    results = await cursor.verify_all_proofs()

    # Both theorems should have results
    assert len(results) == 2, f"Expected 2, got {list(results.keys())}"
    assert "uses_incomplete" in results


# =============================================================================
# Resume/Finalise tests
# =============================================================================

RESUME_SCRIPT = """\
open HolKernel Parse boolLib bossLib markerLib;
val _ = new_theory "testResume";

Theorem split_conj:
  p /\\ (p ==> q) ==> p /\\ q
Proof
  strip_tac >> conj_tac
  >- suspend "p_case"
  >- suspend "q_case"
QED

Resume split_conj[p_case]:
  ASM_REWRITE_TAC[]
QED

Resume split_conj[q_case]:
  RES_TAC
QED

Finalise split_conj

Theorem after_resume:
  T
Proof
  simp[]
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_resume_init_lists_blocks(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """init() should list Resume blocks alongside regular theorems."""
    script = tmp_path / "testResumeScript.sml"
    script.write_text(RESUME_SCRIPT)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    result = await cursor.init()

    names = [t['name'] for t in result['theorems']]
    assert "split_conj" in names
    assert "split_conj[p_case]" in names
    assert "split_conj[q_case]" in names
    assert "after_resume" in names
    assert not result.get('error'), f"init error: {result.get('error')}"


@pytest.mark.asyncio
async def test_resume_state_at(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """state_at should navigate into Resume blocks and show goals."""
    script = tmp_path / "testResumeScript.sml"
    script.write_text(RESUME_SCRIPT)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # Find the p_case Resume block
    thm = cursor._get_theorem("split_conj[p_case]")
    assert thm is not None, "split_conj[p_case] should exist"

    # Navigate to the proof start (should show the suspended goal)
    result = await cursor.state_at(thm.proof_start_line, 1)
    assert result.goals, f"Expected goals, got error: {result.error}"
    # The goal should be related to p (the suspended subgoal)
    goal_text = result.goals[0].get('goal', '')
    assert goal_text, f"Expected non-empty goal, goals={result.goals}"


@pytest.mark.asyncio
async def test_resume_state_at_after_tactics(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """state_at at QED line should show proof complete (no goals)."""
    script = tmp_path / "testResumeScript.sml"
    script.write_text(RESUME_SCRIPT)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    thm = cursor._get_theorem("split_conj[p_case]")
    assert thm is not None

    # Navigate to QED line — should have all tactics replayed
    qed_line = thm.proof_end_line - 1
    result = await cursor.state_at(qed_line, 1)
    # "no goals" error from goals_json means proof completed
    no_goals_ok = result.error and "no goals" in result.error.lower()
    assert len(result.goals) == 0 or no_goals_ok, \
        f"Expected proof complete at QED, got {len(result.goals)} goals, error={result.error}"


@pytest.mark.asyncio
async def test_resume_enter_theorem_shows_goal(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """enter_theorem on a Resume block should show the suspended goal."""
    script = tmp_path / "testResumeScript.sml"
    script.write_text(RESUME_SCRIPT)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    result = await cursor.enter_theorem("split_conj[p_case]")
    assert "error" not in result, f"enter_theorem error: {result.get('error')}"
    assert result.get('goal'), "Goal should be non-empty for Resume block"
    assert result.get('tactics', 0) > 0, "Should have at least one tactic"


@pytest.mark.asyncio
async def test_resume_check_proof(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """execute_proof_traced on a Resume block should return timing trace."""
    script = tmp_path / "testResumeScript.sml"
    script.write_text(RESUME_SCRIPT)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    trace = await cursor.execute_proof_traced("split_conj[p_case]")
    assert trace, "Should have trace entries for Resume block"
    assert not any(e.error for e in trace), \
        f"No errors expected: {[e.error for e in trace if e.error]}"


@pytest.mark.asyncio
async def test_resume_verify_all_proofs(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """verify_all_proofs should handle Resume blocks."""
    script = tmp_path / "testResumeScript.sml"
    script.write_text(RESUME_SCRIPT)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    results = await cursor.verify_all_proofs()

    # Should have results for all theorems including Resume blocks
    assert "split_conj" in results
    assert "split_conj[p_case]" in results
    assert "split_conj[q_case]" in results
    assert "after_resume" in results

    # Resume proofs should succeed (no errors)
    for name in ["split_conj[p_case]", "split_conj[q_case]"]:
        trace = results[name]
        if trace:
            errors = [e.error for e in trace if e.error]
            assert not errors, f"{name} has errors: {errors}"


@pytest.mark.asyncio
async def test_resume_file_status(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """Cursor status should list Resume blocks."""
    script = tmp_path / "testResumeScript.sml"
    script.write_text(RESUME_SCRIPT)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    status = cursor.status
    names = [t['name'] for t in status['theorems']]
    assert "split_conj[p_case]" in names
    assert "split_conj[q_case]" in names


@pytest.mark.asyncio
async def test_resume_failed_proof_cheated(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """A Resume with a failing tactic (runtime fail) should be cheated."""
    script = tmp_path / "testResumeBadScript.sml"
    # Use a real tactic that fails (ACCEPT_TAC TRUTH doesn't solve "p")
    script.write_text("""\
open HolKernel Parse boolLib bossLib markerLib;
val _ = new_theory "testResumeBad";

Theorem split_conj:
  p /\\ (p ==> q) ==> p /\\ q
Proof
  strip_tac >> conj_tac
  >- suspend "p_case"
  >- suspend "q_case"
QED

Resume split_conj[p_case]:
  ACCEPT_TAC TRUTH
QED

Resume split_conj[q_case]:
  RES_TAC
QED

Finalise split_conj

Theorem still_works:
  T
Proof
  simp[]
QED

val _ = export_theory();
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    result = await cursor.init()

    # Init should succeed (failed Resume cheated)
    assert not result.get('error'), f"init error: {result.get('error')}"

    # The after-resume theorem should be accessible
    names = [t['name'] for t in result['theorems']]
    assert "still_works" in names


@pytest.mark.asyncio
async def test_resume_state_at_after_edit(hol_session_tmpdir: HOLSession, tmp_path: Path):
    """state_at on Resume block should work after editing the proof body (issue #10)."""
    script = tmp_path / "testSuspendScript.sml"
    script.write_text("""\
open HolKernel Parse boolLib bossLib markerLib;
val _ = new_theory "testSuspend";

Theorem foo:
  (!n. n + 0 = n) /\\ (!n. 0 + n = n)
Proof
  conj_tac >- suspend "case1"
  >> simp[]
QED

Resume foo[case1]:
  simp[]
QED

Finalise foo

val _ = export_theory();
""")

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # Step 1: Navigate into the Resume block — should work
    thm = cursor._get_theorem("foo[case1]")
    assert thm is not None
    result1 = await cursor.state_at(thm.proof_start_line, 1)
    assert not result1.error or "no goals" in result1.error.lower(), \
        f"First state_at failed: {result1.error}"

    # Step 2: Edit the Resume proof body
    script.write_text("""\
open HolKernel Parse boolLib bossLib markerLib;
val _ = new_theory "testSuspend";

Theorem foo:
  (!n. n + 0 = n) /\\ (!n. 0 + n = n)
Proof
  conj_tac >- suspend "case1"
  >> simp[]
QED

Resume foo[case1]:
  rw[] >> simp[]
QED

Finalise foo

val _ = export_theory();
""")

    # Step 3: Navigate into the same Resume block after edit — should NOT fail
    thm2 = cursor._get_theorem_at_position(thm.proof_start_line)
    # Re-fetch after reparse (state_at will trigger reparse)
    result2 = await cursor.state_at(thm.proof_start_line, 1)
    assert not result2.error or "no goals" in result2.error.lower(), \
        f"state_at after edit failed: {result2.error}"
