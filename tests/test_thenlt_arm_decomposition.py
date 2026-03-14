"""Acceptance tests for >- arm decomposition in step_plan.

After the parent task (ThenLT base decomposition), the >- suffix is still
ONE atomic step: elt(ALL_LT >- arm1 >- arm2). This task decomposes each
>- arm into its own e() step, giving per-arm navigation.

Semantic foundation:
  >- = THEN1: each arm MUST completely solve the first goal.
  After base creates N goals, e(arm1); e(arm2); ... is equivalent to
  elt(ALL_LT >- arm1 >- arm2 ...) because no subgoals leak between arms.

  Exception: >| (THENL) arms can produce subgoals, so must stay atomic.

Test structure:
  Part 1: Baseline — monolithic proofs work
  Part 2: step_plan — step counts with per-arm decomposition
  Part 3: Execution — decomposed steps complete each proof
  Part 4: Format — arm steps use e(), >| stays elt()
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"

# =============================================================================
# Test cases: (name, goal_term, tactic, expected_steps)
#
# expected_steps reflects per-arm decomposition:
#   base steps + 1 per >- arm (not 1 for entire suffix)
# =============================================================================

PROOF_CASES = [
    # -----------------------------------------------------------------
    # Pure >> (no >-) — unchanged from parent task
    # -----------------------------------------------------------------
    (
        "pure_conj",
        "(A:bool) /\\ B ==> A /\\ B",
        "strip_tac >> conj_tac >> fs[]",
        3,
    ),

    # -----------------------------------------------------------------
    # >- with 2 arms — each arm becomes its own e() step
    # -----------------------------------------------------------------
    (
        "conj_2arms",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)",
        4,  # e(strip_tac), eall(conj_tac), e(arm1), e(arm2)
    ),
    (
        "conj_2arms_simple",
        "(A:bool) /\\ B ==> A /\\ B",
        "strip_tac >> conj_tac >- fs[] >- fs[]",
        4,  # e(strip_tac), eall(conj_tac), e(fs[]), e(fs[])
    ),

    # -----------------------------------------------------------------
    # eq_tac >- pattern
    # -----------------------------------------------------------------
    (
        "eq_tac_2arms",
        "(A:bool) /\\ B <=> B /\\ A",
        "eq_tac >- (strip_tac >> conj_tac >> fs[]) >- (strip_tac >> conj_tac >> fs[])",
        3,  # e(eq_tac), e(arm1), e(arm2)
    ),
    (
        "eq_tac_with_base_chain",
        "T ==> ((A:bool) /\\ B <=> B /\\ A)",
        "strip_tac >> eq_tac >- (strip_tac >> simp[]) >- (strip_tac >> simp[])",
        4,  # e(strip_tac), eall(eq_tac), e(arm1), e(arm2)
    ),

    # -----------------------------------------------------------------
    # Cases_on >- pattern
    # -----------------------------------------------------------------
    (
        "cases_2arms",
        "(b:bool) ==> b \\/ ~b",
        "Cases_on `b` >- simp[] >- simp[]",
        3,  # e(Cases_on), e(simp[]), e(simp[])
    ),
    (
        "cases_with_base",
        "(A:bool) ==> (b:bool) ==> A",
        "strip_tac >> Cases_on `b` >- simp[] >- simp[]",
        4,  # e(strip_tac), eall(Cases_on), e(simp[]), e(simp[])
    ),

    # -----------------------------------------------------------------
    # Induct >- pattern
    # -----------------------------------------------------------------
    (
        "induct_2arms",
        "!n:num. n + 0 = n",
        "Induct >- simp[] >- simp[]",
        3,  # e(Induct), e(simp[]), e(simp[])
    ),

    # -----------------------------------------------------------------
    # >| (THENL) — must stay atomic (arms can produce subgoals)
    # -----------------------------------------------------------------
    (
        "thenl_stays_atomic",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >| [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC]",
        3,  # e(strip_tac), eall(conj_tac), elt(ALL_LT >| [...])
    ),

    # -----------------------------------------------------------------
    # Nested >- in arms — inner >- stays opaque (it's inside the arm)
    # -----------------------------------------------------------------
    (
        "nested_inner_opaque",
        "(A:bool) /\\ B ==> B /\\ (A /\\ T)",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >- (conj_tac >- (first_assum ACCEPT_TAC) >- simp[])",
        4,  # e(strip_tac), eall(conj_tac), e(arm1), e(arm2_with_nested_thenlt)
    ),

    # -----------------------------------------------------------------
    # Complex >> chains inside >- arms
    # -----------------------------------------------------------------
    (
        "chains_in_arms",
        "(A:bool) /\\ B ==> (A ==> B) /\\ (B ==> A)",
        "strip_tac >> conj_tac >- (strip_tac >> first_assum ACCEPT_TAC) >- (strip_tac >> first_assum ACCEPT_TAC)",
        4,  # e(strip_tac), eall(conj_tac), e(arm1), e(arm2)
    ),

    # -----------------------------------------------------------------
    # 3 >- arms
    # -----------------------------------------------------------------
    (
        "three_arms",
        "(A:bool) /\\ B /\\ C ==> A /\\ (B /\\ C)",
        "strip_tac >> conj_tac >- fs[] >- (conj_tac >- fs[] >- fs[])",
        4,  # e(strip_tac), eall(conj_tac), e(fs[]), e(nested_arm)
    ),

    # -----------------------------------------------------------------
    # Grouped base — parens must not interfere
    # -----------------------------------------------------------------
    (
        "grouped_base",
        "(A:bool) /\\ B ==> B /\\ A",
        "(strip_tac >> conj_tac) >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)",
        4,  # e(strip_tac), eall(conj_tac), e(arm1), e(arm2)
    ),

    # -----------------------------------------------------------------
    # >- inside >> chain (not top-level) — no arm decomposition
    # -----------------------------------------------------------------
    (
        "thenlt_in_chain",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC",
        # >- binds tighter: strip_tac >> (conj_tac >- arm) >> accept
        # This is a >> chain, not top-level ThenLT. No arm decomposition.
        2,
    ),
]


@pytest.fixture
async def hol_session():
    """HOL session with bossLib loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    await session.send('open HolKernel boolLib bossLib;', timeout=30)
    yield session
    await session.stop()


@pytest.fixture
async def hol_session_with_prefix():
    """HOL session with tactic_prefix loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    await session.send('open HolKernel boolLib bossLib;', timeout=30)
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()


async def call_step_plan(session: HOLSession, tactic_str: str):
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(result)


# =============================================================================
# Part 1: Baseline — every proof works monolithically
# =============================================================================


class TestBaselineProofs:
    """Ground truth: each proof case works via g + e."""

    @pytest.mark.parametrize("name,goal,tactic,_expected_steps", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_prove_directly(self, hol_session, name, goal, tactic, _expected_steps):
        await hol_session.send(f'g `{goal}`;', timeout=10)
        result = await hol_session.send(f'e({tactic});', timeout=30)
        assert "Exception" not in result, f"{name}: e() failed:\n{result}"
        assert "Initial goal proved" in result, f"{name}: proof not complete:\n{result}"
        await hol_session.send('drop();', timeout=5)


# =============================================================================
# Part 2: step_plan returns correct step counts
# =============================================================================


class TestStepPlanArmDecomposition:
    """step_plan should decompose >- arms into individual e() steps."""

    @pytest.mark.parametrize("name,_goal,tactic,expected_steps", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_step_count(self, hol_session_with_prefix, name, _goal, tactic, expected_steps):
        result = await call_step_plan(hol_session_with_prefix, tactic)
        assert len(result) == expected_steps, \
            f"{name}: expected {expected_steps} steps, got {len(result)}: {[s.cmd.strip() for s in result]}"

    async def test_arm_steps_use_e(self, hol_session_with_prefix):
        """Arm steps should use e(), not eall() or elt()."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)"
        )
        # Steps: e(strip_tac), eall(conj_tac), e(arm1), e(arm2)
        assert len(result) == 4
        assert result[0].cmd.strip().startswith("e(")
        assert result[1].cmd.strip().startswith("eall(")
        assert result[2].cmd.strip().startswith("e("), \
            f"Arm 1 should use e(): {result[2].cmd}"
        assert result[3].cmd.strip().startswith("e("), \
            f"Arm 2 should use e(): {result[3].cmd}"

    async def test_thenl_stays_elt(self, hol_session_with_prefix):
        """>| suffix should still use elt(ALL_LT ...), not per-arm e()."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >| [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC]"
        )
        assert len(result) == 3
        suffix = result[-1].cmd.strip()
        assert suffix.startswith("elt("), f">| should use elt(): {suffix}"
        assert ">|" in suffix, f">| operator missing: {suffix}"

    async def test_arm_ends_monotonic(self, hol_session_with_prefix):
        """End positions should be strictly increasing across all steps."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >- simp[] >- fs[]"
        )
        ends = [step.end for step in result]
        for i in range(1, len(ends)):
            assert ends[i] > ends[i-1], f"Non-monotonic ends: {ends}"

    async def test_arm_text_is_tactic(self, hol_session_with_prefix):
        """Arm step commands should contain the arm's tactic text."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "conj_tac >- simp[] >- fs[]"
        )
        # Steps: e(conj_tac), e(simp[]), e(fs[])
        assert len(result) == 3
        assert "simp" in result[1].cmd
        assert "fs" in result[2].cmd

    async def test_no_thenlt_operator_in_arm_steps(self, hol_session_with_prefix):
        """Arm steps should NOT contain >- or ALL_LT — those are suffix artifacts."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "conj_tac >- simp[] >- fs[]"
        )
        for step in result[1:]:  # skip base
            cmd = step.cmd
            assert "ALL_LT" not in cmd, f"ALL_LT in arm step: {cmd}"
            assert ">-" not in cmd, f">- in arm step: {cmd}"


# =============================================================================
# Part 3: Decomposed steps produce same result as monolithic
# =============================================================================


class TestDecomposedExecution:
    """Running decomposed step_plan commands should complete each proof."""

    @pytest.mark.parametrize("name,goal,tactic,_expected_steps", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_decomposed_proves_goal(
        self, hol_session_with_prefix, name, goal, tactic, _expected_steps
    ):
        session = hol_session_with_prefix

        # Monolithic baseline
        await session.send(f"g `{goal}`;", timeout=10)
        mono_result = await session.send(f"e({tactic});", timeout=30)
        assert "Initial goal proved" in mono_result, \
            f"{name}: monolithic failed:\n{mono_result}"
        await session.send("drop();", timeout=5)

        # Decomposed
        steps = await call_step_plan(session, tactic)
        await session.send(f"g `{goal}`;", timeout=10)
        last_result = ""
        for i, step in enumerate(steps):
            last_result = await session.send(step.cmd, timeout=10)
            assert "Exception" not in last_result, \
                f"{name}: step {i} failed: {step.cmd.strip()}\n{last_result}"
        assert "Initial goal proved" in last_result, \
            f"{name}: decomposed didn't prove:\n{last_result}"
        await session.send("drop();", timeout=5)
