"""Acceptance tests for ThenLT (>-) decomposition in step_plan.

Currently, top-level >- makes the ENTIRE proof ONE atomic step, sacrificing
navigation granularity. The proposed feature decomposes the >> base chain
while keeping the >- suffix atomic, giving per-tactic stepping within the
>> prefix.

Test structure:
  Part 1: Baseline — g + e each goal+tactic monolithically to confirm they work
  Part 2: step_plan — verify decomposition returns correct step counts
  Part 3: Execution — run decomposed steps and compare to monolithic

Semantic foundation (from HOL source):
  e(tac) = expandf(VALID tac)             → tac on FIRST goal, PUSH frame
  eall(tac) = expand_list(ALLGOALS tac)   → tac on EACH goal, REPLACE top
  tac1 >> tac2 = tac1 THEN_LT ALLGOALS tac2

  Therefore e(a); eall(b) ≡ e(a >> b) when starting from 1 goal.
Refs: Manager.sml:114-131, goalStack.sml:168-190, Tactical.sml:146
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"

# =============================================================================
# Test cases: (name, goal_term, tactic, expected_decomposed_steps)
#
# Each is a valid HOL proof verified via g + e.
# expected_decomposed_steps = desired step count AFTER implementing the feature.
# =============================================================================

PROOF_CASES = [
    # -----------------------------------------------------------------
    # Pure >> (no >-) — baseline, always decomposed
    # -----------------------------------------------------------------
    (
        "pure_conj",
        "(A:bool) /\\ B ==> A /\\ B",
        "strip_tac >> conj_tac >> fs[]",
        3,
    ),
    (
        "pure_long_chain",
        "(A:bool) /\\ B /\\ C ==> C /\\ B /\\ A",
        "strip_tac >> rpt conj_tac >> fs[]",
        3,
    ),

    # -----------------------------------------------------------------
    # Simple >- at top level (base + suffix)
    # Adapted from: arithmeticScript.sml DIV_0, MOD_0
    # -----------------------------------------------------------------
    (
        "conj_tac_thenlt",
        # conj_tac >- arm1 >> continuation — classic split pattern
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)",
        3,  # strip_tac, conj_tac, >- suffix
    ),
    (
        "bare_thenlt",
        # No >> base, just tactic >- arms
        "(A:bool) /\\ B ==> A /\\ B",
        "strip_tac >> conj_tac >- fs[] >- fs[]",
        3,
    ),

    # -----------------------------------------------------------------
    # eq_tac >- pattern (iff proofs)
    # Adapted from: arithmeticScript.sml LE_ANTISYM
    # -----------------------------------------------------------------
    (
        "eq_tac_thenlt",
        "(A:bool) /\\ B <=> B /\\ A",
        "eq_tac >- (strip_tac >> conj_tac >> fs[]) >- (strip_tac >> conj_tac >> fs[])",
        2,  # eq_tac, >- suffix
    ),
    (
        "eq_tac_with_chain",
        # >> before eq_tac >-
        "T ==> ((A:bool) /\\ B <=> B /\\ A)",
        "strip_tac >> eq_tac >- (strip_tac >> simp[]) >- (strip_tac >> simp[])",
        3,  # strip_tac, eq_tac, >- suffix
    ),

    # -----------------------------------------------------------------
    # Cases_on >- pattern (case splits)
    # Adapted from: arithmeticScript.sml SUB_LESS_OR_EQ, EXP_LE_1
    # -----------------------------------------------------------------
    (
        "cases_bool",
        "(b:bool) ==> b \\/ ~b",
        "Cases_on `b` >- simp[] >- simp[]",
        2,  # Cases_on, >- suffix
    ),
    (
        "cases_with_chain",
        "(A:bool) ==> (b:bool) ==> A",
        "strip_tac >> Cases_on `b` >- simp[] >- simp[]",
        3,  # strip_tac, Cases_on, >- suffix
    ),

    # -----------------------------------------------------------------
    # Induct >- pattern (induction)
    # Adapted from: pred_setScript.sml SCHROEDER_CLOSE_SET
    # -----------------------------------------------------------------
    (
        "induct_thenlt",
        "!n:num. n + 0 = n",
        "Induct >- simp[] >- simp[]",
        2,  # Induct, >- suffix
    ),
    (
        "induct_with_chain",
        "!n:num. 0 + n = n",
        "Induct >- simp[] >> simp[]",
        2,  # Induct is the only >> base element, then >- suffix + >> continuation
        # Actually: Induct >- simp[] >> simp[] parses as (Induct >- simp[]) >> simp[]
        # because >- binds tighter, so this is a >> chain of 2 elements
    ),

    # -----------------------------------------------------------------
    # >| (THENL) — list tactic routing
    # Adapted from: listScript.sml MEM_SPLIT
    # -----------------------------------------------------------------
    (
        "thenl_conj",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >| [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC]",
        3,  # strip_tac, conj_tac, >| suffix
    ),

    # -----------------------------------------------------------------
    # >- used as THEN1 inside >> chain (not at top level)
    # The >- resolves ONE goal and >> continues with the rest.
    # Adapted from: pred_setScript.sml BIJ_INJ_SURJ pattern
    # -----------------------------------------------------------------
    (
        "then1_in_chain",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC",
        # >- binds tighter than >>, so: strip_tac >> (conj_tac >- accept) >> accept
        2,  # (strip_tac >> conj_tac >- accept), accept
    ),

    # -----------------------------------------------------------------
    # Nested >- in arms
    # -----------------------------------------------------------------
    (
        "nested_thenlt",
        "(A:bool) /\\ B ==> B /\\ (A /\\ T)",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >- (conj_tac >- (first_assum ACCEPT_TAC) >- simp[])",
        3,  # strip_tac, conj_tac, >- suffix (nested >- is inside arm, stays atomic)
    ),

    # -----------------------------------------------------------------
    # >> arms with >- — chains inside each >- arm
    # Adapted from: cfgTransformProofsScript.sml wf_function pattern
    # -----------------------------------------------------------------
    (
        "chains_in_arms",
        "(A:bool) /\\ B ==> (A ==> B) /\\ (B ==> A)",
        "strip_tac >> conj_tac >- (strip_tac >> first_assum ACCEPT_TAC) >- (strip_tac >> first_assum ACCEPT_TAC)",
        3,  # strip_tac, conj_tac, >- suffix
    ),

    # -----------------------------------------------------------------
    # Existential goals
    # -----------------------------------------------------------------
    (
        "exists_thenlt",
        "(A:bool) ==> ?x. x /\\ A",
        "strip_tac >> qexists_tac `T` >> simp[]",
        3,  # strip_tac, qexists_tac, simp[]  (pure >> chain, no >-)
    ),

    # -----------------------------------------------------------------
    # Disjunction
    # -----------------------------------------------------------------
    (
        "disj_thenlt",
        "(A:bool) ==> A \\/ B",
        "strip_tac >> disj1_tac >> first_assum ACCEPT_TAC",
        3,  # pure >> chain
    ),

    # -----------------------------------------------------------------
    # metis_tac / decide pattern (heavyweight solvers in >> chain)
    # -----------------------------------------------------------------
    (
        "metis_chain",
        "(A:bool) ==> (A ==> B) ==> (B ==> C) ==> C",
        "rpt strip_tac >> metis_tac[]",
        2,
    ),

    # -----------------------------------------------------------------
    # reverse EQ_TAC >- pattern
    # Adapted from: arithmeticScript.sml SUB_LESS_OR_EQ
    # -----------------------------------------------------------------
    (
        "reverse_eq_tac",
        "(A:bool) /\\ B <=> B /\\ A",
        "reverse eq_tac >- (strip_tac >> fs[]) >> strip_tac >> fs[]",
        # reverse eq_tac is inside a >- at top, so:
        # reverse flips the goal order. eq_tac splits. >- handles first arm.
        # Then >> strip_tac >> fs[] handles the second arm.
        # Parse: (reverse eq_tac >- (strip_tac >> fs[])) >> strip_tac >> fs[]
        # >- binds tighter, so this is a >> chain with 3 elements:
        #   [(reverse eq_tac >- ...), strip_tac, fs[]]
        3,
    ),

    # -----------------------------------------------------------------
    # rpt strip_tac (includes CONJ_TAC internally)
    # -----------------------------------------------------------------
    (
        "rpt_strip_splits",
        "(A:bool) /\\ B ==> B /\\ A",
        "rpt strip_tac >> first_assum ACCEPT_TAC",
        2,
    ),

    # -----------------------------------------------------------------
    # 5-step >> base before >-
    # -----------------------------------------------------------------
    (
        "long_base_thenlt",
        "(A:bool) /\\ B /\\ C ==> A /\\ (B /\\ C)",
        "strip_tac >> conj_tac >- fs[] >- (conj_tac >- fs[] >- fs[])",
        3,  # strip_tac, conj_tac, >- suffix
    ),

    # -----------------------------------------------------------------
    # `by` at top level — ThenLT wrapped in Group
    # -----------------------------------------------------------------
    (
        "by_toplevel",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> `A:bool` by fs[] >> fs[]",
        3,  # strip_tac, (`A` by fs[]), fs[]
        # `by` creates ThenLT inside Group which sits in the >> chain
    ),

    # -----------------------------------------------------------------
    # Grouped base — parens must not leak into suffix
    # -----------------------------------------------------------------
    (
        "grouped_base",
        "(A:bool) /\\ B ==> B /\\ A",
        "(strip_tac >> conj_tac) >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)",
        3,  # strip_tac, conj_tac, >- suffix
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
        """Each proof must succeed via g + e (monolithic)."""
        await hol_session.send(f'g `{goal}`;', timeout=10)
        result = await hol_session.send(f'e({tactic});', timeout=30)
        assert "Exception" not in result, f"{name}: e() failed:\n{result}"
        assert "error" not in result.lower() or "error" in goal.lower(), \
            f"{name}: e() error:\n{result}"
        assert "Initial goal proved" in result, \
            f"{name}: proof not complete:\n{result}"
        await hol_session.send('drop();', timeout=5)


# =============================================================================
# Part 2: step_plan returns correct step counts
# =============================================================================


class TestStepPlanDecomposition:
    """step_plan should decompose >> base of top-level >- expressions."""

    @pytest.mark.parametrize("name,_goal,tactic,expected_steps", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_step_count(self, hol_session_with_prefix, name, _goal, tactic, expected_steps):
        """step_plan should return expected number of steps."""
        result = await call_step_plan(hol_session_with_prefix, tactic)
        assert len(result) == expected_steps, \
            f"{name}: expected {expected_steps} steps, got {len(result)}: {[s.cmd.strip() for s in result]}"

    async def test_first_step_e_rest_eall(self, hol_session_with_prefix):
        """First step uses e(), all subsequent use eall()."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)"
        )
        assert result[0].cmd.strip().startswith("e(")
        for step in result[1:]:
            cmd = step.cmd.strip()
            assert cmd.startswith("eall(") or cmd.startswith("elt("), \
                f"Non-eall/elt step: {step.cmd}"

    async def test_ends_monotonic(self, hol_session_with_prefix):
        """End positions should be strictly increasing."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >- simp[] >- fs[]"
        )
        ends = [step.end for step in result]
        for i in range(1, len(ends)):
            assert ends[i] > ends[i-1], f"Non-monotonic ends: {ends}"

    async def test_by_outermost_rewrites_to_thenl(self, hol_session_with_prefix):
        """`by` at outermost ThenLT decomposes with >- (not by) in suffix.

        `by` = `sg >- tac`. After decomposing sg as base, suffix needs >-
        because ALL_LT by tac is a type error (by expects quotation, not list_tactic).
        """
        result = await call_step_plan(
            hol_session_with_prefix, "`P` by simp[]"
        )
        assert len(result) == 2
        assert "sg" in result[0].cmd
        suffix = result[1].cmd.strip()
        assert suffix.startswith("elt(")
        assert ">-" in suffix, f"by should be rewritten to >-: {suffix}"
        assert " by " not in suffix, f"by should not appear in suffix: {suffix}"

    async def test_grouped_base_no_paren_leak(self, hol_session_with_prefix):
        """Grouped base (a >> b) >- c must not leak closing paren into suffix."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "(strip_tac >> conj_tac) >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)"
        )
        assert len(result) == 3
        suffix = result[-1].cmd
        assert "ALL_LT )" not in suffix, f"Closing paren leaked into suffix: {suffix}"
        assert "ALL_LT >-" in suffix, f"Expected 'ALL_LT >-' in suffix: {suffix}"

    async def test_suffix_contains_thenlt_operator(self, hol_session_with_prefix):
        """The >- suffix step should contain the routing operator."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >- simp[] >- fs[]"
        )
        suffix = result[-1].cmd
        assert ">-" in suffix or ">>>" in suffix or "THEN_LT" in suffix or \
               "HEADGOAL" in suffix, f"Suffix doesn't contain >- operator: {suffix}"


# =============================================================================
# Part 3: Decomposed steps produce same result as monolithic
# =============================================================================


class TestDecomposedExecution:
    """Running decomposed step_plan commands should complete each proof."""

    @pytest.mark.parametrize("name,goal,tactic,_expected_steps", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_decomposed_matches_monolithic(
        self, hol_session_with_prefix, name, goal, tactic, _expected_steps
    ):
        """Decomposed e()/eall() steps should complete the proof."""
        session = hol_session_with_prefix

        # --- Monolithic: confirm proof completes ---
        await session.send(f"g `{goal}`;", timeout=10)
        mono_result = await session.send(f"e({tactic});", timeout=30)
        mono_proved = "Initial goal proved" in mono_result
        await session.send("drop();", timeout=5)
        assert mono_proved, f"{name}: monolithic e() didn't prove goal:\n{mono_result}"

        # --- Decomposed: run step_plan commands ---
        steps = await call_step_plan(session, tactic)
        await session.send(f"g `{goal}`;", timeout=10)
        last_result = ""
        for step in steps:
            last_result = await session.send(step.cmd, timeout=10)
            assert "Exception" not in last_result, \
                f"{name}: step failed: {step.cmd}\n{last_result}"
        decomp_proved = "Initial goal proved" in last_result
        await session.send("drop();", timeout=5)

        assert decomp_proved, \
            f"{name}: decomposed steps didn't prove goal:\n{last_result}"
