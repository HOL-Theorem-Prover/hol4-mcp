"""Acceptance tests for >- arm decomposition in step_plan.

After the parent task (ThenLT base decomposition, 21e313f), the >- suffix
is ONE atomic step: elt(ALL_LT >- arm1 >- arm2). This task decomposes each
>- arm into its own e() step, giving per-arm navigation.

Semantic foundation:
  >- = THEN1: each arm MUST completely solve the first goal (Tactical.sml:220).
  After base creates N goals, sequential e(arm_k) each solve the front goal.
  No subgoals leak because THEN1 enforces complete solution.

  Exception: >| (THENL) arms CAN produce subgoals (Tactical.sml:165).
  Sequential e() would push arm1's subgoals, corrupting arm2's target.
  If ANY arm in the nested ThenLT chain is not LThen1 (i.e., >| or other
  list-tactic form), the ENTIRE suffix must stay atomic as elt(ALL_LT ...).

Refs:
  THEN1: ~/HOL/src/1/Tactical.sml:220-237
  LThen1 in AST: ~/HOL/src/parse/TacticParse.sml
  Parent task: .agent-files/tasks/TASK_thenlt_decomposition.md

Test structure:
  Part 1: Baseline — monolithic proofs work
  Part 2: step_plan — step counts, command format, text extraction
  Part 3: Execution — decomposed steps complete proofs
  Part 4: Intermediate states — goal count decreases by 1 per arm
"""

import pytest
import re
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


# =============================================================================
# Test cases: (name, goal_term, tactic, expected_steps)
# =============================================================================

PROOF_CASES = [
    # --- Pure >> baseline (unchanged) ---
    (
        "pure_chain",
        "(A:bool) /\\ B ==> A /\\ B",
        "strip_tac >> conj_tac >> fs[]",
        3,
    ),

    # --- 2 arms: the standard case ---
    (
        "two_arms_simple",
        "(A:bool) /\\ B ==> A /\\ B",
        "strip_tac >> conj_tac >- fs[] >- fs[]",
        4,  # e(strip_tac), eall(conj_tac), e(fs[]), e(fs[])
    ),

    # --- Single base tactic (no >> before >-) ---
    (
        "single_base",
        "!n:num. n + 0 = n",
        "Induct >- simp[] >- simp[]",
        3,  # e(Induct), e(simp[]), e(simp[])
    ),

    # --- 3 arms from rpt conj_tac (real pattern: arithmeticScript.sml) ---
    (
        "three_arms",
        "(A:bool) /\\ B /\\ C ==> C /\\ B /\\ A",
        "strip_tac >> rpt conj_tac >- fs[] >- fs[] >- fs[]",
        5,  # 2 base + 3 arms
    ),

    # --- 4 arms: stress test ---
    (
        "four_arms",
        "(A:bool) /\\ B /\\ C /\\ D ==> D /\\ C /\\ B /\\ A",
        "strip_tac >> rpt conj_tac >- fs[] >- fs[] >- fs[] >- fs[]",
        6,  # 2 base + 4 arms
    ),

    # --- eq_tac >- (iff split, real pattern: arithmeticScript.sml LE_ANTISYM) ---
    (
        "eq_tac_iff",
        "(A:bool) /\\ B <=> B /\\ A",
        "eq_tac >- (strip_tac >> conj_tac >> fs[]) >- (strip_tac >> conj_tac >> fs[])",
        3,  # 1 base + 2 arms
    ),

    # --- Arm is a >> chain (multi-step arm stays as ONE e() step) ---
    (
        "chain_inside_arm",
        "(A:bool) /\\ B ==> (A ==> B) /\\ (B ==> A)",
        "strip_tac >> conj_tac >- (strip_tac >> first_assum ACCEPT_TAC) >- (strip_tac >> first_assum ACCEPT_TAC)",
        4,
    ),

    # --- Arm contains nested >- (inner >- is opaque inside arm's e()) ---
    (
        "arm_has_inner_thenlt",
        "(A:bool) /\\ B ==> B /\\ (A /\\ T)",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >- (conj_tac >- (first_assum ACCEPT_TAC) >- simp[])",
        4,  # base(2) + arm1(simple) + arm2(has inner >-, but opaque)
    ),

    # --- Asymmetric arms (one trivial, one complex) ---
    (
        "asymmetric_arms",
        "T /\\ (T ==> T)",
        "conj_tac >- simp[] >- (strip_tac >> simp[])",
        3,  # 1 base + 2 differently-structured arms
    ),

    # --- Grouped base: (a >> b) >- arm1 >- arm2 ---
    (
        "grouped_base",
        "(A:bool) /\\ B ==> B /\\ A",
        "(strip_tac >> conj_tac) >- (first_assum ACCEPT_TAC) >- (first_assum ACCEPT_TAC)",
        4,
    ),

    # --- >| MUST stay atomic (THENL arms can produce subgoals) ---
    (
        "thenl_atomic",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >| [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC]",
        3,  # base(2) + elt(ALL_LT >| [...])
    ),

    # --- Mixed >- then >| in same chain: outer arm is LNullOk, not LThen1.
    #     Entire suffix must stay atomic. ---
    (
        "mixed_thenlt_thenl_fallback",
        "(A:bool) /\\ B /\\ C ==> C /\\ B /\\ A",
        "strip_tac >> rpt conj_tac >- fs[] >| [fs[], fs[]]",
        3,  # can't decompose: one arm is >| → fallback to atomic suffix
    ),

    # --- >- inside >> chain (NOT top-level): no arm decomposition ---
    (
        "thenlt_inside_chain",
        "(A:bool) /\\ B ==> B /\\ A",
        "strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC",
        2,  # >> chain: [(strip_tac >> (conj_tac >- arm)), accept]
    ),

    # --- Long >> base before >- ---
    (
        "long_base_before_arms",
        "T ==> ((A:bool) /\\ B <=> B /\\ A)",
        "strip_tac >> eq_tac >- (strip_tac >> simp[]) >- (strip_tac >> simp[])",
        4,  # 2 base + 2 arms
    ),
]


@pytest.fixture
async def hol_session():
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    await session.send('open HolKernel boolLib bossLib;', timeout=30)
    yield session
    await session.stop()


@pytest.fixture
async def hol_session_with_prefix():
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


def count_goals(hol_output: str) -> int | None:
    """Extract goal count from HOL output."""
    m = re.search(r'(\d+)\s+subgoals?', hol_output)
    if m:
        return int(m.group(1))
    if "Initial goal proved" in hol_output:
        return 0
    # Goal proved with remaining subgoals but no explicit count → 1 remaining
    if "Goal proved" in hol_output and "Remaining subgoals" in hol_output:
        return 1
    return None


# =============================================================================
# Part 1: Baseline
# =============================================================================


class TestBaselineProofs:

    @pytest.mark.parametrize("name,goal,tactic,_", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_prove_directly(self, hol_session, name, goal, tactic, _):
        await hol_session.send(f'g `{goal}`;', timeout=10)
        result = await hol_session.send(f'e({tactic});', timeout=30)
        assert "Exception" not in result, f"{name}: failed:\n{result}"
        assert "Initial goal proved" in result, f"{name}: incomplete:\n{result}"
        await hol_session.send('drop();', timeout=5)


# =============================================================================
# Part 2: Step plan decomposition
# =============================================================================


class TestStepPlanArmDecomposition:

    # --- Step counts ---

    @pytest.mark.parametrize("name,_goal,tactic,expected_steps", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_step_count(self, hol_session_with_prefix, name, _goal, tactic, expected_steps):
        result = await call_step_plan(hol_session_with_prefix, tactic)
        assert len(result) == expected_steps, \
            f"{name}: expected {expected_steps}, got {len(result)}: " \
            f"{[s.cmd.strip()[:50] for s in result]}"

    # --- Command format ---

    async def test_arm_steps_use_e(self, hol_session_with_prefix):
        """Arm steps must use e(), not eall() or elt()."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >- fs[] >- fs[]"
        )
        assert len(result) == 4
        assert result[0].cmd.strip().startswith("e(")      # base 1
        assert result[1].cmd.strip().startswith("eall(")    # base 2
        for i in [2, 3]:
            cmd = result[i].cmd.strip()
            assert cmd.startswith("e(") and not cmd.startswith("eall(") \
                and not cmd.startswith("elt("), \
                f"Arm step {i-1} should be e(): {cmd}"

    async def test_thenl_suffix_uses_elt(self, hol_session_with_prefix):
        """>| suffix must use elt(ALL_LT ...), unchanged."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "conj_tac >| [simp[], fs[]]"
        )
        assert len(result) == 2
        suffix = result[-1].cmd.strip()
        assert suffix.startswith("elt("), f">| should use elt(): {suffix}"
        assert ">|" in suffix

    async def test_mixed_fallback_uses_elt(self, hol_session_with_prefix):
        """Mixed >- then >| must fall back to elt() for entire suffix."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> rpt conj_tac >- fs[] >| [fs[], fs[]]"
        )
        assert len(result) == 3
        suffix = result[-1].cmd.strip()
        assert suffix.startswith("elt("), f"Mixed suffix should be elt(): {suffix}"
        # Suffix should contain both the >- and >| operators
        assert ">-" in suffix and ">|" in suffix, f"Should contain both ops: {suffix}"

    # --- Arm text extraction ---

    async def test_chain_arm_text_complete(self, hol_session_with_prefix):
        """Arm that's a >> chain must have complete chain text in e()."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "conj_tac >- (strip_tac >> first_assum ACCEPT_TAC) >- (strip_tac >> first_assum ACCEPT_TAC)"
        )
        assert len(result) == 3
        for i in [1, 2]:
            cmd = result[i].cmd
            assert "strip_tac" in cmd, f"Arm {i} missing strip_tac: {cmd}"
            assert "ACCEPT_TAC" in cmd, f"Arm {i} missing ACCEPT_TAC: {cmd}"

    async def test_nested_thenlt_arm_preserves_inner_operators(self, hol_session_with_prefix):
        """Arm containing >- must include inner >- in its e() text.
        
        The inner >- is part of the arm's tactic — it should be in the
        extracted text, not confused with the outer >- operators.
        """
        result = await call_step_plan(
            hol_session_with_prefix,
            "conj_tac >- simp[] >- (conj_tac >- simp[] >- simp[])"
        )
        assert len(result) == 3
        # First arm: simple, no >-
        assert ">-" not in result[1].cmd
        # Second arm: has inner >- from nested ThenLT
        arm2 = result[2].cmd
        assert ">-" in arm2, f"Inner >- should be in arm text: {arm2}"
        assert arm2.strip().startswith("e("), f"Wrapper must be e(): {arm2}"

    async def test_by_outermost_decomposes_to_plain_e(self, hol_session_with_prefix):
        """`by` at top level → e(sg `P`) + e(tac), not elt(ALL_LT >- tac).
        
        `by` parses as ThenLT(Subgoal, [LThen1(tac)]) — single arm.
        Should decompose like any other single >- arm.
        """
        result = await call_step_plan(
            hol_session_with_prefix,
            "`T` by simp[]"
        )
        assert len(result) == 2
        assert "sg" in result[0].cmd
        arm = result[1].cmd.strip()
        assert arm.startswith("e("), f"by arm should be e(): {arm}"
        assert "ALL_LT" not in arm, f"Should not have ALL_LT: {arm}"
        assert "simp" in arm

    # --- End positions ---

    async def test_ends_strictly_increasing(self, hol_session_with_prefix):
        """End positions must increase across base AND arm steps."""
        result = await call_step_plan(
            hol_session_with_prefix,
            "strip_tac >> conj_tac >- (strip_tac >> fs[]) >- (strip_tac >> simp[])"
        )
        ends = [s.end for s in result]
        for i in range(1, len(ends)):
            assert ends[i] > ends[i-1], \
                f"Non-monotonic at {i}: {ends}"

    async def test_last_arm_end_equals_proof_length(self, hol_session_with_prefix):
        """Last arm's end position should equal the full tactic text length."""
        tactic = "conj_tac >- simp[] >- fs[]"
        result = await call_step_plan(hol_session_with_prefix, tactic)
        assert result[-1].end == len(tactic)


# =============================================================================
# Part 3: Decomposed steps complete proofs
# =============================================================================


class TestDecomposedExecution:

    @pytest.mark.parametrize("name,goal,tactic,_", PROOF_CASES,
                             ids=[c[0] for c in PROOF_CASES])
    async def test_decomposed_proves_goal(
        self, hol_session_with_prefix, name, goal, tactic, _
    ):
        session = hol_session_with_prefix

        # Monolithic baseline
        await session.send(f"g `{goal}`;", timeout=10)
        mono = await session.send(f"e({tactic});", timeout=30)
        assert "Initial goal proved" in mono, f"{name}: mono failed:\n{mono}"
        await session.send("drop();", timeout=5)

        # Decomposed
        steps = await call_step_plan(session, tactic)
        await session.send(f"g `{goal}`;", timeout=10)
        last = ""
        for i, step in enumerate(steps):
            last = await session.send(step.cmd, timeout=10)
            assert "Exception" not in last, \
                f"{name}: step {i} ({step.cmd.strip()[:40]}) failed:\n{last}"
        assert "Initial goal proved" in last, \
            f"{name}: didn't complete:\n{last}"
        await session.send("drop();", timeout=5)


# =============================================================================
# Part 4: Intermediate state verification
#
# Verify that each arm step reduces the goal count by exactly 1.
# This catches bugs where arm text is wrong but proof accidentally works
# (e.g., arm1 solves both goals, arm2 encounters no goals).
# =============================================================================


class TestIntermediateStates:

    async def test_two_arm_goal_reduction(self, hol_session_with_prefix):
        """conj_tac produces 2 goals; each arm solves exactly one."""
        session = hol_session_with_prefix
        steps = await call_step_plan(session,
            "strip_tac >> conj_tac >- fs[] >- fs[]")
        assert len(steps) == 4

        await session.send('g `(A:bool) /\\ B ==> A /\\ B`;', timeout=10)

        r = await session.send(steps[0].cmd, timeout=10)  # strip_tac
        r = await session.send(steps[1].cmd, timeout=10)  # conj_tac
        assert count_goals(r) == 2, f"After conj_tac: {r}"

        r = await session.send(steps[2].cmd, timeout=10)  # arm1
        assert count_goals(r) == 1, f"After arm1, expected 1 goal: {r}"

        r = await session.send(steps[3].cmd, timeout=10)  # arm2
        assert count_goals(r) == 0, f"After arm2, expected proof done: {r}"

        await session.send("drop();", timeout=5)

    async def test_three_arm_sequential_reduction(self, hol_session_with_prefix):
        """rpt conj_tac on A/\\B/\\C gives 3 goals; arms solve 3→2→1→0."""
        session = hol_session_with_prefix
        steps = await call_step_plan(session,
            "strip_tac >> rpt conj_tac >- fs[] >- fs[] >- fs[]")
        assert len(steps) == 5

        await session.send(
            'g `(A:bool) /\\ B /\\ C ==> C /\\ B /\\ A`;', timeout=10)
        await session.send(steps[0].cmd, timeout=10)  # strip_tac
        r = await session.send(steps[1].cmd, timeout=10)  # rpt conj_tac
        assert count_goals(r) == 3

        r = await session.send(steps[2].cmd, timeout=10)  # arm1
        assert count_goals(r) == 2, f"3→2 failed: {r}"

        r = await session.send(steps[3].cmd, timeout=10)  # arm2
        assert count_goals(r) == 1, f"2→1 failed: {r}"

        r = await session.send(steps[4].cmd, timeout=10)  # arm3
        assert count_goals(r) == 0, f"1→0 failed: {r}"

        await session.send("drop();", timeout=5)

    async def test_complex_arm_solves_exactly_one_goal(self, hol_session_with_prefix):
        """A >> chain arm should solve its target goal without affecting others."""
        session = hol_session_with_prefix
        steps = await call_step_plan(session,
            "strip_tac >> conj_tac >- (strip_tac >> first_assum ACCEPT_TAC) >- (strip_tac >> first_assum ACCEPT_TAC)")
        assert len(steps) == 4

        await session.send(
            'g `(A:bool) /\\ B ==> (A ==> B) /\\ (B ==> A)`;', timeout=10)
        await session.send(steps[0].cmd, timeout=10)
        r = await session.send(steps[1].cmd, timeout=10)
        assert count_goals(r) == 2

        # Complex arm1: strip_tac >> first_assum ACCEPT_TAC
        # Should solve goal 1 (A ==> B) using assumption A
        r = await session.send(steps[2].cmd, timeout=10)
        assert count_goals(r) == 1, \
            f"Complex arm should solve exactly 1 goal: {r}"

        r = await session.send(steps[3].cmd, timeout=10)
        assert count_goals(r) == 0

        await session.send("drop();", timeout=5)

    async def test_four_arms_four_goals(self, hol_session_with_prefix):
        """4-way conjunction: each arm peels off exactly one goal."""
        session = hol_session_with_prefix
        steps = await call_step_plan(session,
            "strip_tac >> rpt conj_tac >- fs[] >- fs[] >- fs[] >- fs[]")
        assert len(steps) == 6

        await session.send(
            'g `(A:bool) /\\ B /\\ C /\\ D ==> D /\\ C /\\ B /\\ A`;',
            timeout=10)
        await session.send(steps[0].cmd, timeout=10)
        r = await session.send(steps[1].cmd, timeout=10)
        assert count_goals(r) == 4

        for i, expected in [(2, 3), (3, 2), (4, 1), (5, 0)]:
            r = await session.send(steps[i].cmd, timeout=10)
            g = count_goals(r)
            assert g == expected, f"Step {i}: expected {expected} goals, got {g}: {r}"

        await session.send("drop();", timeout=5)
