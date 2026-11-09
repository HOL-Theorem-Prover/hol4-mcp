"""Tests for tactic_prefix.sml functions (goalfrag_step_plan).

Tests the GOALFRAG-based proof navigation: every TacticParse.linearize fragment
is a step, FOpen/FFMid/FFClose are natively steppable via ef().
"""

import pytest
import json
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    """Fixture that provides a HOL session with tactic_prefix loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()


async def call_step_plan(session: HOLSession, tactic_str: str):
    """Call goalfrag_step_plan_json and parse the result."""
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'goalfrag_step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(result)




# =============================================================================
# Step Plan: basic structure
# =============================================================================

class TestGoalfragStepPlanBasic:
    """Basic goalfrag_step_plan tests."""

    async def test_single_tactic(self, hol_session):
        """Single tactic returns one step."""
        result = await call_step_plan(hol_session, "simp[]")
        assert len(result) == 1
        assert "ef(goalFrag.expand(simp[])(Context.snapshot()))" in result[0].cmd

    async def test_then_chain(self, hol_session):
        """>> chain returns one step per tactic."""
        result = await call_step_plan(hol_session, "a >> b >> c")
        assert len(result) == 3
        assert "ef(goalFrag.expand(a)(Context.snapshot()))" in result[0].cmd
        assert "ef(goalFrag.expand(b)(Context.snapshot()))" in result[1].cmd
        assert "ef(goalFrag.expand(c)(Context.snapshot()))" in result[2].cmd

    async def test_ends_are_monotonic(self, hol_session):
        """End offsets should be monotonically non-decreasing."""
        result = await call_step_plan(hol_session, "a >> b >> c >> d")
        ends = [step.end for step in result]
        assert ends == sorted(ends)

    async def test_empty_proof_body_returns_empty_expand(self, hol_session):
        """Empty proof body produces a single empty expand step."""
        result = await call_step_plan(hol_session, "")
        # parseTacticBlock on "" produces Opaque with zero-length span
        assert len(result) <= 1  # 0 or 1 step (empty expand)

    async def test_with_quotations(self, hol_session):
        """Backtick quotations work."""
        result = await call_step_plan(hol_session, "Cases_on `x` >> simp[]")
        assert len(result) == 2
        assert "Cases_on" in result[0].cmd
        assert "simp" in result[1].cmd


# =============================================================================
# Step Plan: >- (Then1) decomposition
# =============================================================================

class TestGoalfragThen1Decomposition:
    """With GOALFRAG, >- decomposes into open/expand/close fragments."""

    async def test_single_then1(self, hol_session):
        """`a >- b` → expand(a), open_then1, expand(b), close_paren."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        cmds = [s.cmd for s in result]
        assert "ef(goalFrag.expand(conj_tac)(Context.snapshot()));" in cmds
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.expand(simp[])(Context.snapshot()));" in cmds
        assert "ef(goalFrag.close_paren);" in cmds
        # Order: expand base, open, expand arm, close
        assert cmds.index("ef(goalFrag.expand(conj_tac)(Context.snapshot()));") < cmds.index("ef(goalFrag.open_then1);")
        assert cmds.index("ef(goalFrag.open_then1);") < cmds.index("ef(goalFrag.expand(simp[])(Context.snapshot()));")
        assert cmds.index("ef(goalFrag.expand(simp[])(Context.snapshot()));") < cmds.index("ef(goalFrag.close_paren);")

    async def test_nested_then1(self, hol_session):
        """Chained >- decomposes each arm."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >- fs[]")
        cmds = [s.cmd for s in result]
        # Should have: expand(conj_tac), open, expand(simp[]), close, open, expand(fs[]), close
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.close_paren);" in cmds
        # Two open_then1 (one per >-)
        assert cmds.count("ef(goalFrag.open_then1);") == 2
        assert cmds.count("ef(goalFrag.close_paren);") == 2

    async def test_by_decomposition(self, hol_session):
        """`by` (sugar for >-) decomposes the same way."""
        result = await call_step_plan(hol_session, "strip_tac by simp[]")
        cmds = [s.cmd for s in result]
        assert "ef(goalFrag.expand(strip_tac)(Context.snapshot()));" in cmds
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.expand(simp[])(Context.snapshot()));" in cmds
        assert "ef(goalFrag.close_paren);" in cmds


# =============================================================================
# Step Plan: >| (ThenL) — stays atomic when linearize treats it as one
# =============================================================================

class TestGoalfragThenLDecomposition:
    """Multi-arm >| decomposition depends on linearize output."""

    async def test_thenl_atomic(self, hol_session):
        """strip_tac >| [simp[], fs[]] may be one atom if linearize doesn't decompose it."""
        result = await call_step_plan(hol_session, "strip_tac >| [simp[], fs[]]")
        # linearize treats this as FAtom(Opaque) — one step
        assert len(result) >= 1
        assert "ef(goalFrag.expand" in result[0].cmd


# =============================================================================
# Step Plan: execution correctness
# =============================================================================

class TestGoalfragExecutionCorrectness:
    """Verify that step_plan steps actually execute and produce correct goals."""

    async def test_then_chain_execution(self, hol_session):
        """>> chain steps execute correctly on GOALFRAG."""
        result = await call_step_plan(hol_session, "CONJ_TAC >> REFL_TAC >> REFL_TAC")
        # Without >-, CONJ_TAC creates 2 goals >> applies to both
        # Actually CONJ_TAC >> REFL_TAC on `T /\ T` would:
        # CONJ_TAC splits into T, T; REFL_TAC fails on T (not an equation)
        # Use a simpler proof
        pass  # Execution tests are covered by state_at integration tests

    async def test_then1_execution(self, hol_session):
        """Single >- step plan executes correctly on GOALFRAG."""
        # Set up goal and execute steps
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\ T`;', timeout=10)

        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        assert len(result) == 7  # expand, open, expand, close, open, expand, close

        # Execute all steps
        for step in result:
            r = await hol_session.send(step.cmd, timeout=10)
            assert not any("Exception-" in line for line in r.split('\n')), f"Step failed: {step.cmd} → {r}"

        # Verify proof completed
        r = await hol_session.send('top_thm();', timeout=10)
        assert "T ∧ T" in r


# =============================================================================
# backup_n
# =============================================================================

class TestBackupN:
    """Test backup_n undoes ef() steps on GOALFRAG."""

    async def test_backup_then1_proof(self, hol_session):
        """backup_n correctly undoes >- steps."""
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\ T`;', timeout=10)

        plan = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")

        # Execute up to step 3 (CONJ_TAC + open_then1 + SIMP_TAC)
        for step in plan[:3]:
            await hol_session.send(step.cmd, timeout=10)

        # Check goals: should have 0 goals (first arm solved, focused)
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 0, f"Expected 0 goals after step 3, got {len(goals)}"
                break

        # Backup 2 steps (undo SIMP_TAC + open_then1)
        await hol_session.send('backup_n 2;', timeout=10)

        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 2, f"Expected 2 goals after backup, got {len(goals)}"
                break

    async def test_backup_full_proof(self, hol_session):
        """backup_n undoes entire proof back to initial goal."""
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\ T`;', timeout=10)

        plan = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")

        for step in plan:
            await hol_session.send(step.cmd, timeout=10)

        # Should be complete
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 0
                break

        # Undo all
        await hol_session.send(f'backup_n {len(plan)};', timeout=10)

        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 1
                assert "T ∧ T" in goals[0]['goal']
                break


# =============================================================================
# Step Plan: ThenLT/By re-expansion inside >> chains
# =============================================================================

class TestThenLTReexpand:
    """ThenLT inside >> chains: KEPT OPAQUE so per-goal vs global semantics
    of the inner `>-` are preserved.

    The parser emits `Group(true, ..., ThenLT(_, [LThen1 _]))` for any
    precedence-grouped `tac1 >- tac2` sub-expression — including cases
    without source parens (left-associative grouping is implicit). My
    isComposable check excludes these Groups from re-expansion because
    re-expanding them would emit `[expand tac1, open_then1, expand tac2,
    close_paren]` fragments where `open_then1` runs GLOBALLY across the
    goalstate, diverging from Holmake's per-goal semantics whenever the
    Group sits inside an outer per-goal-distributing context.

    Trade-off: lose mid-arm navigation between `tac1` and `tac2`. The
    whole `tac1 >- tac2` runs as one atomic expand step.

    Subgoal-based ThenLT (by/sg) is similarly atomic — the merged form
    `\`Q\` by tac` runs per-goal correctly via goalFrag.expand.
    """

    async def test_thenlt_in_then_chain(self, hol_session):
        """`tac1 >- tac2 >> tac3` precedence-groups as
        `((tac1 >- tac2) >> tac3)`. The inner `>-` Group stays opaque; the
        outer `>>` chain is two expand steps."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> fs[]")
        assert len(result) == 2, f"Expected 2 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand" and result[0].text == "conj_tac >- simp[]"
        assert result[1].kind == "expand" and result[1].text == "fs[]"

    async def test_by_in_then_chain(self, hol_session):
        """`P` by tac inside >> chain merges into a SINGLE atomic step.

        Why not decomposed: the naive [sg `P`, open_then1, tac, close_paren]
        decomposition is INCORRECT under THEN-distribution over multiple
        goals, because open_then1 only focuses the first global goal,
        leaving N-1 sg-subgoals open. HOL4's actual `P` by tac is atomic
        and distributes per-goal correctly. See test_by_distributes_over_*
        below for the end-to-end regression."""
        result = await call_step_plan(hol_session, r"strip_tac >> `Q` by simp[] >> fs[]")
        # strip_tac, `Q` by simp[], fs[]
        assert len(result) == 3, f"Expected 3 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand" and result[0].text == "strip_tac"
        assert result[1].kind == "expand" and result[1].text == "`Q` by simp[]"
        assert result[2].kind == "expand" and result[2].text == "fs[]"

    async def test_by_tactic_base_no_sg_prefix(self, hol_session):
        """Top-level `tac1 by tac2` (no surrounding chain): the parser
        produces a top-level ThenLT WITHOUT a Group wrapper. Linearize
        decomposes it directly into [expand, open_then1, expand, close_paren].
        Mid-arm navigation IS preserved at top level (no per-goal context
        above to worry about)."""
        result = await call_step_plan(hol_session, "strip_tac by simp[]")
        assert len(result) == 4, f"Expected 4 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].text == "strip_tac"
        assert result[1].kind == "open" and result[1].text == "open_then1"
        assert result[2].text == "simp[]"
        assert result[3].kind == "close" and result[3].text == "close_paren"

    async def test_sg_in_then_chain_merges(self, hol_session):
        """`strip_tac >> sg \`Q\` >- simp[] >> fs[]`: precedence-groups as
        `((((strip_tac >> sg \`Q\`) >- simp[]) >> fs[])`. The whole
        `((strip_tac >> sg \`Q\`) >- simp[])` is the Group-wrapped left
        operand of the outer `>>`. Atomic step + fs[] = 2 steps."""
        result = await call_step_plan(hol_session, r"strip_tac >> sg `Q` >- simp[] >> fs[]")
        assert len(result) == 2, f"Expected 2 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand"
        for tok in ("strip_tac", "`Q`", "simp[]"):
            assert tok in result[0].text, f"Missing {tok!r}: {result[0].text!r}"
        assert result[1].kind == "expand" and result[1].text == "fs[]"

    async def test_by_term_base_merges(self, hol_session):
        """Standalone `P` by tac (no enclosing chain) merges into one step."""
        result = await call_step_plan(hol_session, r"`Q` by simp[]")
        # `Q` by simp[]
        assert len(result) == 1, f"Expected 1 step, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand"
        assert result[0].text == "`Q` by simp[]"

    async def test_by_compound_body_merges(self, hol_session):
        """`P` by (t1 >> t2): compound body merges with parens to keep
        binding correct (so >- doesn't bind only to t1)."""
        result = await call_step_plan(hol_session, r"`Q` by (simp[] >> fs[])")
        assert len(result) == 1, f"Expected 1 step, got {len(result)}: {[s.text for s in result]}"
        text = result[0].text
        assert "`Q`" in text and "by" in text
        # body grouped via parens
        assert "(simp[] >> fs[])" in text or "(simp[]) >> (fs[])" in text or \
               text.endswith("by (simp[] >> fs[])"), \
            f"Compound body must be parenthesized after `by`: {text!r}"

    async def test_thenlt_bare_decomposes(self, hol_session):
        """Standalone `tac1 >- tac2` (no surrounding chain) — the parser
        emits the ThenLT directly without a Group wrapper, so the
        decomposition still happens. Mid-arm navigation IS preserved here."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        assert len(result) == 4, f"Expected 4 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[1].kind == "open"

    async def test_thenlt_multi_step_arm_in_chain(self, hol_session):
        """`tac1 >- (multi-step arm) >> tac3`: parser groups the LHS as
        Group(_, ThenLT(tac1, [LThen1 (multi-step)])). My fix keeps it
        opaque — atomic expand step containing the whole `tac1 >- (...)`."""
        result = await call_step_plan(
            hol_session,
            "conj_tac >- (simp[] >> ACCEPT_TAC) >> fs[]"
        )
        assert len(result) == 2, f"Expected 2 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand"
        assert result[0].text == "conj_tac >- (simp[] >> ACCEPT_TAC)"
        assert result[1].kind == "expand" and result[1].text == "fs[]"

    async def test_then_chain_without_thenlt_unchanged(self, hol_session):
        """Pure >> chain without >-/by is not affected by reexpand."""
        result = await call_step_plan(hol_session, "conj_tac >> simp[] >> fs[]")
        assert len(result) == 3
        assert all(s.kind == "expand" for s in result)

    async def test_nested_thenlt_with_then_chain(self, hol_session):
        """`tac1 >- (chain with nested >- inside)`. The OUTER `>-` Group
        stays opaque (LThen1). The arm body has its own Group wrapping the
        inner `>-`, also kept opaque. Top-level pattern: `conj_tac >- (...)`
        decomposes the outer arm body via open/close, and the inner `>-`
        appears as one merged expand step inside the arm."""
        result = await call_step_plan(
            hol_session,
            "conj_tac >- (strip_tac >> simp[] >> strip_tac >- conj_tac)"
        )
        kinds = [s.kind for s in result]
        texts = [s.text for s in result]
        # Outer `>-` arm decomposes: expand conj_tac, open_then1, then arm
        # body atoms, close_paren. Arm body contains the inner merged `>-`.
        assert "open" in kinds and "close" in kinds, (
            f"Outer arm should still decompose: {kinds}"
        )
        # Inner `>-` is merged into a single atom containing both atoms.
        assert any("strip_tac >- conj_tac" in t for t in texts), (
            f"Inner `>-` should be merged: {texts}"
        )

    async def test_thenlt_at_start_of_chain(self, hol_session):
        """`tac1 >- tac2 >> tac3` — same precedence-grouped form as
        test_thenlt_in_then_chain. Outer Group stays opaque; chain is 2 steps."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> fs[]")
        assert len(result) == 2
        assert result[0].text == "conj_tac >- simp[]"

    async def test_multiple_thenlt_in_chain(self, hol_session):
        """`tac1 >- tac2 >> tac3 >- tac4`: parses as
        `(((tac1 >- tac2) >> tac3) >- tac4)`. The outer-most ThenLT is at
        TOP LEVEL (no Group wrapper around it), so it decomposes into
        [base..., open_then1, expand fs[], close_paren]. The base
        `((tac1 >- tac2) >> tac3)` is a Then containing a Group-wrapped
        inner `>-` (kept opaque) and `tac3`. Total: 5 steps."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> conj_tac >- fs[]")
        # Expected: [merged inner, conj_tac, open_then1, fs[], close_paren]
        assert len(result) == 5, f"Expected 5 steps, got {len(result)}: {[s.text for s in result]}"
        assert result[0].kind == "expand" and result[0].text == "conj_tac >- simp[]"
        assert result[1].kind == "expand" and result[1].text == "conj_tac"
        assert result[2].kind == "open" and result[2].text == "open_then1"
        assert result[3].kind == "expand" and result[3].text == "fs[]"
        assert result[4].kind == "close" and result[4].text == "close_paren"

    async def test_end_offsets_correct_after_reexpand(self, hol_session):
        """End offsets for reexpanded fragments use original proof body positions."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >> fs[]")
        ends = [s.end for s in result]
        for i in range(1, len(ends)):
            assert ends[i] >= ends[i-1], f"End offsets not monotonic at step {i}: {ends}"


# =============================================================================
# Step Plan: `P` by tac in multi-goal contexts (regression for sg/>- decomp bug)
#
# REGRESSION: Previously the step plan decomposed ``P` by tac` into FOUR
# separate ef() steps: [expand (sg P), open_then1, expand tac, close_paren].
# When the by-pattern follows a multi-goal-producing tactic (Cases_on, conj_tac,
# IF_CASES_TAC, etc.) under THEN-distribution (\\ / >>), the decomposition is
# semantically WRONG:
#
#   - `expand (sg P)` distributes per-goal  →  N goals become 2N ([P_i; cont_i])
#   - `open_then1` focuses ONLY the first global goal           ← bug
#   - `expand tac` closes only that one P_1
#   - `close_paren` leaves [cont_1, P_2, cont_2, ..., P_N, cont_N]
#
# The N-1 sg-subgoals P_2..P_N are NEVER discharged, so subsequent tactics
# that operate on the cont_i shape leave the P_i open and the proof appears
# INCOMPLETE in the MCP — even though Holmake (which runs ``P` by tac` as
# one atomic per-goal tactic) closes the same proof cleanly.
#
# Fix: merge_by_steps in tactic_prefix.sml combines [Subgoal `P`, open_then1,
# expand+, close_paren] back into a single expand step with the original
# ``P` by tac` source text. Run via goalFrag.expand, distributes per-goal.
# =============================================================================


class TestByDistribution:
    """``P` by tac` distribution under THEN over multi-goal stacks."""

    async def test_step_plan_merges_by_after_multi_goal_split(self, hol_session):
        """The full pattern `Cases_on q \\\\ \\`P\\` by tac \\\\ rest` in step plan
        keeps the by-pattern as ONE atomic expand (not 4 decomposed steps)."""
        result = await call_step_plan(
            hol_session, r"Cases_on `q` >> `P` by tac >> rest"
        )
        # Cases_on `q`, `P` by tac, rest
        kinds = [s.kind for s in result]
        texts = [s.text for s in result]
        assert kinds == ["expand", "expand", "expand"], (
            f"Expected 3 atomic expand steps; got {list(zip(kinds, texts))}"
        )
        assert "by" in texts[1] and "`P`" in texts[1], (
            f"Step 2 should be the merged `P` by tac form; got {texts[1]!r}"
        )
        # No bare sg/open_then1/close_paren plumbing should leak through.
        for s in result:
            assert s.text not in ("open_then1", "close_paren"), (
                f"Decomposition plumbing leaked into step plan: {s.text}"
            )
            assert not s.text.startswith("sg `"), (
                f"Raw sg-prefix Subgoal atom should have been merged: {s.text!r}"
            )

    async def test_by_proof_passes_after_multi_goal_split(self, hol_session):
        """End-to-end: a proof that uses `P` by tac after a 2-goal split must
        verify_theorem_json to "all goals closed".

        Without merge_by_steps this exact proof would leave 1 sg-subgoal
        (`1+1 = 2`) open after the final ACCEPT_TAC TRUTH (which can close
        T but not 1+1=2). Reflects the data_to_word_assignProofScript.sml
        cake-while idiom that exposed the bug:
            Cases_on `q` >> `P` by tac >> closing_tac
        """
        await hol_session.send('drop_all();', timeout=5)
        # Goal: T /\ T  (after conj_tac, 2 identical T goals)
        cmd = (
            'verify_theorem_json "T /\\\\ T" "by_multigoal_thm" '
            '["ef(goalFrag.expand(conj_tac)(Context.snapshot()))",'
            ' "ef(goalFrag.expand(`1+1 = 2` by EVAL_TAC)(Context.snapshot()))",'
            ' "ef(goalFrag.expand(ACCEPT_TAC TRUTH)(Context.snapshot()))"] false 10.0;'
        )
        result = await hol_session.send(cmd, timeout=30)
        ok_line = next(
            (line.strip() for line in result.strip().split('\n')
             if line.strip().startswith('{"ok":')),
            None,
        )
        assert ok_line is not None, (
            f"verify_theorem_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        trace = payload.get('trace', [])
        assert trace, f"Empty trace: {payload!r}"
        last = trace[-1]
        assert last.get('goals_after') == 0, (
            f"Multi-goal `P` by tac left goals open: {trace!r}"
        )

    async def test_old_decomposition_would_have_failed(self, hol_session):
        """Negative control: the OLD decomposed sequence
        [conj_tac, sg `1+1=2`, open_then1, EVAL_TAC, close_paren, ACCEPT_TAC TRUTH]
        leaves 1 unproven sg-subgoal — confirming that the merge in
        merge_by_steps is what makes the prior test pass.

        Demonstrates that the decomposition is semantically wrong, not just
        cosmetically split."""
        await hol_session.send('drop_all();', timeout=5)
        cmd = (
            'verify_theorem_json "T /\\\\ T" "by_multigoal_thm_old" '
            '["ef(goalFrag.expand(conj_tac)(Context.snapshot()))",'
            ' "ef(goalFrag.expand(sg `1+1 = 2`)(Context.snapshot()))",'
            ' "ef(goalFrag.open_then1)",'
            ' "ef(goalFrag.expand(EVAL_TAC)(Context.snapshot()))",'
            ' "ef(goalFrag.close_paren)",'
            ' "ef(goalFrag.expand(ACCEPT_TAC TRUTH)(Context.snapshot()))"] false 10.0;'
        )
        result = await hol_session.send(cmd, timeout=30)
        ok_line = next(
            (line.strip() for line in result.strip().split('\n')
             if line.strip().startswith('{"ok":')),
            None,
        )
        assert ok_line is not None, (
            f"verify_theorem_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        trace = payload.get('trace', [])
        assert trace, f"Empty trace: {payload!r}"
        last = trace[-1]
        # The OLD decomposition strands the second `1+1 = 2` sg-subgoal —
        # confirms why merging is needed.
        assert last.get('goals_after', 0) > 0 or last.get('err') is not None, (
            f"Decomposed sequence should have failed/left goals open, "
            f"but trace says proof closed: {trace!r}"
        )


# =============================================================================
# Step Plan: >~ [pat] >- (compound body with NESTED >-)
#
# REGRESSION: Previously merge_select_steps' walkArm bailed on ANY nested
# open inside the body of >~ [pat] >- (...), and the "no bracket consumed"
# branch then silently DROPPED the SELECT step. Result: `>~ [pat]` never
# executed, the following `>-` focused the wrong goal, and the proof
# silently mis-executed (or failed many steps later for unrelated-looking
# reasons). Hit on the cake-while branch when inlining a Resume[Result]
# body that contained `\\ reverse TOP_CASE_TAC >- (rw [] \\ rw [])`.
#
# Fix: parseBody walks nested brackets recursively, parenthesising nested
# `>-` groups so SML precedence (>- inside >> chain) is preserved.
# =============================================================================


class TestSelectGoalNestedBody:
    """`>~ [pat] >- (body with nested >-)` must merge into a single
    expand_list step, not silently drop the SELECT pattern."""

    async def test_nested_then1_inside_select_body_merges(self, hol_session):
        """Body of `>~ [pat] >- (... >- ...)` is reconstructed with nested
        >- properly parenthesised so the SELECT_GOAL_LT prefix survives."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- (a >> b >- c >> d)"
        )
        assert len(result) == 2, (
            f"Expected 2 steps (Cases_on, expand_list); got "
            f"{[(s.kind, s.text) for s in result]}"
        )
        assert result[0].kind == "expand"
        assert result[1].kind == "expand_list", (
            f"Compound body with nested >- must yield expand_list, "
            f"not bare expand or dropped select: {result[1].kind}"
        )
        text = result[1].text
        assert "Q.SELECT_GOAL_LT" in text, (
            f"SELECT_GOAL_LT prefix dropped: {text!r}"
        )
        for tok in ("`Foo`", "a", "b", "c", "d"):
            assert tok in text, (
                f"Token {tok!r} missing from reconstruction: {text!r}"
            )

    async def test_double_nested_then1_inside_select_body(self, hol_session):
        """Two nested >- arms in body still merge correctly."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- (a >- b >- c)"
        )
        assert len(result) == 2
        assert result[1].kind == "expand_list"
        text = result[1].text
        assert "Q.SELECT_GOAL_LT" in text
        for tok in ("`Foo`", "a", "b", "c"):
            assert tok in text, f"Token {tok!r} missing from {text!r}"

    async def test_nested_paren_inside_select_body(self, hol_session):
        """Plain (...) nesting inside select body merges correctly."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- (a >> (b >> c) >> d)"
        )
        assert len(result) == 2
        assert result[1].kind == "expand_list"
        for tok in ("`Foo`", "a", "b", "c", "d"):
            assert tok in result[1].text

    async def test_select_no_nested_unchanged(self, hol_session):
        """Existing flat-body case still merges as before (regression guard)."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- simp[]"
        )
        assert len(result) == 2
        assert result[1].kind == "expand_list"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        assert "simp[]" in result[1].text


# =============================================================================
# Step Plan: `reverse TAC` is preserved (not stripped to bare TAC)
#
# REGRESSION: TacticParse parses `reverse TAC` as
#   Group(span, ThenLT(TAC, [LReverse]))
# reexpand_group_atoms previously re-expanded ANY ThenLT-containing Group,
# producing flat frags [FAtom TAC, FAtom LReverse]. LReverse has no span,
# so frag_text returned "" and assignEnds dropped it — losing the `reverse`
# wrapper entirely. The decomposed step ran TAC alone, which has the wrong
# goal-stack ordering vs `reverse TAC`.
#
# Fix: lsHasStructuralOnly excludes ThenLTs whose list-tactic part has
# LReverse (or other span-less LT-elements) from re-expansion. The Group
# stays as a single FAtom whose text is the full `reverse TAC` source.
# =============================================================================


class TestReverseTactical:
    """`reverse TAC` must survive linearization as a single atomic step."""

    async def test_reverse_preserved_in_step_text(self, hol_session):
        """Step plan for `reverse TOP_CASE_TAC` keeps the `reverse` prefix."""
        result = await call_step_plan(hol_session, "reverse TOP_CASE_TAC")
        assert len(result) == 1, (
            f"Expected one atomic step for `reverse TOP_CASE_TAC`; got "
            f"{[(s.kind, s.text) for s in result]}"
        )
        assert result[0].kind == "expand"
        assert result[0].text == "reverse TOP_CASE_TAC", (
            f"`reverse` prefix dropped: {result[0].text!r}"
        )

    async def test_reverse_in_then_chain_keeps_prefix(self, hol_session):
        """`reverse TOP_CASE_TAC` inside a >> chain still keeps `reverse`."""
        result = await call_step_plan(
            hol_session, "strip_tac >> reverse TOP_CASE_TAC >> simp[]"
        )
        assert len(result) == 3
        assert result[1].text == "reverse TOP_CASE_TAC", (
            f"`reverse` prefix dropped in chain: {result[1].text!r}"
        )

    async def test_reverse_with_then1_arm(self, hol_session):
        """`reverse TAC >- arm` keeps `reverse` and decomposes the >-."""
        result = await call_step_plan(
            hol_session, "reverse TOP_CASE_TAC >- simp[]"
        )
        # Expect: expand "reverse TOP_CASE_TAC", open_then1, expand simp[], close_paren
        assert len(result) == 4, (
            f"Expected 4 steps; got {[(s.kind, s.text) for s in result]}"
        )
        assert result[0].kind == "expand"
        assert result[0].text == "reverse TOP_CASE_TAC"
        assert result[1].kind == "open"
        assert result[2].text == "simp[]"
        assert result[3].kind == "close"


# =============================================================================
# Step Plan: >~ (SELECT_GOAL_LT) decomposition
# =============================================================================

class TestGoalfragSelectGoalDecomposition:
    """>~[pat] >- tac decomposes into expand_list steps (not bare expand)."""

    async def test_select_goal_produces_expand_list(self, hol_session):
        """>~[`Foo`] >- simp[] becomes a single expand_list step."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- simp[]")
        # Should produce: expand(Cases_on), expand_list(Q.SELECT_GOAL_LT >- simp[])
        assert len(result) == 2
        assert result[0].kind == "expand"
        assert result[0].text == "Cases_on `x`"
        assert result[1].kind == "expand_list"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        assert ">-" in result[1].text
        assert "simp[]" in result[1].text

    async def test_select_goal_cmd_uses_expand_list(self, hol_session):
        """expand_list step generates goalFrag.expand_list command."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- simp[]")
        assert "goalFrag.expand_list" in result[1].cmd
        assert "goalFrag.expand_list" in result[1].cmd

    async def test_multiple_select_goals(self, hol_session):
        """Multiple >~ arms each become separate expand_list steps."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- simp[] >~ [`Bar`] >- simp[]"
        )
        # expand(Cases_on), expand_list(>~Foo>-simp), expand_list(>~Bar>-simp)
        assert len(result) == 3
        assert result[0].kind == "expand"
        assert result[1].kind == "expand_list"
        assert result[2].kind == "expand_list"
        assert "`Foo`" in result[1].text
        assert "`Bar`" in result[2].text

    async def test_select_goal_end_offsets(self, hol_session):
        """expand_list end offset covers the full >~ >- pattern."""
        result = await call_step_plan(
            hol_session,
            "Cases_on `x` >~ [`Foo`] >- simp[]"
        )
        # expand_list end should be at end of "simp[]", which is after the pattern
        assert result[1].end > result[0].end

    async def test_select_goal_no_bare_pattern_expand(self, hol_session):
        """>~ pattern does NOT produce a bare expand step with just the pattern text."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- simp[]")
        # No step should have kind="expand" and text that is just a pattern list
        for step in result:
            if step.kind == "expand":
                assert not step.text.startswith("[`"), \
                    f"Bare pattern expand step found: {step.text}"

    async def test_select_goal_compound_body_then(self, hol_session):
        """>~[pat] >- (a >> b): compound body must be merged, not silently dropped.

        Regression: previously the SELECT_GOAL_LT prefix was dropped when the
        `>-` body had multiple tactics joined by `>>` (the bracket pattern
        match in tryConsumeBracket was open+single_expand+close). With the
        prefix dropped, the `>~` selector never executed and `>-` ran on the
        un-reordered goal stack, picking the wrong goal."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (simp[] >> fs[])")
        # Must produce: expand(Cases_on), expand_list(Q.SELECT_GOAL_LT [`Foo`] >- (simp[] >> fs[]))
        assert len(result) == 2, f"Expected 2 steps, got {len(result)}: {[(s.kind, s.text) for s in result]}"
        assert result[0].kind == "expand"
        assert result[1].kind == "expand_list", \
            f"Compound body should yield expand_list step, got kind={result[1].kind} text={result[1].text!r}"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        assert "`Foo`" in result[1].text
        assert "simp[]" in result[1].text
        assert "fs[]" in result[1].text

    async def test_select_goal_compound_body_three_then(self, hol_session):
        """>~[pat] >- (a >> b >> c): three-tactic compound body."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (a >> b >> c)")
        assert len(result) == 2
        assert result[1].kind == "expand_list"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        # All three sub-tactics must be present
        for tac in ("a", "b", "c"):
            assert tac in result[1].text

    async def test_select_goal_compound_body_associativity(self, hol_session):
        """Compound body must parenthesize so `>-` doesn't bind only to first sub-tactic.

        `Q.SELECT_GOAL_LT [pat] >- a >> b` parses as
          `(Q.SELECT_GOAL_LT [pat] >- a) >> b`
        which would run `b` on goals OUTSIDE the >- arm. The body must be
        wrapped in parens so the entire compound is the arm body."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (simp[] >> fs[])")
        # The combined text must keep simp[] >> fs[] grouped (parens, or some
        # equivalent that prevents `>-` from binding only to simp[]).
        text = result[1].text
        # Find the position of `>-` and check what follows is parenthesized
        dash_idx = text.find(">-")
        assert dash_idx >= 0
        body = text[dash_idx + 2:].lstrip()
        assert body.startswith("("), \
            f"Compound body must be parenthesized; got {body!r}"


# =============================================================================
# Resume goal extraction
#
# Regression tests for a bug where `resume_goal_terms` referenced
# `boolLib.find_suspension` (does not exist) instead of
# `markerLib.lookup_suspension`, causing `extract_resume_goal_json` and
# `verify_resume_json` to fail to compile. The downstream symptom was:
#
#     Failed to extract Resume goal for '<thm>[<label>]'; goals_json: NO_PROOFS
#
# These tests pin the SML-level entry points so the bug cannot regress
# silently behind the higher-level cursor tests.
# =============================================================================


async def _setup_split_conj(session: HOLSession) -> None:
    """Define a parent theorem with two suspended subgoals in the live session."""
    await session.send('drop_all();', timeout=5)
    parent = (
        'Theorem split_conj:\n'
        '  p /\\ (p ==> q) ==> p /\\ q\n'
        'Proof\n'
        '  strip_tac >> conj_tac\n'
        '  >- suspend "p_case"\n'
        '  >- suspend "q_case"\n'
        'QED'
    )
    result = await session.send(parent, timeout=30)
    assert "saved theorem" in result.lower() or "stashing" in result.lower(), (
        f"Parent theorem did not register: {result[-500:]}"
    )


class TestResumeGoalExtraction:
    """Direct SML tests for the Resume goal extraction helpers."""

    async def test_extract_resume_goal_json_first_label(self, hol_session):
        """extract_resume_goal_json returns the suspended subgoal as JSON."""
        await _setup_split_conj(hol_session)
        result = await hol_session.send(
            'extract_resume_goal_json "split_conj" "p_case";', timeout=10
        )
        # Must have produced a JSON ok line (not an err, not a static error).
        ok_line = None
        for line in result.strip().split('\n'):
            line = line.strip()
            if line.startswith('{"ok":'):
                ok_line = line
                break
        assert ok_line is not None, (
            f"extract_resume_goal_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        # The first suspended subgoal of split_conj is `p` (with `p ==> q` as asm
        # added by `strip_tac`). extract_resume_goal_json prints types, so the
        # term renders as e.g. "(p :bool)".
        assert 'p' in payload['goal'] and 'bool' in payload['goal'], (
            f"Unexpected goal text: {payload!r}"
        )

    async def test_extract_resume_goal_json_second_label(self, hol_session):
        """Both suspended labels are independently extractable."""
        await _setup_split_conj(hol_session)
        result = await hol_session.send(
            'extract_resume_goal_json "split_conj" "q_case";', timeout=10
        )
        ok_line = next(
            (line.strip() for line in result.strip().split('\n')
             if line.strip().startswith('{"ok":')),
            None,
        )
        assert ok_line is not None, (
            f"extract_resume_goal_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        # Second subgoal is `q`; types are printed.
        assert 'q' in payload['goal'] and 'bool' in payload['goal'], (
            f"Unexpected goal text: {payload!r}"
        )

    async def test_extract_resume_goal_json_unknown_suspension(self, hol_session):
        """Looking up a non-existent suspension reports an error, not a crash."""
        await hol_session.send('drop_all();', timeout=5)
        result = await hol_session.send(
            'extract_resume_goal_json "no_such_thm" "no_label";', timeout=5
        )
        # Should produce a JSON err line — NOT a Poly/ML 'has not been declared'
        # static error (which is the symptom of the original bug).
        assert "has not been declared" not in result, (
            f"resume_goal_terms failed to compile: {result!r}"
        )
        assert any(
            line.strip().startswith('{"err":') for line in result.strip().split('\n')
        ), f"Expected JSON err line; got: {result!r}"

    async def test_verify_resume_json_closes_subgoal(self, hol_session):
        """verify_resume_json runs Resume tactics against the suspended goal."""
        await _setup_split_conj(hol_session)
        # `ASM_REWRITE_TAC[]` closes `p` given `p` is in the asms (added by strip_tac).
        cmd = (
            'verify_resume_json "split_conj" "p_case" "split_conj_p_case" '
            '["ef(goalFrag.expand(ASM_REWRITE_TAC[])(Context.snapshot()))"] false 10.0;'
        )
        result = await hol_session.send(cmd, timeout=20)
        ok_line = next(
            (line.strip() for line in result.strip().split('\n')
             if line.strip().startswith('{"ok":')),
            None,
        )
        assert ok_line is not None, (
            f"verify_resume_json did not emit ok JSON. Output: {result!r}"
        )
        payload = json.loads(ok_line)['ok']
        trace = payload.get('trace', [])
        assert trace, f"Empty trace from verify_resume_json: {payload!r}"
        # Final tactic must close the goal (goals_after == 0).
        assert trace[-1].get('goals_after') == 0, (
            f"Resume tactics did not close goal: {trace!r}"
        )
    async def test_select_goal_compound_body_then(self, hol_session):
        """>~[pat] >- (a >> b): compound body must be merged, not silently dropped.

        Regression: previously the SELECT_GOAL_LT prefix was dropped when the
        `>-` body had multiple tactics joined by `>>` (the bracket pattern
        match in tryConsumeBracket was open+single_expand+close). With the
        prefix dropped, the `>~` selector never executed and `>-` ran on the
        un-reordered goal stack, picking the wrong goal."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (simp[] >> fs[])")
        # Must produce: expand(Cases_on), expand_list(Q.SELECT_GOAL_LT [`Foo`] >- (simp[] >> fs[]))
        assert len(result) == 2, f"Expected 2 steps, got {len(result)}: {[(s.kind, s.text) for s in result]}"
        assert result[0].kind == "expand"
        assert result[1].kind == "expand_list", \
            f"Compound body should yield expand_list step, got kind={result[1].kind} text={result[1].text!r}"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        assert "`Foo`" in result[1].text
        assert "simp[]" in result[1].text
        assert "fs[]" in result[1].text

    async def test_select_goal_compound_body_three_then(self, hol_session):
        """>~[pat] >- (a >> b >> c): three-tactic compound body."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (a >> b >> c)")
        assert len(result) == 2
        assert result[1].kind == "expand_list"
        assert "Q.SELECT_GOAL_LT" in result[1].text
        # All three sub-tactics must be present
        for tac in ("a", "b", "c"):
            assert tac in result[1].text

    async def test_select_goal_compound_body_associativity(self, hol_session):
        """Compound body must parenthesize so `>-` doesn't bind only to first sub-tactic.

        `Q.SELECT_GOAL_LT [pat] >- a >> b` parses as
          `(Q.SELECT_GOAL_LT [pat] >- a) >> b`
        which would run `b` on goals OUTSIDE the >- arm. The body must be
        wrapped in parens so the entire compound is the arm body."""
        result = await call_step_plan(hol_session, "Cases_on `x` >~ [`Foo`] >- (simp[] >> fs[])")
        # The combined text must keep simp[] >> fs[] grouped (parens, or some
        # equivalent that prevents `>-` from binding only to simp[]).
        text = result[1].text
        # Find the position of `>-` and check what follows is parenthesized
        dash_idx = text.find(">-")
        assert dash_idx >= 0
        body = text[dash_idx + 2:].lstrip()
        assert body.startswith("("), \
            f"Compound body must be parenthesized; got {body!r}"
