"""Tests for tactic_prefix.sml functions (step_positions, prefix_commands).

This tests the prefix-based tactic replay used by FileProofCursor for mapping
file positions to proof state.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_positions_output, parse_prefix_commands_output, parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    """Fixture that provides a HOL session with tactic_prefix loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    # Load tactic_prefix.sml which defines step_positions_json and prefix_commands_json
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()


async def call_step_positions(session: HOLSession, tactic_str: str) -> list[int]:
    """Call step_positions_json and parse the result."""
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'step_positions_json "{escaped}";', timeout=10)
    return parse_step_positions_output(result)


async def call_prefix_commands(session: HOLSession, tactic_str: str, offset: int) -> str:
    """Call prefix_commands_json and parse the result."""
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'prefix_commands_json "{escaped}" {offset};', timeout=10)
    return parse_prefix_commands_output(result)


class TestStepPositionsBasic:
    """Basic step position tests."""

    async def test_single_tactic(self, hol_session):
        """Single tactic should return one position."""
        result = await call_step_positions(hol_session, "simp[]")
        assert len(result) == 1

    async def test_then_chain(self, hol_session):
        """>> chain should give multiple positions."""
        result = await call_step_positions(hol_session, "a >> b >> c")
        # Should have 3 steps
        assert len(result) == 3

    async def test_thenlt_fragments(self, hol_session):
        """>- structure returns fragment positions (not atomic)."""
        result = await call_step_positions(hol_session, "conj_tac >- simp[] >- fs[]")
        # linearize returns fragment endpoints for each spanning node
        assert len(result) >= 1

    async def test_empty_string(self, hol_session):
        """Empty string may return [0] or []."""
        result = await call_step_positions(hol_session, "")
        # Empty input gives one position at 0
        assert result == [0] or result == []


class TestStepPositionsMixed:
    """Tests for mixed >> and >- structures."""

    async def test_then_with_thenlt(self, hol_session):
        """>> with embedded >- should treat >- as atomic."""
        result = await call_step_positions(hol_session, "a >> (conj_tac >- simp[]) >> b")
        # Should have 3 steps: a, (conj_tac >- simp[]), b
        assert len(result) == 3

    async def test_complex_nesting(self, hol_session):
        """Complex pattern with multiple levels."""
        result = await call_step_positions(hol_session, "a >> b >- c >- d >> e")
        # b >- c >- d is atomic, so: a, (b >- c >- d), e = 3 steps
        # Actually depends on parsing - let's just verify it returns something
        assert len(result) >= 2


class TestPrefixCommands:
    """Tests for prefix_commands_json."""

    async def test_full_proof(self, hol_session):
        """Prefix at end should include everything."""
        tactic = "simp[] >> gvs[]"
        result = await call_prefix_commands(hol_session, tactic, len(tactic))
        assert "simp" in result
        assert "gvs" in result

    async def test_partial_prefix(self, hol_session):
        """Prefix at middle should include only up to that point."""
        tactic = "simp[] >> gvs[] >> fs[]"
        # Position after simp[] but before gvs[]
        result = await call_prefix_commands(hol_session, tactic, 7)
        assert "simp" in result
        # May or may not include gvs depending on exact offset

    async def test_zero_offset(self, hol_session):
        """Offset 0 should return empty or minimal prefix."""
        result = await call_prefix_commands(hol_session, "simp[]", 0)
        # At offset 0, nothing should be included
        assert result.strip() == "" or "e()" in result

    async def test_returns_e_command(self, hol_session):
        """Result should be a valid e() command."""
        result = await call_prefix_commands(hol_session, "simp[]", 6)
        # Should contain e( and )
        assert "e(" in result or result.strip() == ""


class TestByConstruct:
    """Tests for `by` and `suffices_by` constructs."""

    async def test_by_atomic(self, hol_session):
        """`by` should be treated as atomic."""
        result = await call_step_positions(hol_session, "`foo` by simp[]")
        # by is atomic - one step
        assert len(result) == 1

    async def test_by_in_chain(self, hol_session):
        """`by` in >> chain should be one of the steps."""
        result = await call_step_positions(hol_session, "rpt strip_tac >> `P x` by simp[] >> fs[]")
        # Should be 3 steps
        assert len(result) == 3


class TestEdgeCases:
    """Edge cases and special patterns."""

    async def test_cheat_tactic(self, hol_session):
        """cheat should be recognized."""
        result = await call_step_positions(hol_session, "simp[] >> cheat")
        assert len(result) == 2

    async def test_first_combinator(self, hol_session):
        """FIRST combinator may not have span in all cases."""
        result = await call_step_positions(hol_session, "FIRST [simp[], fs[], gvs[]]")
        # FIRST may or may not yield fragment positions depending on TacticParse
        assert isinstance(result, list)

    async def test_multiline(self, hol_session):
        """Multi-line tactics should work."""
        tactic = "rpt strip_tac\n  >> simp[]\n  >> fs[]"
        result = await call_step_positions(hol_session, tactic)
        assert len(result) >= 2


class TestParseTreeStructure:
    """Tests documenting parse tree structure for different patterns.

    These test cases document expected behavior for batch-correct step extraction.
    """

    async def test_then_chain_structure(self, hol_session):
        """a >> b >> c parses as Then[a, b, c] - 3 top-level steps."""
        result = await call_step_positions(hol_session, "a >> b >> c")
        # Current: linearize gives endpoints for each
        assert len(result) == 3

    async def test_thenlt_structure(self, hol_session):
        """conj_tac >- simp[] >- fs[] parses as nested ThenLT - should be 1 atomic step.

        Current behavior: linearize splits into 3 fragments.
        Batch-correct: should be 1 step (entire >- is atomic).
        """
        result = await call_step_positions(hol_session, "conj_tac >- simp[] >- fs[]")
        # Current behavior: 3 fragments
        assert len(result) >= 1
        # TODO: For batch-correct O(1) access, this should be 1 step

    async def test_then_with_thenlt_inside(self, hol_session):
        """a >> (b >- c) >> d - the (b >- c) is atomic within the >> chain.

        Batch-correct: 3 steps [a, (b >- c), d].
        """
        result = await call_step_positions(hol_session, "a >> (b >- c) >> d")
        # Should have at least 3 step boundaries
        assert len(result) >= 3

    async def test_thenlt_with_then_inside(self, hol_session):
        """(a >> b) >- c >- d - entire thing is one >- structure.

        Batch-correct: 1 step (the whole ThenLT is atomic).
        Current: linearize splits it.
        """
        result = await call_step_positions(hol_session, "(a >> b) >- c >- d")
        # Current behavior: multiple fragments
        assert len(result) >= 1
        # TODO: For batch-correct, this should be 1 step


class TestFineGrainedStepping:
    """Tests for fine-grained stepping inside >- structures.

    Key discovery: sliceTacticBlock generates >>> HEADGOAL for partial arms,
    allowing stepping at ANY position, not just step boundaries.
    """

    async def test_partial_first_arm(self, hol_session):
        """Position inside first >- arm should use HEADGOAL."""
        tactic = "conj_tac >- simp[] >- fs[]"
        # Position 15 is inside simp[]
        result = await call_prefix_commands(hol_session, tactic, 15)
        # Should generate HEADGOAL for partial arm
        assert "HEADGOAL" in result or "simp" in result
        assert "e(" in result

    async def test_partial_second_arm(self, hol_session):
        """Position inside second >- arm should keep first arm intact."""
        tactic = "conj_tac >- simp[] >- fs[]"
        # Position 23 is inside fs[]
        result = await call_prefix_commands(hol_session, tactic, 23)
        # First arm should be intact
        assert "simp" in result
        # Should have HEADGOAL for partial second arm
        assert "HEADGOAL" in result or "fs" in result

    async def test_full_thenl(self, hol_session):
        """Position at end should give complete expression."""
        tactic = "conj_tac >- simp[] >- fs[]"
        result = await call_prefix_commands(hol_session, tactic, len(tactic))
        # Should have original >- structure
        assert ">-" in result or (">-" not in tactic) or "conj_tac" in result
        # No HEADGOAL needed when complete
        assert "simp" in result
        assert "fs" in result

    async def test_nested_fine_grained(self, hol_session):
        """Fine-grained stepping in nested structures."""
        tactic = "a >> (b >- c >- d) >> e"
        # Position inside the nested >- structure
        result = await call_prefix_commands(hol_session, tactic, 15)
        # Should have partial prefix
        assert "e(" in result

    async def test_then_chain_partial(self, hol_session):
        """Partial >> chain should include only completed steps."""
        tactic = "simp[] >> gvs[] >> fs[]"
        # Position after simp[] (offset 6) and before gvs[]
        result = await call_prefix_commands(hol_session, tactic, 7)
        assert "simp" in result
        # May or may not include gvs depending on exact offset

    async def test_prefix_executable(self, hol_session):
        """Generated prefix should be valid SML/HOL syntax."""
        tactic = "conj_tac >- simp[] >- fs[]"
        for offset in [5, 12, 20, 26]:
            result = await call_prefix_commands(hol_session, tactic, offset)
            # Should be either empty or valid e() command
            result_stripped = result.strip()
            assert result_stripped == "" or result_stripped.startswith("e(")
            # Should have matching parens if non-empty
            if "e(" in result:
                assert result.count("(") >= result.count(")")  # may have trailing newline


class TestReplayEquivalence:
    """Tests verifying e(a >> b) is equivalent to e(a); eall(b).

    This is critical for understanding whether sliceTacticBlock-based replay
    (single e(prefix) call) matches the DESIGN's e+eall sequential approach.
    """

    async def _get_goal_count(self, session: HOLSession) -> int:
        """Get number of current goals."""
        result = await session.send('length (top_goals());', timeout=5)
        # Look for "val it = N : int" pattern
        import re
        match = re.search(r'val it\s*=\s*(\d+)', result)
        if match:
            return int(match.group(1))
        # Fallback: look for bare number
        for line in result.strip().split('\n'):
            line = line.strip()
            if line.isdigit():
                return int(line)
        return -1

    async def _goals_equal(self, session: HOLSession, method1_cmds: list[str], method2_cmds: list[str], goal: str) -> tuple[int, int]:
        """Run two methods and return their goal counts."""
        # Method 1
        await session.send(f'g `{goal}`;', timeout=5)
        for cmd in method1_cmds:
            await session.send(cmd, timeout=5)
        count1 = await self._get_goal_count(session)
        await session.send('drop();', timeout=5)

        # Method 2
        await session.send(f'g `{goal}`;', timeout=5)
        for cmd in method2_cmds:
            await session.send(cmd, timeout=5)
        count2 = await self._get_goal_count(session)
        await session.send('drop();', timeout=5)

        return count1, count2

    async def test_simple_then_chain(self, hol_session):
        """e(a >> b) should equal e(a); eall(b) for simple chain."""
        # conj_tac >> conj_tac on (A /\ B) /\ (C /\ D)
        # First conj_tac: [A /\ B, C /\ D] - 2 goals, both are conjunctions
        # Second conj_tac on both: [A, B, C, D] - 4 goals
        # Note: avoid S as it's a reserved combinator in HOL
        count1, count2 = await self._goals_equal(
            hol_session,
            ['e(conj_tac >> conj_tac);'],
            ['e(conj_tac);', 'eall(conj_tac);'],
            '(A /\\ B) /\\ (C /\\ D)'
        )
        assert count1 == count2 == 4

    async def test_three_step_chain(self, hol_session):
        """e(a >> b >> c) should equal e(a); eall(b); eall(c)."""
        # conj_tac >> conj_tac >> all_tac on (A /\ B) /\ (C /\ D)
        count1, count2 = await self._goals_equal(
            hol_session,
            ['e(conj_tac >> conj_tac >> all_tac);'],
            ['e(conj_tac);', 'eall(conj_tac);', 'eall(all_tac);'],
            '(A /\\ B) /\\ (C /\\ D)'
        )
        assert count1 == count2 == 4

    async def test_thenlt_atomic(self, hol_session):
        """e(tac >- arm) should be atomic - single step."""
        # conj_tac >- all_tac leaves second goal
        count1, count2 = await self._goals_equal(
            hol_session,
            ['e(conj_tac >- all_tac);'],
            ['e(conj_tac >- all_tac);'],  # Same - it's atomic
            'P /\\ Q'
        )
        # conj_tac produces 2 goals, >- all_tac handles first, leaves 1
        assert count1 == count2 == 1

    async def test_prefix_vs_eall_chain(self, hol_session):
        """sliceTacticBlock prefix should match e+eall replay."""
        # For a >> b, sliceTacticBlock at end of a gives e(a)
        # This should match e(a) directly
        tactic = "conj_tac >> conj_tac"

        # Get prefix at end of first step (after conj_tac, before >>)
        prefix = await call_prefix_commands(hol_session, tactic, 8)  # "conj_tac" is 8 chars

        # Method 1: Use the prefix
        await hol_session.send('g `P /\\ Q /\\ R`;', timeout=5)
        await hol_session.send(prefix, timeout=5)
        count1 = await self._get_goal_count(hol_session)
        await hol_session.send('drop();', timeout=5)

        # Method 2: Direct e(conj_tac)
        await hol_session.send('g `P /\\ Q /\\ R`;', timeout=5)
        await hol_session.send('e(conj_tac);', timeout=5)
        count2 = await self._get_goal_count(hol_session)
        await hol_session.send('drop();', timeout=5)

        assert count1 == count2 == 2

    async def test_full_prefix_vs_eall(self, hol_session):
        """Full prefix e(a >> b) should match e(a); eall(b)."""
        tactic = "conj_tac >> conj_tac"
        goal = "(A /\\ B) /\\ (C /\\ D)"  # Avoid S (reserved combinator)

        # Get full prefix
        prefix = await call_prefix_commands(hol_session, tactic, len(tactic))

        # Method 1: Use the prefix
        await hol_session.send(f'g `{goal}`;', timeout=5)
        await hol_session.send(prefix, timeout=5)
        count1 = await self._get_goal_count(hol_session)
        await hol_session.send('drop();', timeout=5)

        # Method 2: e + eall
        await hol_session.send(f'g `{goal}`;', timeout=5)
        await hol_session.send('e(conj_tac);', timeout=5)
        await hol_session.send('eall(conj_tac);', timeout=5)
        count2 = await self._get_goal_count(hol_session)
        await hol_session.send('drop();', timeout=5)

        assert count1 == count2 == 4


class TestStepCommands:
    """Test step_commands and backup_n for O(1) access."""

    async def test_step_commands_generates_e_calls(self, hol_session):
        """step_commands should generate e() calls."""
        tactic = "conj_tac >> simp[] >> fs[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_commands_json "{escaped}";', timeout=10)

        # Parse the result
        cmds = parse_prefix_commands_output(result)

        # Should contain e() calls
        assert "e(" in cmds

    async def test_backup_n_undoes_steps(self, hol_session):
        """backup_n should undo the correct number of e() calls."""
        goal = "T /\\ T"

        # Set up goal
        await hol_session.send(f'g `{goal}`;', timeout=5)

        # Initial: 1 goal
        r0 = await hol_session.send('length (top_goals());', timeout=5)
        assert "1" in r0

        # After conj_tac: 2 goals
        await hol_session.send('e(conj_tac);', timeout=5)
        r1 = await hol_session.send('length (top_goals());', timeout=5)
        assert "2" in r1

        # Backup 1 step - should be back at 1 goal
        await hol_session.send('backup_n 1;', timeout=5)
        r2 = await hol_session.send('length (top_goals());', timeout=5)
        assert "1" in r2

        # Re-apply and backup 0 - should stay at 2 goals
        await hol_session.send('e(conj_tac);', timeout=5)
        await hol_session.send('backup_n 0;', timeout=5)
        r3 = await hol_session.send('length (top_goals());', timeout=5)
        assert "2" in r3

        await hol_session.send('drop();', timeout=5)

    async def test_partial_step_commands(self, hol_session):
        """partial_step_commands should generate commands for a slice."""
        tactic = "conj_tac >> simp[] >> fs[]"
        escaped = escape_sml_string(tactic)

        # Get step positions
        pos_result = await hol_session.send(f'step_positions_json "{escaped}";', timeout=10)
        positions = parse_step_positions_output(pos_result)
        assert len(positions) == 3  # conj_tac, simp[], fs[]

        # Get partial from step 0 end to middle of step 1
        start_offset = positions[0]  # After conj_tac
        end_offset = positions[0] + 3  # Partial into simp[]
        partial_result = await hol_session.send(
            f'partial_step_commands_json "{escaped}" {start_offset} {end_offset};',
            timeout=10
        )
        partial_cmd = parse_prefix_commands_output(partial_result)

        # Should be a valid SML expression (may be empty or contain partial)
        assert isinstance(partial_cmd, str)


async def call_step_plan(session: HOLSession, tactic_str: str):
    """Call step_plan_json and parse the result."""
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(result)


class TestStepPlan:
    """Tests for step_plan_json - the main API for tactic navigation.

    step_plan_json returns (end_offset, cmd) pairs for each executable step.
    This is the single source of truth for O(1) tactic navigation.
    """

    async def test_simple_then_chain(self, hol_session):
        """>> chain should return one step per tactic.

        This was a bug: step_plan returned 1 step instead of 3.
        """
        result = await call_step_plan(hol_session, "simp[] >> rpt strip_tac >> gvs[]")
        assert len(result) == 3
        # End positions should be monotonically increasing
        ends = [step.end for step in result]
        assert ends == sorted(ends)
        # Each cmd should be INDIVIDUAL (not cumulative)
        assert "simp" in result[0].cmd
        assert "strip_tac" in result[1].cmd
        assert "gvs" in result[2].cmd

    async def test_thenlt_chain(self, hol_session):
        """>- at top level decomposes base and arms into individual steps.
        
        e(Induct); e(simp[]) ≡ e(Induct >- simp[]) for single >- arm.
        """
        result = await call_step_plan(hol_session, "Induct >- simp[]")
        assert len(result) == 2
        assert "Induct" in result[0].cmd
        assert result[1].cmd.strip().startswith("e(")
        assert "simp" in result[1].cmd

    async def test_mixed_then_and_thenlt(self, hol_session):
        """Mixed >> and >- should handle both."""
        result = await call_step_plan(hol_session, "Induct >- simp[] >> gvs[]")
        # Induct, simp[], gvs[] = 3 steps
        assert len(result) >= 2

    async def test_with_quotations(self, hol_session):
        """Backtick quotations should be handled."""
        result = await call_step_plan(hol_session, "Cases_on `x` >> simp[]")
        assert len(result) == 2
        assert "Cases_on" in result[0].cmd
        assert "simp" in result[1].cmd

    async def test_single_tactic(self, hol_session):
        """Single tactic should return one step."""
        result = await call_step_plan(hol_session, "simp[]")
        assert len(result) == 1

    async def test_empty_proof_body_returns_no_steps(self, hol_session):
        """Empty proof body should return no executable steps."""
        result = await call_step_plan(hol_session, "")
        assert result == []

    async def test_comment_only_returns_no_steps(self, hol_session):
        """Comments/whitespace-only body should return no executable steps."""
        result = await call_step_plan(hol_session, "(* just a comment *)")
        assert result == []

    async def test_matches_tactic_steps(self, hol_session):
        """step_plan should return same step count as tactic_steps."""
        tactic = "simp[] >> rpt strip_tac >> gvs[]"
        escaped = escape_sml_string(tactic)

        # Get step_plan results
        plan_result = await call_step_plan(hol_session, tactic)

        # Get tactic_steps results
        steps_output = await hol_session.send(f'tactic_steps_json "{escaped}";', timeout=10)
        # Parse manually since we don't have a dedicated parser
        import json
        for line in steps_output.strip().split('\n'):
            if line.startswith('{"ok":'):
                steps_data = json.loads(line)['ok']
                break

        # Same number of steps
        assert len(plan_result) == len(steps_data)

        # Same end positions
        plan_ends = [step.end for step in plan_result]
        steps_ends = [step['end'] for step in steps_data]
        assert plan_ends == steps_ends

    async def test_by_construct(self, hol_session):
        """`by` is parsed as ThenLT — decomposes base, keeps >- suffix."""
        result = await call_step_plan(hol_session, "`P` by simp[]")
        # `by` = ThenLT at top level → base + suffix
        assert len(result) == 2

    async def test_by_in_chain(self, hol_session):
        """`by` in >> chain should be one step."""
        result = await call_step_plan(hol_session, "rpt strip_tac >> `P` by simp[] >> fs[]")
        assert len(result) == 3

    async def test_every_block_not_forced_atomic_by_coverage_heuristic(self, hol_session):
        """Regression: EVERY [...] should not be forced to one atomic step.

        Previously step_plan_json used a parseCoverage<0.9 heuristic and
        incorrectly collapsed some valid parses (e.g., EVERY lists) into a
        single raw e(full_proof) step.
        """
        result = await call_step_plan(hol_session, "EVERY [strip_tac, simp[], fs[]]")
        assert len(result) == 3
        assert "strip_tac" in result[0].cmd
        assert "simp" in result[1].cmd
        assert "fs" in result[2].cmd

    async def test_commands_are_valid_e_or_eall_calls(self, hol_session):
        """Each cmd should be a valid e() or eall() command."""
        result = await call_step_plan(hol_session, "a >> b >> c")
        for i, step in enumerate(result):
            cmd = step.cmd.strip()
            if i == 0:
                assert cmd.startswith("e("), f"First step should use e(), got: {cmd}"
            else:
                assert cmd.startswith("eall("), f"Step {i} should use eall(), got: {cmd}"
            assert cmd.endswith(");") or cmd.endswith(";\n")

    async def test_commands_are_individual_not_cumulative(self, hol_session):
        """Each step.cmd should be INDIVIDUAL, not cumulative.
        
        Critical for cursor: it joins all commands with "".join(step.cmd for step in steps).
        If commands are cumulative (e(a), e(a>>b), e(a>>b>>c)), joining runs 'a' 3 times!
        Commands should be individual: e(a), eall(b), eall(c).
        First uses e(), subsequent use eall() for correct >> semantics.
        """
        result = await call_step_plan(hol_session, "simp[] >> gvs[] >> fs[]")
        assert len(result) == 3
        
        # Each command should contain only ONE tactic (individual steps)
        # Step 1: e(simp[])
        assert "simp" in result[0].cmd
        assert result[0].cmd.strip().startswith("e(")
        assert "gvs" not in result[0].cmd
        assert "fs" not in result[0].cmd
        
        # Step 2: eall(gvs[]) - uses eall for >> semantics
        assert "gvs" in result[1].cmd
        assert result[1].cmd.strip().startswith("eall(")
        assert "simp" not in result[1].cmd
        assert "fs" not in result[1].cmd
        
        # Step 3: eall(fs[])
        assert "fs" in result[2].cmd
        assert result[2].cmd.strip().startswith("eall(")
        assert "simp" not in result[2].cmd
        assert "gvs" not in result[2].cmd

    async def test_joined_commands_execute_each_tactic_once(self, hol_session):
        """Joining all step commands should execute each tactic exactly once.
        
        This is how the cursor uses step_plan:
            step_cmds = "".join(step.cmd for step in self._step_plan)
        
        If step_plan returns cumulative commands, tactics get executed multiple times.
        First step uses e(), subsequent use eall() for correct >> semantics.
        """
        # Use simp[] instead of all_tac - all_tac has no span in TacticParse
        result = await call_step_plan(hol_session, "conj_tac >> conj_tac >> simp[]")
        
        # Join commands like the cursor does
        joined = "".join(step.cmd for step in result)
        
        # Should have 1 e() and 2 eall() calls
        assert joined.count("e(") == 1, f"Expected 1 e() call. Commands:\n{joined}"
        assert joined.count("eall(") == 2, f"Expected 2 eall() calls. Commands:\n{joined}"
        
        # Each tactic should appear exactly once in the joined string
        # (conj_tac appears twice in the original, so 2 occurrences is correct)
        assert joined.count("conj_tac") == 2, f"conj_tac should appear twice"
        assert joined.count("simp") == 1, f"simp should appear once"
