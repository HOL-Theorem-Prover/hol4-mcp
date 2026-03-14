"""Test step_plan_json consistency - single source of truth for O(1) navigation.

Key design:
- >> chains: return one step per tactic (for fine-grained navigation)
  - First step uses e(), subsequent use eall() for correct >> semantics
  - e(a >> b >> c) = e(a); eall(b); eall(c)
- >- chains: return one step per fragment (linearize splits them)
  - Navigation inside >- uses HEADGOAL via partial_step_commands
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_file_parser import parse_step_plan_output
from hol4_mcp.hol_session import HOLSession, escape_sml_string

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


class TestStepPlan:
    """Test step_plan_json returns consistent step boundaries with commands."""

    async def test_step_plan_single_tactic(self, hol_session):
        """Single tactic returns one step."""
        tactic = "strip_tac"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        assert len(plan) == 1
        assert plan[0].end == 9  # len("strip_tac")
        assert "e(strip_tac)" in plan[0].cmd

    async def test_step_plan_then_chain_multiple_steps(self, hol_session):
        """THEN chain (>>) returns one step per tactic for fine-grained navigation.
        
        First step uses e(), subsequent steps use eall() for correct >> semantics:
        e(a >> b >> c) = e(a); eall(b); eall(c)
        """
        tactic = "strip_tac >> rw[] >> fs[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        # THEN chain gives one step per tactic
        assert len(plan) == 3
        # First uses e(), rest use eall()
        assert plan[0].cmd.strip().startswith("e(")
        assert plan[1].cmd.strip().startswith("eall(")
        assert plan[2].cmd.strip().startswith("eall(")

    async def test_step_plan_thenl_multiple_steps(self, hol_session):
        """THENL (>-) with arms: base decomposed, arms decomposed into e() each."""
        tactic = "conj_tac >- simp[] >- fs[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        # Base (conj_tac) + 2 arms (simp[], fs[])
        assert len(plan) == 3
        # All steps start with e(, eall(, or elt(
        for step in plan:
            cmd = step.cmd.strip()
            assert cmd.startswith("e(") or cmd.startswith("eall(") or cmd.startswith("elt(")

    async def test_step_plan_thenl_bracket(self, hol_session):
        """THENL with bracket (>|) returns steps."""
        tactic = "conj_tac >| [simp[], rw[]]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        assert len(plan) >= 1
        # Last step should end at tactic length
        assert plan[-1].end == len(tactic)

    async def test_step_plan_ends_are_monotonic(self, hol_session):
        """Step ends should be monotonically increasing."""
        tactic = "strip_tac >> rw[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        for i in range(1, len(plan)):
            assert plan[i].end >= plan[i-1].end

    async def test_step_plan_commands_are_executable(self, hol_session):
        """Step commands should be valid e(), eall(), or elt() calls."""
        tactic = "conj_tac >- simp[] >- fs[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        for step in plan:
            cmd = step.cmd.strip()
            assert cmd.startswith("e(") or cmd.startswith("eall(") or cmd.startswith("elt(")
            assert cmd.endswith(");")
