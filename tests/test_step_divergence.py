"""Tests for GOALFRAG step plan structure and properties.

Verifies monotonicity, command format, and execution correctness.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower()
    yield session
    await session.stop()


async def call_step_plan(session, tactic_str):
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'goalfrag_step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(result)


class TestStepPlan:
    """Structural properties of goalfrag_step_plan output."""

    async def test_step_plan_ends_are_monotonic(self, hol_session):
        """End offsets are non-decreasing."""
        for tactic in ["a >> b >> c", "conj_tac >- simp[] >- fs[]", "strip_tac >> conj_tac >- simp[]"]:
            result = await call_step_plan(hol_session, tactic)
            ends = [step.end for step in result]
            assert ends == sorted(ends), f"Non-monotonic ends for {tactic}: {ends}"

    async def test_step_plan_commands_use_ef(self, hol_session):
        """All commands use ef(goalFrag."), not e( or eall(."""
        result = await call_step_plan(hol_session, "a >> b >> c >- d >- e")
        for step in result:
            assert step.cmd.startswith("ef(goalFrag."), f"Expected ef(), got: {step.cmd}"

    async def test_step_plan_then_chain(self, hol_session):
        """>> chain: one expand step per tactic."""
        result = await call_step_plan(hol_session, "simp[] >> rpt strip_tac >> gvs[]")
        assert len(result) == 3
        assert all("ef(goalFrag.expand(" in s.cmd for s in result)

    async def test_step_plan_then1_structure(self, hol_session):
        """>- structure: expand, open_then1, expand, close."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        assert len(result) == 4
        assert "ef(goalFrag.expand(conj_tac));" == result[0].cmd
        assert "ef(goalFrag.open_then1);" == result[1].cmd
        assert result[2].cmd.startswith("ef(goalFrag.expand(")
        assert "ef(goalFrag.close_paren);" == result[3].cmd

    async def test_step_plan_commands_are_executable(self, hol_session):
        """Steps can be executed on GOALFRAG without errors."""
        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\\ T`;', timeout=10)
        for step in result:
            r = await hol_session.send(step.cmd, timeout=10)
            assert "Exception-" not in r, f"Step failed: {step.cmd}"
