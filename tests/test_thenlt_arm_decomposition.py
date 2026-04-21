"""Tests for GOALFRAG arm decomposition of >- chains.

With GOALFRAG, each >- arm becomes open_then1 / expand / close_paren.
No need for the old e(arm_text) decomposition — every fragment is a step.
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


class TestArmDecomposition:
    """GOALFRAG decomposes each >- arm into open/expand/close."""

    async def test_single_arm(self, hol_session):
        """Single >- arm: expand(base), open_then1, expand(arm), close."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        cmds = [s.cmd for s in result]
        assert len(cmds) == 4
        assert "ef(goalFrag.expand(conj_tac));" in cmds
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.expand(simp[]));" in cmds
        assert "ef(goalFrag.close_paren);" in cmds

    async def test_two_arms(self, hol_session):
        """Two >- arms: each gets open/expand/close."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >- fs[]")
        cmds = [s.cmd for s in result]
        # expand(conj_tac), open, expand(simp[]), close, open, expand(fs[]), close
        assert cmds.count("ef(goalFrag.open_then1);") == 2
        assert cmds.count("ef(goalFrag.close_paren);") == 2

    async def test_by_is_same(self, hol_session):
        """`by` produces same decomposition as `>-`."""
        by_result = await call_step_plan(hol_session, "conj_tac by simp[]")
        then1_result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        by_cmds = [s.cmd for s in by_result]
        then1_cmds = [s.cmd for s in then1_result]
        # Should have same step structure (open/expand/close)
        assert len(by_cmds) == len(then1_cmds)
        assert by_cmds.count("ef(goalFrag.open_then1);") == then1_cmds.count("ef(goalFrag.open_then1);")

    async def test_arm_execution_proves_goal(self, hol_session):
        """Two-arm decomposition proves conjunction on GOALFRAG."""
        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        assert len(result) == 7

        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\\ T`;', timeout=10)
        for step in result:
            r = await hol_session.send(step.cmd, timeout=10)
            assert "Exception-" not in r, f"Step failed: {step.cmd} → {r}"

        r = await hol_session.send('top_thm();', timeout=10)
        assert "T ∧ T" in r

    async def test_arm_with_nested_then(self, hol_session):
        """Arm containing >> chain produces intra-arm expand steps."""
        result = await call_step_plan(hol_session, "conj_tac >- (simp[] >> fs[])")
        cmds = [s.cmd for s in result]
        # expand(conj_tac), open_then1, expand(simp[]), expand(fs[]), close_paren
        assert "ef(goalFrag.expand(conj_tac));" in cmds
        assert "ef(goalFrag.open_then1);" in cmds
        # Inside arm: simp[] and fs[] as separate expands
        assert "ef(goalFrag.expand(simp[]));" in cmds or "ef(goalFrag.expand((simp[] >> fs[])));" in cmds
        assert "ef(goalFrag.close_paren);" in cmds

    async def test_backup_inside_arm(self, hol_session):
        """Can backup inside an arm to see intermediate state."""
        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\\ T`;', timeout=10)

        # Execute CONJ_TAC + open_then1 (first 2 steps)
        for step in result[:2]:
            await hol_session.send(step.cmd, timeout=10)

        # After open_then1: should see focused subgoal
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                # Focused on first subgoal
                assert len(goals) == 1
                break

        # Backup out of the open_then1
        await hol_session.send('backup_n 1;', timeout=10)
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                # Back to 2 unfocused goals
                assert len(goals) == 2
                break
