"""Tests for GOALFRAG >- (Then1) decomposition.

With GOALFRAG, >- decomposes into open_then1 / expand / close_paren steps.
Every fragment boundary is a step — no heuristics needed.
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


async def execute_steps(session, steps, goal="T /\\ T"):
    """Execute all steps on a GOALFRAG proof, return final goal count."""
    await session.send('drop_all();', timeout=5)
    await session.send(f'gf `{goal}`;', timeout=10)
    for step in steps:
        r = await session.send(step.cmd, timeout=10)
        if "Exception-" in r:
            return -1
    r = await session.send('goals_json();', timeout=10)
    for line in r.strip().split('\n'):
        if line.startswith('{"ok":'):
            return len(json.loads(line)['ok'])
    return -1


class TestThen1StepPlan:
    """Verify goalfrag_step_plan decomposition for >- patterns."""

    async def test_single_then1_step_count(self, hol_session):
        """`a >- b` → 4 steps: expand(a), open_then1, expand(b), close_paren."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        assert len(result) == 4

    async def test_double_then1_step_count(self, hol_session):
        """`a >- b >- c` → 7 steps: expand, open, expand, close, open, expand, close."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[] >- fs[]")
        assert len(result) == 7

    async def test_then1_before_then(self, hol_session):
        """`a >> b >- c` → 4 steps: expand(a), expand(b), open, expand(c), close."""
        result = await call_step_plan(hol_session, "strip_tac >> conj_tac >- simp[]")
        cmds = [s.cmd for s in result]
        assert "ef(goalFrag.expand(strip_tac));" in cmds
        assert "ef(goalFrag.expand(conj_tac));" in cmds
        assert "ef(goalFrag.open_then1);" in cmds
        assert "ef(goalFrag.expand(simp[]));" in cmds
        assert "ef(goalFrag.close_paren);" in cmds

    async def test_by_same_as_then1(self, hol_session):
        """`a by b` decomposes same as `a >- b`."""
        by_result = await call_step_plan(hol_session, "conj_tac by simp[]")
        then1_result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        assert len(by_result) == len(then1_result)

    async def test_then1_step_order(self, hol_session):
        """Steps are in correct execution order: base → open → arm → close."""
        result = await call_step_plan(hol_session, "conj_tac >- simp[]")
        cmds = [s.cmd for s in result]
        idx_base = next(i for i, c in enumerate(cmds) if "conj_tac" in c)
        idx_open = next(i for i, c in enumerate(cmds) if "open_then1" in c)
        idx_arm = next(i for i, c in enumerate(cmds) if "simp[]" in c)
        idx_close = next(i for i, c in enumerate(cmds) if "close_paren" in c)
        assert idx_base < idx_open < idx_arm < idx_close


class TestThen1Execution:
    """Verify >- steps execute correctly on GOALFRAG."""

    async def test_single_then1_proves_goal(self, hol_session):
        """`CONJ_TAC >- SIMP_TAC bool_ss []` proves `T /\\ T`."""
        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        goal_count = await execute_steps(hol_session, result)
        assert goal_count == 0

    async def test_backup_restores_goals(self, hol_session):
        """backup_n after >- restores original goals."""
        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\\ T`;', timeout=10)

        # Execute CONJ_TAC + open_then1 (2 steps)
        for step in result[:2]:
            await hol_session.send(step.cmd, timeout=10)

        # After open_then1: 1 focused goal
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 1
                break

        # Backup to before open_then1: 2 goals
        await hol_session.send('backup_n 1;', timeout=10)
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 2
                break

    async def test_mid_proof_navigation(self, hol_session):
        """Can navigate to position after open_then1 (focused subgoal)."""
        result = await call_step_plan(hol_session, "CONJ_TAC >- SIMP_TAC bool_ss [] >- SIMP_TAC bool_ss []")
        await hol_session.send('drop_all();', timeout=5)
        await hol_session.send('gf `T /\\ T`;', timeout=10)

        # Execute just the first arm (4 steps)
        for step in result[:4]:
            await hol_session.send(step.cmd, timeout=10)

        # After close_paren: back to 1 remaining goal
        r = await hol_session.send('goals_json();', timeout=10)
        for line in r.strip().split('\n'):
            if line.startswith('{"ok":'):
                goals = json.loads(line)['ok']
                assert len(goals) == 1
                break
