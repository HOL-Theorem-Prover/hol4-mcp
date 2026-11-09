"""Tests for GOALFRAG >>~- (LSelectThen / SELECT_LT_THEN) decomposition.

`>>~- ([pat], tac)` selects all goals matching pat, runs tac on them, and
requires zero residual. TacticParse decomposes it into
open_select_lt / <body> / next_select_lt / <arm> / close fragments; the MCP
step decomposer must navigate it rather than choking on the bare pattern list
(the historically-reported false 'PROOF BROKEN at the opaque step').
"""

import pytest
import json
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output
from hol4_mcp.hol_cursor import FileProofCursor

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"
SELECT_THEN_FIXTURE = FIXTURES_DIR / "selectThenScript.sml"


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


async def execute_steps(session, steps, goal):
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


# `>>~-` pattern uses term quotes; use Unicode ‘ ’ (CakeML convention).
SELECT_THEN = "conj_tac >>~- ([‘T’], SIMP_TAC bool_ss [])"


class TestSelectThenStepPlan:
    async def test_decomposes_without_error(self, hol_session):
        """A >>~- proof must decompose into fragments, not a single opaque/failed step."""
        steps = await call_step_plan(hol_session, SELECT_THEN)
        assert len(steps) > 1, f"expected fragment decomposition, got {len(steps)}: {[s.cmd for s in steps]}"

    async def test_emits_select_lt_fragments(self, hol_session):
        """The decomposition must use the select-LT goalFrag operators
        (open_select_lt / next_select_lt), not collapse to one opaque step."""
        steps = await call_step_plan(hol_session, SELECT_THEN)
        cmds = " ".join(s.cmd for s in steps)
        assert "open_select_lt" in cmds, cmds
        assert "next_select_lt" in cmds, cmds
        # No fragment should be an Opaque step (the old false-PROOF-BROKEN shape).
        assert "Opaque" not in cmds and "OOpaque" not in cmds


class TestSelectThenExecution:
    async def test_proves_goal(self, hol_session):
        """`conj_tac >>~- ([‘T’], SIMP_TAC bool_ss [])` proves `T /\\ T`."""
        steps = await call_step_plan(hol_session, SELECT_THEN)
        goal_count = await execute_steps(hol_session, steps, "T /\\ T")
        assert goal_count == 0, f"expected proof complete, {goal_count} goals remain"


class TestSelectThenNavigation:
    """state_at over a real >>~- proof must reach 'No goals', not a false
    PROOF BROKEN at the opaque step (the originally-reported symptom)."""

    @pytest.fixture
    async def cursor(self, tmp_path):
        session = HOLSession(str(tmp_path))
        await session.start()
        await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
        c = FileProofCursor(SELECT_THEN_FIXTURE, session,
                            checkpoint_dir=tmp_path / "checkpoints")
        await c.init()
        yield c
        await session.stop()

    async def test_state_at_qed_no_goals(self, cursor):
        # QED line of select_then_thm in the fixture.
        qed_line = next(
            i for i, l in enumerate(SELECT_THEN_FIXTURE.read_text().splitlines(), 1)
            if l.strip() == "QED"
        )
        result = await cursor.state_at(line=qed_line)
        assert not result.error, f"unexpected error: {result.error}"
        assert not result.goals, f"expected no goals, got {result.goals}"
