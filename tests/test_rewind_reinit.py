"""Backward navigation when no checkpoint can be restored.

Every per-theorem checkpoint saved in a session becomes part of its Poly/ML
SaveState parent chain, and Poly/ML refuses to save over a parent. A rewind
that restores nothing must therefore restart HOL rather than replay in the
old heap: replaying there keeps later theorems bound and loses every
checkpoint it tries to re-save.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp.hol_session import HOLSession


SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"

FIXTURE = Path(__file__).parent / "fixtures" / "testScript.sml"


@pytest.fixture
async def cursor(tmp_path):
    session = HOLSession(str(tmp_path))
    await session.start()
    await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
    c = FileProofCursor(FIXTURE, session, checkpoint_dir=tmp_path / "checkpoints")
    await c.init()
    yield c
    await session.stop()


@pytest.mark.asyncio
async def test_unrestorable_rewind_restarts_hol(cursor: FileProofCursor):
    await cursor.enter_theorem("helper_lemma")
    context_paths = [ck.context_path for ck in cursor._checkpoints.values()
                     if ck.context_path is not None]
    assert context_paths, "forward navigation saved no context checkpoints"
    cursor.take_notices()

    for p in context_paths:
        p.unlink()
    cursor._deps_checkpoint_path.unlink()
    for ck in cursor._checkpoints.values():   # no in-memory point either
        ck.point_id = None

    bound = await cursor.session.send('DB.fetch "-" "zero_add";', timeout=10)
    assert "HOL_ERR" not in bound and "Exception" not in bound, bound

    target = cursor._get_theorem("partial_proof")
    result = await cursor.state_at(target.start_line + 2, 1)
    assert result.error is None, result.error

    notices = cursor.take_notices()
    assert any("Session reinit" in n for n in notices), notices
    assert not any("used as a parent" in n for n in notices), notices

    # The heap no longer holds a theorem that follows the target.
    fetched = await cursor.session.send('DB.fetch "-" "zero_add";', timeout=10)
    assert "HOL_ERR" in fetched or "Exception" in fetched, fetched

    # Checkpoints save again after the restart.
    saved = [ck.context_path for ck in cursor._checkpoints.values()
             if ck.context_path is not None and ck.context_path.exists()]
    assert saved, "no context checkpoint was saved after the restart"
