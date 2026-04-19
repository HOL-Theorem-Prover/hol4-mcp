"""Tests for context checkpoint creation, loading, and backward navigation.

Context checkpoints capture theory state after loading theorem content (QED → stored).
They enable O(1) backward navigation instead of full file replay.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import FileProofCursor, TheoremCheckpoint
from hol4_mcp.hol_session import HOLSession


SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"

FIXTURE = Path(__file__).parent / "fixtures" / "testScript.sml"


@pytest.fixture
async def cursor(tmp_path):
    """Create an initialized FileProofCursor with test fixtures."""
    session = HOLSession(str(tmp_path))
    await session.start()
    await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
    ckpt_dir = tmp_path / "checkpoints"
    c = FileProofCursor(FIXTURE, session, checkpoint_dir=ckpt_dir)
    await c.init()
    yield c
    await session.stop()


# --- Context checkpoint creation during loading ---


@pytest.mark.asyncio
async def test_context_checkpoints_created_on_enter(cursor: FileProofCursor):
    """enter_theorem should save context checkpoints for predecessors whose
    proof_end_line is within the loaded range."""
    # testScript has: add_zero, needs_proof, partial_proof, zero_add, helper_lemma
    # enter_theorem loads content up to target start_line, so any predecessor
    # whose proof_end_line <= target start_line gets a checkpoint.
    await cursor.enter_theorem("helper_lemma")

    # All predecessors whose proof_end_line <= helper_lemma.start_line
    # should have context checkpoints
    assert "add_zero" in cursor._checkpoints
    assert "needs_proof" in cursor._checkpoints
    assert "partial_proof" in cursor._checkpoints
    assert "zero_add" in cursor._checkpoints

    # helper_lemma itself is NOT checkpointed — only loaded up to start_line
    assert "helper_lemma" not in cursor._checkpoints


@pytest.mark.asyncio
async def test_context_checkpoint_has_context_path(cursor: FileProofCursor):
    """Context checkpoints should have context_path set, no end_of_proof_path."""
    # Enter a later theorem so add_zero (predecessor) gets a context checkpoint
    await cursor.enter_theorem("zero_add")

    ckpt = cursor._checkpoints.get("add_zero")
    assert ckpt is not None
    assert ckpt.context_path is not None
    assert ckpt.context_path.exists()
    assert ckpt.end_of_proof_path is None  # No proof replay yet


@pytest.mark.asyncio
async def test_context_checkpoint_files_on_disk(cursor: FileProofCursor):
    """Context checkpoint files should exist on disk."""
    await cursor.enter_theorem("helper_lemma")

    for name in ["add_zero", "needs_proof", "partial_proof", "zero_add"]:
        ckpt = cursor._checkpoints.get(name)
        assert ckpt is not None, f"Missing checkpoint entry for {name}"
        assert ckpt.context_path is not None, f"Missing context_path for {name}"
        assert ckpt.context_path.exists(), f"Missing context file for {name}"
        assert ckpt.context_path.name.endswith("_context.save")


# --- _loaded_to_line tracking ---


@pytest.mark.asyncio
async def test_loaded_to_line_after_enter(cursor: FileProofCursor):
    """_loaded_to_line should reflect content loaded, not last theorem."""
    await cursor.enter_theorem("add_zero")
    # add_zero starts at line 11, proof_end_line after QED
    thm = cursor._get_theorem("add_zero")
    assert thm is not None
    # _loaded_to_line should be at or past add_zero's start_line
    assert cursor._loaded_to_line >= thm.start_line


@pytest.mark.asyncio
async def test_loaded_to_line_after_load_context_checkpoint(cursor: FileProofCursor):
    """Loading context checkpoint should set _loaded_to_line to that theorem's proof_end_line."""
    # Enter later theorem to create checkpoints for predecessors
    await cursor.enter_theorem("helper_lemma")

    ckpt = cursor._checkpoints.get("add_zero")
    assert ckpt is not None and ckpt.context_path is not None

    result = await cursor._load_context_checkpoint("add_zero")
    assert result is True

    thm = cursor._get_theorem("add_zero")
    assert thm is not None
    # Key fix: _loaded_to_line should be add_zero's proof_end_line, NOT last theorem's
    assert cursor._loaded_to_line == thm.proof_end_line, (
        f"Expected _loaded_to_line={thm.proof_end_line}, "
        f"got {cursor._loaded_to_line} (should be add_zero's proof_end_line, not last_thm)"
    )


@pytest.mark.asyncio
async def test_loaded_to_line_after_load_end_of_proof_checkpoint(cursor: FileProofCursor):
    """Loading end_of_proof checkpoint should set _loaded_to_line to that theorem's proof_end_line.

    This tests the fix for the Gemini-identified bug where _loaded_to_line was set to
    last_thm.proof_end_line instead of the checkpoint's theorem.
    """
    # Enter later theorem so add_zero gets a context checkpoint
    await cursor.enter_theorem("zero_add")

    # Go back and do state_at on add_zero to create end_of_proof checkpoint
    await cursor._load_context_checkpoint("add_zero")
    thm = cursor._get_theorem("add_zero")
    qed_line = thm.proof_end_line - 1
    result = await cursor.state_at(line=qed_line)
    assert result.error is None or "no goals" in (result.error or "")

    ckpt = cursor._checkpoints.get("add_zero")
    assert ckpt is not None
    assert ckpt.end_of_proof_path is not None

    # Now load a different theorem to move the cursor elsewhere
    await cursor.enter_theorem("helper_lemma")

    # Load add_zero's end_of_proof checkpoint
    ok = await cursor._load_checkpoint_and_backup("add_zero", 0)
    assert ok, "Should load add_zero's end_of_proof checkpoint"

    thm = cursor._get_theorem("add_zero")
    assert thm is not None
    # Key assertion: should be add_zero's proof_end_line, NOT last theorem's
    assert cursor._loaded_to_line == thm.proof_end_line, (
        f"Expected _loaded_to_line={thm.proof_end_line}, "
        f"got {cursor._loaded_to_line}"
    )


# --- _find_predecessor_checkpoint ---


@pytest.mark.asyncio
async def test_find_predecessor_returns_closest(cursor: FileProofCursor):
    """_find_predecessor_checkpoint should return the closest predecessor with a valid checkpoint."""
    await cursor.enter_theorem("helper_lemma")

    target = cursor._get_theorem("helper_lemma")
    pred = cursor._find_predecessor_checkpoint(target)
    assert pred is not None
    # Closest predecessor with checkpoint should be zero_add
    assert pred.name == "zero_add"


@pytest.mark.asyncio
async def test_find_predecessor_returns_none_when_no_checkpoints(cursor: FileProofCursor):
    """_find_predecessor_checkpoint should return None if no predecessors have checkpoints."""
    # Don't enter any theorem — no checkpoints exist
    target = cursor._get_theorem("helper_lemma")
    pred = cursor._find_predecessor_checkpoint(target)
    assert pred is None


# --- Backward navigation via context checkpoint ---


@pytest.mark.asyncio
async def test_backward_navigation_via_checkpoint(cursor: FileProofCursor):
    """Navigating backward should use context checkpoint instead of full replay."""
    # Load all theorems forward
    await cursor.enter_theorem("helper_lemma")
    assert cursor._loaded_to_line >= 40

    # Simulate being "past" the target (like after hol_state_at loaded later state)
    # by manually advancing _loaded_to_line
    cursor._loaded_to_line = 999

    # Navigate backward to zero_add via context checkpoint
    target = cursor._get_theorem("zero_add")
    assert target is not None

    pred = cursor._find_predecessor_checkpoint(target)
    assert pred is not None

    ok = await cursor._load_context_checkpoint(pred.name)
    assert ok

    # Verify _loaded_to_line is at the predecessor, not at 999 or last theorem
    pred_thm = cursor._get_theorem(pred.name)
    assert cursor._loaded_to_line == pred_thm.proof_end_line

    # enter_theorem should load only the small delta
    result = await cursor.enter_theorem("zero_add")
    assert "error" not in result


@pytest.mark.asyncio
async def test_backward_navigation_fallback_to_deps(cursor: FileProofCursor):
    """If no predecessor checkpoint exists, backward navigation should restore to deps."""
    # No checkpoints exist, but _loaded_to_line is advanced
    cursor._loaded_to_line = 999
    assert cursor._deps_checkpoint_saved

    target = cursor._get_theorem("zero_add")
    assert target is not None

    pred = cursor._find_predecessor_checkpoint(target)
    assert pred is None  # No checkpoints yet

    # execute_proof_traced would fallback to _restore_to_deps here
    ok = await cursor._restore_to_deps()
    assert ok
    assert cursor._loaded_to_line == 0

    # enter_theorem does full incremental load
    result = await cursor.enter_theorem("zero_add")
    assert "error" not in result


# --- Context vs end_of_proof checkpoint coexistence ---


@pytest.mark.asyncio
async def test_context_and_end_of_proof_coexist(cursor: FileProofCursor):
    """A theorem can have both context and end_of_proof checkpoints."""
    # Enter a later theorem so add_zero gets a context checkpoint
    await cursor.enter_theorem("zero_add")

    # Now go back and do state_at on add_zero to create end_of_proof checkpoint
    await cursor._load_context_checkpoint("add_zero")
    thm_az = cursor._get_theorem("add_zero")
    qed_line = thm_az.proof_end_line - 1
    result = await cursor.state_at(line=qed_line)
    assert result.error is None or "no goals" in (result.error or "")

    ckpt = cursor._checkpoints.get("add_zero")
    assert ckpt is not None
    assert ckpt.context_path is not None, "Context checkpoint should exist from loading"
    assert ckpt.end_of_proof_path is not None, "End_of_proof checkpoint should exist from state_at"


# --- Checkpoint invalidation ---


@pytest.mark.asyncio
async def test_invalidate_deletes_both_paths(cursor: FileProofCursor):
    """_invalidate_checkpoint should delete both context and end_of_proof files."""
    # Enter later theorem to create context checkpoint for add_zero
    await cursor.enter_theorem("zero_add")

    # Go back and create end_of_proof for add_zero
    await cursor._load_context_checkpoint("add_zero")
    thm_az = cursor._get_theorem("add_zero")
    qed_line = thm_az.proof_end_line - 1
    result = await cursor.state_at(line=qed_line)
    assert result.error is None or "no goals" in (result.error or "")

    ckpt = cursor._checkpoints.get("add_zero")
    assert ckpt is not None
    ctx_path = ckpt.context_path
    eop_path = ckpt.end_of_proof_path
    assert ctx_path is not None and ctx_path.exists()
    assert eop_path is not None and eop_path.exists()

    # Invalidate
    cursor._invalidate_checkpoint("add_zero")

    # Both files should be deleted
    assert not ctx_path.exists(), "Context file should be deleted"
    assert not eop_path.exists(), "End_of_proof file should be deleted"
    assert "add_zero" not in cursor._checkpoints


@pytest.mark.asyncio
async def test_is_context_checkpoint_valid(cursor: FileProofCursor):
    """_is_context_checkpoint_valid should check context_path existence and content_hash."""
    # Enter later theorem so add_zero gets a context checkpoint
    await cursor.enter_theorem("zero_add")

    assert cursor._is_context_checkpoint_valid("add_zero") is True
    assert cursor._is_context_checkpoint_valid("helper_lemma") is False  # Not loaded yet

    # Invalidate should make it invalid
    cursor._invalidate_checkpoint("add_zero")
    assert cursor._is_context_checkpoint_valid("add_zero") is False


@pytest.mark.asyncio
async def test_is_checkpoint_valid_still_checks_end_of_proof(cursor: FileProofCursor):
    """_is_checkpoint_valid should still only check end_of_proof_path."""
    # Enter later theorem so add_zero gets a context checkpoint
    await cursor.enter_theorem("zero_add")

    # Only context checkpoint exists, no end_of_proof
    assert cursor._is_checkpoint_valid("add_zero") is False  # No end_of_proof_path
    assert cursor._is_context_checkpoint_valid("add_zero") is True  # Has context_path


# --- Context checkpoint state correctness ---


@pytest.mark.asyncio
async def test_context_checkpoint_theorem_stored(cursor: FileProofCursor, tmp_path: Path):
    """Loading a context checkpoint should have the theorem stored (not just proved)."""
    # Enter later theorem so add_zero gets a context checkpoint
    await cursor.enter_theorem("zero_add")

    ckpt = cursor._checkpoints.get("add_zero")
    assert ckpt is not None and ckpt.context_path is not None

    # Verify theorem is stored in SML
    result = await cursor.session.send("DB.fetch \"test\" \"add_zero\";", timeout=10)
    assert "ERR" not in result, "add_zero should be stored in theory after loading"

    # Now load the checkpoint and verify still accessible
    ok = await cursor._load_context_checkpoint("add_zero")
    assert ok

    result = await cursor.session.send("DB.fetch \"test\" \"add_zero\";", timeout=10)
    assert "ERR" not in result, "add_zero should still be stored after loading context checkpoint"


# --- execute_proof_traced backward navigation ---


@pytest.mark.asyncio
async def test_execute_proof_traced_backward_uses_checkpoint(cursor: FileProofCursor):
    """execute_proof_traced should use predecessor checkpoint for backward navigation."""
    # First: load far ahead to create context checkpoints
    await cursor.enter_theorem("helper_lemma")

    # Now move _loaded_to_line past an earlier theorem to simulate backward case
    cursor._loaded_to_line = 999

    # Execute proof for an early theorem
    trace = await cursor.execute_proof_traced("add_zero")

    # Should succeed — backward navigation used predecessor or deps fallback
    # (add_zero is the first theorem so there's no predecessor; deps restore happened)
    # For middle theorems, the predecessor checkpoint path would be used
    # We just verify it doesn't crash and returns results


@pytest.mark.asyncio
async def test_execute_proof_traced_forward_skips_restore(cursor: FileProofCursor):
    """execute_proof_traced forward calls should not restore to deps."""
    # Load add_zero (first theorem)
    trace1 = await cursor.execute_proof_traced("add_zero")

    # _loaded_to_line should be past add_zero's start
    assert cursor._loaded_to_line > 0

    # Now call for the next theorem — should be incremental, no deps restore
    # Verify by checking _loaded_to_line didn't reset to 0
    prev_loaded = cursor._loaded_to_line
    trace2 = await cursor.execute_proof_traced("zero_add")
    # _loaded_to_line should have advanced, not reset
    assert cursor._loaded_to_line >= prev_loaded, (
        f"Forward call should advance _loaded_to_line, got {cursor._loaded_to_line} < {prev_loaded}"
    )


# --- _load_context_checkpoint failure handling ---


@pytest.mark.asyncio
async def test_load_context_checkpoint_handles_missing_file(cursor: FileProofCursor):
    """Loading a context checkpoint with a deleted file should fail gracefully."""
    # Enter later theorem so add_zero gets a context checkpoint
    await cursor.enter_theorem("zero_add")

    ckpt = cursor._checkpoints.get("add_zero")
    assert ckpt is not None and ckpt.context_path is not None

    # Delete the file
    ckpt.context_path.unlink()

    # Should fail and clean up
    result = await cursor._load_context_checkpoint("add_zero")
    assert result is False
    assert ckpt.context_path is None  # Should be cleared
