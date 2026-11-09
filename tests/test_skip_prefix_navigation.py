"""Integration tests for prefix-skip navigation (state_at skip_prefix=True).

skip_prefix binds every theorem BEFORE the target via `cheat` (statement only)
instead of replaying it, so navigation into a target is instant even when an
earlier proof is slow or non-terminating. These drive FileProofCursor /
HOLSession directly (no FastMCP tool layer), matching the other live tests.

The fixture's `broken_prefix` has a proof that FAILS fast if replayed but a TRUE
statement — a deterministic proxy for "a prefix proof you don't want to run":
  - skip_prefix=True  → it is cheated, recorded in cursor._skipped_thms, and the
    target navigates fine using its statement.
  - skip_prefix=False → it is replayed, fails, and is auto-cheated into
    cursor._failed_proofs (NOT _skipped_thms).
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession
from hol4_mcp.hol_cursor import FileProofCursor

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"
SKIP_FIXTURE = FIXTURES_DIR / "skipPrefixScript.sml"


def _qed_line_of(theorem: str) -> int:
    """1-indexed line of the QED that closes `Theorem <theorem>:` in the fixture."""
    lines = SKIP_FIXTURE.read_text().splitlines()
    start = next(i for i, l in enumerate(lines)
                 if l.strip().startswith(f"Theorem {theorem}"))
    for i in range(start, len(lines)):
        if lines[i].strip() == "QED":
            return i + 1
    raise AssertionError(f"no QED after Theorem {theorem}")


@pytest.fixture
async def cursor(tmp_path):
    session = HOLSession(str(tmp_path))
    await session.start()
    await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
    c = FileProofCursor(SKIP_FIXTURE, session,
                        checkpoint_dir=tmp_path / "checkpoints")
    await c.init()
    yield c
    await session.stop()


class TestSkipPrefixNavigation:
    async def test_skip_binds_prefix_by_statement(self, cursor):
        """With skip_prefix=True the target navigates to 'No goals' and every
        prefix theorem is recorded as skipped (cheated, not replayed)."""
        qed = _qed_line_of("uses_prefix")
        result = await cursor.state_at(line=qed, skip_prefix=True)
        assert not result.error, f"unexpected error: {result.error}"
        assert not result.goals, f"expected no goals, got {result.goals}"
        # Both prefix theorems were bound by cheat without replay.
        assert "broken_prefix" in cursor._skipped_thms
        assert "good_prefix" in cursor._skipped_thms
        # The target itself is NOT a skipped prefix (it replayed for real).
        assert "uses_prefix" not in cursor._skipped_thms
        assert cursor._skip_prefix is True

    async def test_skip_succeeds_despite_unreplayable_prefix(self, cursor):
        """broken_prefix's proof would FAIL if replayed; skip mode must still
        reach the target (proving the prefix was cheated, not run)."""
        qed = _qed_line_of("uses_prefix")
        result = await cursor.state_at(line=qed, skip_prefix=True)
        assert not result.error and not result.goals
        # It was skipped, NOT routed through the failure/auto-cheat path.
        assert "broken_prefix" in cursor._skipped_thms
        assert "broken_prefix" not in getattr(cursor, "_failed_proofs", {})

    async def test_skip_off_replays_and_autocheats_broken(self, cursor):
        """Without skip_prefix, broken_prefix is replayed, fails, and is
        auto-cheated into _failed_proofs — NOT _skipped_thms."""
        qed = _qed_line_of("uses_prefix")
        result = await cursor.state_at(line=qed, skip_prefix=False)
        assert not result.error, f"unexpected error: {result.error}"
        assert not result.goals
        assert "broken_prefix" not in cursor._skipped_thms
        assert "broken_prefix" in cursor._failed_proofs
        assert cursor._skip_prefix is False

    async def test_toggle_mode_resets_skipped(self, cursor):
        """Toggling skip_prefix forces a clean reload and clears the skip set."""
        qed = _qed_line_of("uses_prefix")
        await cursor.state_at(line=qed, skip_prefix=True)
        assert cursor._skipped_thms  # populated
        # Toggle off: skip set cleared, mode flips, target still navigates.
        result = await cursor.state_at(line=qed, skip_prefix=False)
        assert not result.error and not result.goals
        assert cursor._skipped_thms == set()
        assert cursor._skip_prefix is False

    async def test_target_goal_readable_mid_proof_under_skip(self, cursor):
        """Inside the target proof (before its closing tactic), skip mode shows
        the real live goal — the point of the feature."""
        # Position at the Proof keyword line of uses_prefix → entry goal.
        lines = SKIP_FIXTURE.read_text().splitlines()
        start = next(i for i, l in enumerate(lines)
                     if l.strip().startswith("Theorem uses_prefix"))
        proof_line = next(i for i in range(start, len(lines))
                          if lines[i].strip() == "Proof") + 1  # 1-indexed
        result = await cursor.state_at(line=proof_line + 1, skip_prefix=True)
        # Entry goal of `5 + 0 = 5` is present and real.
        assert not result.error, f"unexpected error: {result.error}"
        assert result.goals, "expected the target's entry goal"
        assert "5" in result.goals[0].get("goal", "")
