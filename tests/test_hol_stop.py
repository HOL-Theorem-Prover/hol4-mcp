"""Unit tests for HOLSession.stop() and hol_stop() bug fixes.

Tests for:
- Bug 1: SIGKILL targets entire process group, not just main process
- Bug 2: OSError caught in killpg (race between getpgid and killpg)
- Bug 3: Timeout on post-SIGKILL wait (D-state processes)
- Bug 4: hol_stop doesn't pop session before stop() completes
"""

import asyncio
import os
import signal
from unittest.mock import AsyncMock, MagicMock, patch, call

import pytest

from hol4_mcp.hol_session import HOLSession


def _make_mock_process(pid=1234, returncode=None):
    """Create a mock asyncio.subprocess.Process."""
    proc = MagicMock()
    proc.pid = pid
    proc.returncode = returncode
    proc.wait = AsyncMock(return_value=0)
    return proc


# --- Bug 1: SIGKILL should target entire process group ---


async def test_stop_timeout_uses_killpg_not_process_kill():
    """After SIGTERM timeout, stop() should SIGKILL the process GROUP
    (os.killpg), not just the main process (self.process.kill()).

    Regression: self.process.kill() only kills the parent; orphaned
    Poly/ML GC threads leak memory.
    """
    session = HOLSession()
    proc = _make_mock_process()
    session.process = proc

    # SIGTERM wait times out → should fall into SIGKILL path
    proc.wait = AsyncMock(side_effect=[asyncio.TimeoutError(), asyncio.TimeoutError()])

    with patch("hol4_mcp.hol_session.os.getpgid", return_value=100), \
         patch("hol4_mcp.hol_session.os.killpg") as mock_killpg:
        await session.stop()

    # Must see SIGTERM then SIGKILL both via killpg
    calls = mock_killpg.call_args_list
    assert any(c == call(100, signal.SIGTERM) for c in calls), \
        f"Expected SIGTERM via killpg, got: {calls}"
    assert any(c == call(100, signal.SIGKILL) for c in calls), \
        f"Expected SIGKILL via killpg, got: {calls}"
    # Must NOT call proc.kill() (only kills main process)
    proc.kill.assert_not_called()


# --- Bug 2: OSError should be caught in all killpg calls ---


async def test_stop_sigterm_catches_oserror():
    """OSError from killpg (e.g. race: leader died after getpgid) should
    not propagate — catch (ProcessLookupError, PermissionError, OSError)."""
    session = HOLSession()
    proc = _make_mock_process()
    session.process = proc

    with patch("hol4_mcp.hol_session.os.getpgid", return_value=100), \
         patch("hol4_mcp.hol_session.os.killpg", side_effect=OSError("no such pgid")):
        # Should not raise
        await session.stop()


async def test_stop_sigkill_catches_oserror():
    """OSError from killpg SIGKILL path should also not propagate."""
    session = HOLSession()
    proc = _make_mock_process()
    session.process = proc

    # SIGTERM works, but wait times out; SIGKILL raises OSError
    proc.wait = AsyncMock(side_effect=[asyncio.TimeoutError()])

    with patch("hol4_mcp.hol_session.os.getpgid", return_value=100), \
         patch("hol4_mcp.hol_session.os.killpg",
               side_effect=[None, OSError("already dead")]) as mock_killpg:
        # Should not raise
        await session.stop()


# --- Bug 3: Post-SIGKILL wait should have a timeout ---


async def test_stop_post_sigkill_wait_has_timeout():
    """After SIGKILL, wait() should have a timeout (not hang forever
    on D-state/uninterruptible processes)."""
    session = HOLSession()
    proc = _make_mock_process()
    session.process = proc

    # SIGTERM times out, SIGKILL sent, then wait times out too (D-state)
    proc.wait = AsyncMock(
        side_effect=[asyncio.TimeoutError(), asyncio.TimeoutError()]
    )

    with patch("hol4_mcp.hol_session.os.getpgid", return_value=100), \
         patch("hol4_mcp.hol_session.os.killpg"):
        # Should complete (not hang), both waits timed out
        await session.stop()


async def test_stop_waits_after_sigterm():
    """stop() should wait for process to exit after SIGTERM before
    escalating to SIGKILL."""
    session = HOLSession()
    proc = _make_mock_process()
    session.process = proc

    # Process exits cleanly after SIGTERM
    proc.wait = AsyncMock(return_value=0)

    with patch("hol4_mcp.hol_session.os.getpgid", return_value=100), \
         patch("hol4_mcp.hol_session.os.killpg") as mock_killpg:
        await session.stop()

    # Only SIGTERM should have been sent; no SIGKILL
    calls = mock_killpg.call_args_list
    assert calls == [call(100, signal.SIGTERM)], \
        f"Expected only SIGTERM, got: {calls}"


# --- Shared: stop() cleans up state ---


async def test_stop_clears_process_and_buffer():
    """After stop(), process and buffer should be reset."""
    session = HOLSession()
    proc = _make_mock_process()
    session.process = proc
    session._buffer = b"stale data"

    with patch("hol4_mcp.hol_session.os.getpgid", return_value=100), \
         patch("hol4_mcp.hol_session.os.killpg"):
        await session.stop()

    assert session.process is None
    assert session._buffer == b""


async def test_stop_noop_if_not_running():
    """stop() on an already-stopped session should be a no-op."""
    session = HOLSession()
    session.process = None
    # Should not raise
    await session.stop()


# --- Bug 4: hol_stop pops session AFTER successful stop ---


async def test_hol_stop_preserves_session_on_stop_failure():
    """If session.stop() raises, the session entry should still be in
    _sessions (not leaked as an orphan).

    Regression: _sessions.pop(session) before stop() meant a failing
    stop() leaked the HOL process — no entry to clean up later.
    """
    from hol4_mcp.hol_mcp_server import _sessions, hol_stop
    from hol4_mcp.hol_session import HOLSession

    # Create a mock session entry
    mock_session = MagicMock(spec=HOLSession)
    mock_session.stop = AsyncMock(side_effect=RuntimeError("stop failed"))
    mock_entry = MagicMock()
    mock_entry.session = mock_session

    # Inject into _sessions
    _sessions["test_leak"] = mock_entry

    # stop() raises, but session should still be in _sessions for cleanup
    with pytest.raises(RuntimeError, match="stop failed"):
        await hol_stop(session="test_leak")

    # Key assertion: entry is still registered (not popped/leaked)
    assert "test_leak" in _sessions, \
        "Session entry should remain in _sessions when stop() fails"

    # Clean up
    del _sessions["test_leak"]


async def test_hol_stop_removes_session_on_success():
    """After successful stop(), session should be removed from _sessions."""
    from hol4_mcp.hol_mcp_server import _sessions, hol_stop
    from hol4_mcp.hol_session import HOLSession

    mock_session = MagicMock(spec=HOLSession)
    mock_session.stop = AsyncMock()
    mock_entry = MagicMock()
    mock_entry.session = mock_session

    _sessions["test_success"] = mock_entry

    result = await hol_stop(session="test_success")

    assert "test_success" not in _sessions
    assert "stopped" in result.lower()


async def test_hol_stop_not_found():
    """Stopping a non-existent session should return 'not found'."""
    from hol4_mcp.hol_mcp_server import _sessions, hol_stop

    # Ensure session doesn't exist
    _sessions.pop("nonexistent_test", None)

    result = await hol_stop(session="nonexistent_test")
    assert "not found" in result.lower()
