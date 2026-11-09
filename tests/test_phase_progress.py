"""Progress inspection is read-only and timeout advice follows the measured phase."""
import asyncio
import time
from datetime import datetime
from types import SimpleNamespace
from unittest.mock import AsyncMock

from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp import hol_mcp_server as srv


async def test_prefix_progress_is_visible_without_hol_command(tmp_path, monkeypatch):
    entered, release = asyncio.Event(), asyncio.Event()

    async def send(command, timeout=5):
        entered.set()
        await release.wait()
        return "OK.."

    session = SimpleNamespace(send=AsyncMock(side_effect=send), is_running=True,
                              workdir=tmp_path)
    cursor = FileProofCursor(tmp_path / "progressScript.sml", session)
    entry = srv.SessionEntry(session, datetime.now(), tmp_path)
    entry.cursor = cursor
    monkeypatch.setattr(srv, "_sessions", {"progress": entry})
    task = asyncio.create_task(cursor._send_and_check("val x = 1;", 300, 2, 900))
    try:
        await asyncio.wait_for(entered.wait(), 2)
        result = await srv.hol_sessions()
        assert "top-level SML/translation" in result and "lines 2-900" in result
        assert "Elapsed" in result and "300s" in result
        assert session.send.await_count == 1
    finally:
        release.set()
        await task
    assert not cursor._phase["active"]


async def test_busy_session_is_not_pruned_by_status(tmp_path, monkeypatch):
    lock = asyncio.Lock()
    session = SimpleNamespace(_lock=lock, stop=AsyncMock())
    entry = srv.SessionEntry(session, datetime.now(), tmp_path)
    entry.last_used = time.time() - srv._SESSION_IDLE_TIMEOUT - 60
    monkeypatch.setattr(srv, "_sessions", {"busy": entry})
    monkeypatch.setattr(srv, "_last_prune_time", 0)
    async with lock:
        await srv._prune_idle_sessions()
    assert "busy" in srv._sessions
    session.stop.assert_not_called()


async def test_cancelled_prefix_retains_honest_timeout_phase(tmp_path):
    async def hang(command, timeout=5):
        await asyncio.Event().wait()

    cursor = FileProofCursor(tmp_path / "progressScript.sml",
                             SimpleNamespace(send=hang))
    try:
        await asyncio.wait_for(cursor._send_and_check("val x = 1;", 300, 2, 900), .01)
    except asyncio.TimeoutError:
        pass
    assert cursor._phase["interrupted"] and not cursor._phase["active"]
    result = srv._timeout_error_text(300, 300, 0, False, cursor._phase)
    assert "lines 2-900" in result
    assert "current file's declarations/translation" in result
    assert "build the ancestors (holmake)" not in result


async def test_failed_resync_after_budget_abort_schedules_restart():
    async def hang(*args, **kwargs):
        await asyncio.Event().wait()

    session = SimpleNamespace(interrupt=lambda: None, resync=AsyncMock(return_value=False))
    reinit = []
    cursor = SimpleNamespace(
        state_at=hang, session=session, mark_interrupted=lambda: None, _phase={},
        _schedule_full_reinit=lambda reason=None: reinit.append(reason))
    result = await srv._state_at_budgeted(cursor, 1, timeout=0.05)
    assert "NOT recovered" in result.error and "restarts" in result.error, result.error
    assert reinit, "an unsynchronised pipe must force a fresh HOL process"
    session.resync.return_value = True
    reinit.clear()
    result = await srv._state_at_budgeted(cursor, 1, timeout=0.05)
    assert "session recovered" in result.error and not reinit, result.error


def test_slow_prefix_does_not_blame_target_proof():
    for _ in range(3):
        lines = srv._slow_nav_lines("prefix", "file", "trivial", 200, 199)
        assert "Slow prefix/setup" in "".join(lines)
        assert "PROCESS FAILURE" not in "".join(lines)
    # Slow target behavior stays separate, and retains the existing warning.
    srv._slow_nav_counts.pop(("target", "file", "loop"), None)
    assert not srv._slow_nav_lines("target", "file", "loop", 200, 1)
    assert "SLOW NAVIGATION #2" in "".join(
        srv._slow_nav_lines("target", "file", "loop", 200, 1))


def test_slow_navigation_count_resets_after_proof_revision_changes():
    key = ("revised", "file", "theorem")
    srv._slow_nav_counts.pop(key, None)
    assert not srv._slow_nav_lines(
        "revised", "file", "theorem", 200, 1, revision="before"
    )
    assert not srv._slow_nav_lines(
        "revised", "file", "theorem", 200, 1, revision="after"
    )
    assert "SLOW NAVIGATION #2" in "".join(srv._slow_nav_lines(
        "revised", "file", "theorem", 200, 1, revision="after"
    ))


def test_preceding_theorem_timeout_names_preceding_theorem():
    result = srv._timeout_error_text(300, 300, 0, False,
        {"phase": "preceding theorem", "item": "earlier", "budget": 120,
         "start_line": 12, "end_line": 90})
    assert "earlier" in result and "lines 12-90" in result
    assert "not the target proof" in result
