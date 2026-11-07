"""A session's HOL environment (the heap limit above all) belongs to the
session name, not to one process: every automatic start reuses it, whatever
dropped the previous process, and says that it started one."""
import os
import signal
import time

import pytest

from hol4_mcp import hol_mcp_server
from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    _sessions,
    hol_send,
    hol_sessions,
    hol_setenv,
    hol_start,
    hol_state_at,
    hol_stop,
)

SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "{name}";

Theorem t1:
  T
Proof
  simp[]
QED

val _ = export_theory();
"""

HEAP = "2048"


def _script(directory, name="envs"):
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{name}Script.sml"
    path.write_text(SCRIPT.replace("{name}", name))
    return path


def _heap(session: str) -> int | None:
    entry = _sessions.get(session)
    return entry.session.maxheap_mb if entry else None


def _cmdline_heap(session: str) -> str:
    """The --maxheap the live Poly/ML process was started with."""
    root = _sessions[session].session.process.pid
    pids = [root]
    for task in os.listdir(f"/proc/{root}/task"):
        children = open(f"/proc/{root}/task/{task}/children").read().split()
        pids.extend(int(c) for c in children)
    for pid in pids:
        args = open(f"/proc/{pid}/cmdline", "rb").read().split(b"\0")
        for i, arg in enumerate(args):
            if arg == b"--maxheap" and i + 1 < len(args):
                return args[i + 1].decode()
    return ""


async def _start(script, session, heap=HEAP):
    started = await hol_start(workdir=str(script.parent), name=session,
                              env={"HOL4_MCP_MAXHEAP_MB": heap})
    assert "started" in started, started
    await _init_file_cursor(file=str(script), session=session)
    assert _heap(session) == int(heap)


@pytest.fixture
def forget_session_env():
    yield
    getattr(hol_mcp_server, "_session_envs", {}).clear()


async def test_setenv_accepts_an_integer_heap(tmp_path, forget_session_env):
    script = _script(tmp_path)
    session = "env_int"
    try:
        await _start(script, session)
        result = await hol_setenv({"HOL4_MCP_MAXHEAP_MB": 1536}, session=session)
        assert "ERROR" not in result, result
        assert _heap(session) == 1536
        assert _cmdline_heap(session) == "1536"
    finally:
        await hol_stop(session=session)


async def test_a_pruned_session_restarts_with_its_heap(tmp_path, monkeypatch,
                                                       forget_session_env):
    script = _script(tmp_path)
    session = "env_prune"
    try:
        await _start(script, session)
        _sessions[session].last_used = time.time() - 10 * hol_mcp_server._SESSION_IDLE_TIMEOUT
        monkeypatch.setattr(hol_mcp_server, "_last_prune_time", 0.0)
        # A call serialized on another session (or none) prunes this one.
        await hol_sessions()
        assert session not in _sessions
        state = await hol_state_at(line=8, col=3, file=str(script), session=session)
        assert "=== Goal" in state, state
        assert _heap(session) == int(HEAP)
        assert "idle" in state and f"{HEAP} MB" in state, state
    finally:
        await hol_stop(session=session)


async def test_a_dead_session_restarts_with_its_heap(tmp_path, forget_session_env):
    script = _script(tmp_path)
    session = "env_dead"
    try:
        await _start(script, session)
        os.killpg(_sessions[session].session.process.pid, signal.SIGKILL)
        await _sessions[session].session.process.wait()
        assert "died" in await hol_send("1;", session=session)
        state = await hol_state_at(line=8, col=3, file=str(script), session=session)
        assert "=== Goal" in state, state
        assert _heap(session) == int(HEAP)
        assert f"{HEAP} MB" in state, state
    finally:
        await hol_stop(session=session)


async def test_a_workdir_round_trip_and_a_stop_keep_the_heap(tmp_path, forget_session_env):
    first = _script(tmp_path / "a", "enva")
    second = _script(tmp_path / "b", "envb")
    session = "env_workdir"
    try:
        await _start(first, session)
        state = await hol_state_at(line=8, col=3, file=str(second), session=session)
        assert "=== Goal" in state and _heap(session) == int(HEAP), state
        state = await hol_state_at(line=8, col=3, file=str(first), session=session)
        assert "=== Goal" in state and _heap(session) == int(HEAP), state
        await hol_stop(session=session)
        state = await hol_state_at(line=8, col=3, file=str(first), session=session)
        assert "=== Goal" in state, state
        assert _heap(session) == int(HEAP)
    finally:
        await hol_stop(session=session)


async def test_a_long_call_does_not_make_the_session_look_idle(tmp_path, monkeypatch,
                                                               forget_session_env):
    script = _script(tmp_path)
    session = "env_long"
    try:
        await _start(script, session)
        monkeypatch.setattr(hol_mcp_server, "_SESSION_IDLE_TIMEOUT", 1.5)
        monkeypatch.setattr(hol_mcp_server, "_PRUNE_INTERVAL", 0.0)
        await hol_send("OS.Process.sleep (Time.fromSeconds 3);", session=session)
        await hol_sessions()
        assert session in _sessions
    finally:
        await hol_stop(session=session)


async def test_hol_start_on_a_running_session_names_an_unapplied_env(tmp_path,
                                                                     forget_session_env):
    script = _script(tmp_path)
    session = "env_running"
    try:
        await _start(script, session)
        reply = await hol_start(workdir=str(tmp_path), name=session,
                                env={"HOL4_MCP_MAXHEAP_MB": "4096"})
        assert "already running" in reply and "hol_setenv" in reply, reply
        assert _heap(session) == int(HEAP)
    finally:
        await hol_stop(session=session)


async def test_a_timeout_at_the_heap_limit_names_the_pressure(tmp_path, monkeypatch,
                                                              forget_session_env):
    from hol4_mcp.hol_session import HOLSession
    monkeypatch.setattr(HOLSession, "resident_mb",
                        lambda self: int(self.maxheap_mb * 0.95))
    script = tmp_path / "loopsScript.sml"
    script.write_text(SCRIPT.replace("{name}", "loops").replace(
        "  simp[]", "  REPEAT ALL_TAC \\\\ simp[]"))
    session = "env_pressure"
    try:
        await _start(script, session)
        state = await hol_state_at(line=9, col=1, session=session, timeout=5)
        assert "TIMEOUT" in state, state
        assert "Heap pressure" in state and "hol_setenv" in state, state
    finally:
        await hol_stop(session=session)


async def test_the_default_heap_is_half_of_ram(tmp_path, monkeypatch, forget_session_env):
    monkeypatch.delenv("HOL4_MCP_MAXHEAP_MB", raising=False)
    total_kb = next(int(line.split()[1]) for line in open("/proc/meminfo")
                    if line.startswith("MemTotal:"))
    expected = max(8192, total_kb // 1024 // 2)
    script = _script(tmp_path)
    session = "env_default"
    try:
        await _init_file_cursor(file=str(script), session=session)
        assert _heap(session) == expected
    finally:
        await hol_stop(session=session)
