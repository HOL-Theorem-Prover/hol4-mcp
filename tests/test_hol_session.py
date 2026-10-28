"""Tests for HOL session subprocess wrapper."""

import asyncio
import sys

import pytest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, Mock

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_cursor import _is_hol_error

FIXTURES_DIR = Path(__file__).parent / "fixtures"


async def test_server_applies_and_restarts_with_explicit_heap_configuration(tmp_path):
    from hol4_mcp import hol_mcp_server as srv
    name = "heap_configuration"
    try:
        result = await srv.hol_start(str(tmp_path), name=name,
                                     env={"HOL4_MCP_MAXHEAP_MB": "12288"})
        assert "maxheap=12288 MB" in result, result
        original_pid = srv._sessions[name].session.process.pid
        assert srv._sessions[name].session.maxheap_mb == 12288
        result = await srv.hol_setenv({"HOL4_MCP_MAXHEAP_MB": "10240"}, session=name)
        assert "maxheap=10240 MB" in result, result
        assert srv._sessions[name].session.process.pid != original_pid
        assert srv._sessions[name].session.maxheap_mb == 10240
        assert "2" in await srv.hol_send("1 + 1;", session=name)
    finally:
        await srv.hol_stop(session=name)


@pytest.mark.parametrize("inherited,explicit,expected", [
    (None, None, 8192), ("10240", None, 10240),
    ("10240", "12288", 12288), (None, "256", 256),
])
async def test_interactive_heap_configuration(monkeypatch, tmp_path,
                                              inherited, explicit, expected):
    monkeypatch.delenv("HOL4_MCP_MAXHEAP_MB", raising=False)
    if inherited is not None:
        monkeypatch.setenv("HOL4_MCP_MAXHEAP_MB", inherited)
    env = {"HOL4_MCP_MAXHEAP_MB": explicit} if explicit is not None else None
    session = HOLSession(str(tmp_path), env=env)
    spawn = AsyncMock(return_value=SimpleNamespace(pid=123, returncode=None))
    monkeypatch.setattr("asyncio.create_subprocess_exec", spawn)
    monkeypatch.setattr(session, "_read_response", AsyncMock(return_value=""))
    monkeypatch.setattr(session, "send", AsyncMock(return_value=""))
    result = await session.start()
    args = spawn.call_args.args
    assert args[args.index("--maxheap") + 1] == str(expected)
    assert session.maxheap_mb == expected and f"maxheap={expected} MB" in result


@pytest.mark.parametrize("value", ["", "0", "255", "-1", "12GiB", "8192.0"])
async def test_bad_interactive_heap_does_not_spawn(monkeypatch, tmp_path, value):
    spawn = AsyncMock()
    monkeypatch.setattr("asyncio.create_subprocess_exec", spawn)
    session = HOLSession(str(tmp_path), env={"HOL4_MCP_MAXHEAP_MB": value})
    with pytest.raises(ValueError, match="HOL4_MCP_MAXHEAP_MB"):
        await session.start()
    spawn.assert_not_called()


@pytest.mark.parametrize("phase", ["prompt", "helpers"])
@pytest.mark.parametrize("failure", [TimeoutError, asyncio.CancelledError])
async def test_startup_failure_reaps_process_and_allows_retry(monkeypatch, tmp_path, phase, failure):
    # A real child pins process cleanup without waiting for a real HOL timeout.
    spawn = asyncio.create_subprocess_exec
    children = []

    async def spawn_idle(*args, **kwargs):
        child = await spawn(sys.executable, "-c", "import time; time.sleep(60)", **kwargs)
        children.append(child)
        return child

    monkeypatch.setattr(asyncio, "create_subprocess_exec", spawn_idle)
    session = HOLSession(str(tmp_path))
    reader = AsyncMock(return_value="")
    sender = AsyncMock(return_value="")
    (reader if phase == "prompt" else sender).side_effect = failure("startup failed")
    monkeypatch.setattr(session, "_read_response", reader)
    monkeypatch.setattr(session, "send", sender)
    try:
        with pytest.raises(failure, match="startup failed"):
            async with session:
                pytest.fail("failed startup must not enter the context")
        assert children[0].returncode is not None, "startup leaked its child"
        assert session.process is None
        reader.side_effect = sender.side_effect = None
        assert "HOL started" in await session.start()
        assert len(children) == 2
        assert session.process is children[1]
    finally:
        await session.stop()
        for child in children:
            if child.returncode is None:
                child.kill()
                await child.wait()


async def test_startup_reports_init_errors_and_reaps_process(tmp_path):
    (tmp_path / ".hol_init.sml").write_text('raise Fail "broken startup file";\n')
    session = HOLSession(str(tmp_path))
    try:
        with pytest.raises(RuntimeError, match="broken startup file"):
            await session.start()
        assert session.process is None
    finally:
        await session.stop()


async def test_too_old_hol_is_reported_plainly(monkeypatch, tmp_path):
    from hol4_mcp import hol_mcp_server as srv
    # The probe as an older TacticParse, with span-less combinators, would
    # accept it; against the current one it fails like the real probe there.
    monkeypatch.setattr("hol4_mcp.hol_session._TACTICPARSE_PROBE",
                        "val _ = TacticParse.FOpenBy (0, 0);")
    name = "too_old_hol"
    try:
        result = await srv.hol_start(str(tmp_path), name=name)
        assert result.startswith("ERROR starting HOL: the HOL at "), result
        assert "too old for hol4-mcp" in result and "current master" in result, result
        assert "tactic_prefix" not in result and "Type error" not in result, result
        assert name not in srv._sessions
    finally:
        await srv.hol_stop(session=name)


async def test_stop_handles_process_group_lookup_failure(monkeypatch, tmp_path):
    session = HOLSession(str(tmp_path))
    process = SimpleNamespace(pid=123, returncode=None,
                              wait=AsyncMock(side_effect=[TimeoutError, 0]))
    session.process = process
    monkeypatch.setattr("hol4_mcp.hol_session.os.getpgid", Mock(side_effect=PermissionError))
    kill = Mock()
    monkeypatch.setattr("hol4_mcp.hol_session.os.killpg", kill)
    await session.stop()
    assert session.process is None
    assert process.wait.await_count == 2
    kill.assert_not_called()


async def test_hol_session():
    """Test HOL session basic functionality."""
    session = HOLSession(str(FIXTURES_DIR))
    try:
        result = await session.start()
        assert "HOL started" in result

        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result

        assert session.is_running
    finally:
        await session.stop()
        assert not session.is_running


async def test_hol_session_context_manager():
    """Test HOL session as async context manager."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        assert session.is_running
        result = await session.send('3 + 4;', timeout=10)
        assert "7" in result
        assert session.is_running
    assert not session.is_running


async def test_hol_session_interrupt():
    """Test interrupting a long-running HOL command."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Start a long-running computation via short timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should still be usable after interrupt
        assert session.is_running
        result = await session.send('1 + 1;', timeout=10)
        assert "2" in result


async def test_hol_session_send_not_running():
    """Test sending to a stopped session returns error."""
    session = HOLSession(str(FIXTURES_DIR))
    result = await session.send('1 + 1;', timeout=10)
    assert "ERROR" in result


async def test_hol_session_start_already_running():
    async with HOLSession(str(FIXTURES_DIR)) as session:
        pid = session.process.pid
        result = await session.start()
        assert "already running" in result.lower()
        assert session.process.pid == pid


async def test_hol_session_sequential_sends():
    """Test sequential sends return correct outputs in order."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        for i in range(10):
            result = await session.send(f'{i};', timeout=10)
            assert str(i) in result, f"Expected {i} in result, got: {result}"


async def test_hol_session_post_interrupt_sync():
    """Test that session resyncs correctly after interrupt.

    After timeout/interrupt, buffer and pipe may have stale data.
    Verify subsequent commands work correctly.
    """
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Trigger interrupt with a timeout
        result = await session.send('fun loop () = loop (); loop ();', timeout=1)
        assert "TIMEOUT" in result or "interrupt" in result.lower()

        # Session should resync - send a few commands and verify correct outputs
        for i in range(5):
            result = await session.send(f'{100 + i};', timeout=10)
            assert str(100 + i) in result, f"Expected {100+i} after interrupt, got: {result}"


# Unit tests for escape_sml_string

def test_escape_sml_string_backslash():
    """Backslash should be doubled for SML string literal."""
    assert escape_sml_string('/\\') == '/\\\\'
    assert escape_sml_string('A /\\ B') == 'A /\\\\ B'


def test_escape_sml_string_quote():
    """Double quotes should be escaped."""
    assert escape_sml_string('SPEC "x"') == 'SPEC \\"x\\"'


def test_escape_sml_string_newline():
    """Newlines should become \\n."""
    assert escape_sml_string('foo\nbar') == 'foo\\nbar'


def test_escape_sml_string_tab():
    """Tabs should become \\t."""
    assert escape_sml_string('foo\tbar') == 'foo\\tbar'


def test_escape_sml_string_carriage_return():
    """Carriage returns should become \\r."""
    assert escape_sml_string('foo\rbar') == 'foo\\rbar'


def test_escape_sml_string_combined():
    """Test multiple escape sequences together."""
    # /\ with newline and embedded quote
    assert escape_sml_string('`T /\\ T`\nby SPEC "x"') == '`T /\\\\ T`\\nby SPEC \\"x\\"'


def test_escape_sml_string_no_change():
    """Regular strings pass through unchanged."""
    assert escape_sml_string('simp[]') == 'simp[]'
    assert escape_sml_string('strip_tac') == 'strip_tac'


# Tests for _is_hol_error with real HOL output

async def test_is_hol_error_detects_syntax_error():
    """Poly/ML syntax errors should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('val x = ;', timeout=10)  # syntax error
        assert _is_hol_error(result), f"Should detect syntax error: {result}"


async def test_is_hol_error_detects_type_error():
    """Poly/ML type errors should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('val x : int = "hello";', timeout=10)
        assert _is_hol_error(result), f"Should detect type error: {result}"


async def test_is_hol_error_detects_exception():
    """SML exceptions should be detected."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        result = await session.send('raise Fail "test";', timeout=10)
        assert _is_hol_error(result), f"Should detect exception: {result}"


async def test_is_hol_error_ignores_error_in_term():
    """The word 'error' in a term should NOT trigger error detection."""
    async with HOLSession(str(FIXTURES_DIR)) as session:
        # Define a value with "error" in the name - this is valid SML
        result = await session.send('val error_state = 42;', timeout=10)
        assert not _is_hol_error(result), f"Should not flag 'error' in identifier: {result}"

        # Use "error" in a HOL term
        result = await session.send('val t = ``is_error x``;', timeout=10)
        assert not _is_hol_error(result), f"Should not flag 'error' in term: {result}"


def test_is_hol_error_detects_timeout():
    """_is_hol_error catches TIMEOUT strings from send()."""
    assert _is_hol_error("TIMEOUT after 30s - sent interrupt.")
    assert _is_hol_error("TIMEOUT after 5s - sent interrupt.\npartial output")


def test_is_hol_error_detects_error_prefix():
    """_is_hol_error catches ERROR: sentinel outputs."""
    assert _is_hol_error("ERROR: HOL not running")
    assert _is_hol_error("Error: HOL not running")
