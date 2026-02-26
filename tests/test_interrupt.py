"""Test SIGINT interrupt handling for hol4-mcp server.

Tests that:
1. SIGINT handler is installed
2. SIGINT interrupts HOL sessions
3. Server survives SIGINT and continues serving requests
"""

import asyncio
import os
import signal

import pytest

from hol4_mcp.hol_mcp_server import (
    _sigint_handler,
    _sessions,
    hol_start as _hol_start,
    hol_send as _hol_send,
    hol_sessions as _hol_sessions,
    hol_stop as _hol_stop,
    hol_interrupt as _hol_interrupt,
)

# In FastMCP 3.x, @mcp.tool() returns the original function unchanged
hol_start = _hol_start
hol_send = _hol_send
hol_sessions = _hol_sessions
hol_stop = _hol_stop
hol_interrupt = _hol_interrupt


async def test_sigint_handler_installed():
    """Test that SIGINT handler is installed in the server."""
    # The handler should be installed at module load time
    current_handler = signal.getsignal(signal.SIGINT)
    assert current_handler == _sigint_handler, "SIGINT handler not installed"


async def test_sigint_handler_callable():
    """Test that SIGINT handler is a callable function."""
    assert callable(_sigint_handler)


async def test_hol_interrupt_tool():
    """Test the hol_interrupt tool sends SIGINT to session."""
    # Start a session
    result = await hol_start(workdir="/tmp", name="test_interrupt_tool")
    assert "started" in result.lower() or "running" in result.lower()
    
    try:
        # Call hol_interrupt
        result = await hol_interrupt(session="test_interrupt_tool")
        assert "SIGINT" in result
    finally:
        await hol_stop(session="test_interrupt_tool")


async def test_sigint_during_command():
    """Test that SIGINT interrupts a running HOL command."""
    result = await hol_start(workdir="/tmp", name="test_sigint_cmd")
    assert "started" in result.lower() or "running" in result.lower()
    
    try:
        # Start a long-running command
        async def long_command():
            return await hol_send(
                session="test_sigint_cmd",
                command="let val _ = OS.Process.sleep (Time.fromSeconds 30) in 1 end;",
                timeout=60
            )
        
        task = asyncio.create_task(long_command())
        
        # Wait a bit then send interrupt
        await asyncio.sleep(1)
        
        # Get the session and interrupt it directly
        entry = _sessions.get("test_sigint_cmd")
        assert entry is not None
        entry.session.interrupt()
        
        # Command should complete with interrupt
        result = await asyncio.wait_for(task, timeout=5)
        assert "Interrupt" in result
        
    finally:
        await hol_stop(session="test_sigint_cmd")


async def test_sigint_handler_interrupts_all_sessions():
    """Test that SIGINT handler interrupts all running sessions."""
    # Start two sessions
    await hol_start(workdir="/tmp", name="test_sigint_1")
    await hol_start(workdir="/tmp", name="test_sigint_2")
    
    try:
        # Verify both sessions exist
        result = await hol_sessions()
        assert "test_sigint_1" in result
        assert "test_sigint_2" in result
        
        # Call the handler directly (simulates receiving SIGINT)
        _sigint_handler(signal.SIGINT, None)
        
        # Sessions should still be running (interrupt doesn't kill them)
        result = await hol_sessions()
        assert "test_sigint_1" in result
        assert "test_sigint_2" in result
        
    finally:
        await hol_stop(session="test_sigint_1")
        await hol_stop(session="test_sigint_2")


async def test_session_survives_interrupt():
    """Test that a session survives interrupt and can be used again."""
    await hol_start(workdir="/tmp", name="test_survive")
    
    try:
        # Send a command
        result = await hol_send(session="test_survive", command="1 + 1;")
        assert "val it = 2" in result
        
        # Send interrupt
        await hol_interrupt(session="test_survive")
        
        # Session should still work
        await asyncio.sleep(0.5)  # Give it a moment
        result = await hol_send(session="test_survive", command="2 + 2;")
        assert "val it = 4" in result
        
    finally:
        await hol_stop(session="test_survive")


async def test_interrupt_nonexistent_session():
    """Test that interrupting a nonexistent session returns error."""
    result = await hol_interrupt(session="nonexistent_session_xyz")
    assert "ERROR" in result or "not found" in result.lower()


async def test_interrupt_empty_sessions():
    """Test that SIGINT handler works with no sessions."""
    # Clear any existing sessions first
    for name in list(_sessions.keys()):
        await hol_stop(session=name)
    
    # Should not raise
    _sigint_handler(signal.SIGINT, None)


async def test_double_interrupt():
    """Test that double interrupt doesn't crash."""
    await hol_start(workdir="/tmp", name="test_double")
    
    try:
        # Send two interrupts in quick succession
        await hol_interrupt(session="test_double")
        await hol_interrupt(session="test_double")
        
        # Session should still work
        await asyncio.sleep(0.3)
        result = await hol_send(session="test_double", command="1;")
        assert "val it = 1" in result
    finally:
        await hol_stop(session="test_double")
