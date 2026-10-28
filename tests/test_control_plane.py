"""Interrupting and replacing a session while a call is running on it.

1. A Resume body that diverges while a later label is navigated to:
   hol_interrupt returns at once and the navigation returns as interrupted.
2. A hol_send whose loop outlives its timeout: the next call does not write
   into the busy process, and hol_restart replaces the session.
3. A reply that never arrives while HOL sits idle: hol_interrupt says HOL is
   idle, the waiting call returns, and the session answers again.
"""
import asyncio
import time

from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    _sessions,
    hol_interrupt,
    hol_restart,
    hol_send,
    hol_start,
    hol_state_at,
    hol_stop,
)

SPIN = "(fn g => (let fun spin (n:int) = spin (n + 1) in spin 0 end; ALL_TAC g))"

RESUME_SCRIPT = f"""\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "cpl";

Theorem main:
  T /\\ T
Proof
  conj_tac >- suspend "a" >> suspend "b"
QED

Resume main[a]:
  {SPIN}
QED

Resume main[b]:
  simp[]
QED

val _ = export_theory();
"""


async def _started(task, seconds):
    await asyncio.sleep(seconds)
    assert not task.done(), task.result()


async def test_interrupt_stops_a_diverging_resume_load(tmp_path):
    script = tmp_path / "cplScript.sml"
    script.write_text(RESUME_SCRIPT)
    session = "cp_resume_spin"
    try:
        await _init_file_cursor(file=str(script), session=session)
        navigation = asyncio.create_task(hol_state_at(line=16, col=3, session=session))
        await _started(navigation, 3)
        t0 = time.monotonic()
        reply = await asyncio.wait_for(hol_interrupt(session=session), 10)
        assert time.monotonic() - t0 < 5, reply
        assert "interrupted" in reply.lower() and "hol_state_at" in reply, reply
        result = await asyncio.wait_for(navigation, 10)
        assert result.startswith("INTERRUPTED") and "re-run" in result, result
        assert "val it = 1" in await hol_send("1;", session=session)
    finally:
        await hol_stop(session=session)


async def test_timed_out_send_does_not_feed_a_busy_process(tmp_path):
    session = "cp_busy_send"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        # SIGINT ignored: the loop stands for code that never reaches a point
        # where Poly/ML acts on an interrupt.
        first = await hol_send(
            "val _ = Signal.signal (Posix.Signal.int, Signal.SIG_IGN); "
            "val _ = let fun f (x:int) = f (x + 1) in f 0 end;",
            timeout=1, session=session)
        assert first.startswith("TIMEOUT") and "still busy" in first, first
        assert "hol_stop" in first, first
        t0 = time.monotonic()
        nxt = await hol_send("1;", timeout=5, session=session)
        assert time.monotonic() - t0 < 3, nxt
        assert "still busy" in nxt and "Nothing was sent" in nxt and "hol_stop" in nxt, nxt
        restarted = await asyncio.wait_for(hol_restart(session=session), 60)
        assert "started" in restarted, restarted
        assert "val it = 2" in await hol_send("2;", session=session)
    finally:
        await hol_stop(session=session)


async def test_interrupt_recovers_a_lost_reply(tmp_path):
    session = "cp_lost_reply"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        hol = _sessions[session].session
        read = hol._read_response
        dropped = []

        async def drop_first_frame(timeout):
            if not dropped:
                dropped.append(await read(timeout))
            return await read(timeout)
        hol._read_response = drop_first_frame
        waiting = asyncio.create_task(hol_send("1;", timeout=60, session=session))
        await _started(waiting, 1.5)
        hol._read_response = read
        reply = await asyncio.wait_for(hol_interrupt(session=session), 10)
        assert "no CPU" in reply and "lost" in reply, reply
        result = await asyncio.wait_for(waiting, 10)
        assert result.startswith("INTERRUPTED"), result
        assert "val it = 2" in await hol_send("2;", session=session)
    finally:
        await hol_stop(session=session)


class _RecordingSession:
    """Answers the replay batch with `batch_reply`, everything else with ''."""

    def __init__(self, batch_reply):
        self.batch_reply = batch_reply
        self.sent = []

    async def send(self, command, timeout=None):
        self.sent.append(command)
        return self.batch_reply if len(self.sent) == 1 else ""


async def test_fallback_does_not_rerun_an_interrupted_replay(tmp_path):
    from hol4_mcp.hol_cursor import FileProofCursor
    script = tmp_path / "cplScript.sml"
    script.write_text(RESUME_SCRIPT)
    hol = _RecordingSession("> e (simp[]);\nException- Interrupt raised\n")
    cursor = FileProofCursor(script, hol)
    replayed, error = await cursor._replay_steps_with_fallback(
        "main", ["e (conj_tac);\n", "e (simp[]);\n"], batch_timeout=10)
    assert hol.sent == ["e (conj_tac);\ne (simp[]);\n"], hol.sent
    assert replayed == 0 and "interrupted" in error.lower(), error


async def test_interrupted_call_answers_through_the_mcp_protocol(tmp_path):
    from fastmcp import Client
    from hol4_mcp.hol_mcp_server import mcp
    session = "cp_protocol"
    try:
        async with Client(mcp) as client:
            started = await client.call_tool(
                "hol_start", {"workdir": str(tmp_path), "name": session})
            assert "started" in started.content[0].text
            spin = asyncio.create_task(client.call_tool("hol_send", {
                "command": "val _ = let fun f (x:int) = f (x + 1) in f 0 end;",
                "timeout": 120, "session": session}))
            await _started(spin, 1.5)
            reply = await asyncio.wait_for(
                client.call_tool("hol_interrupt", {"session": session}), 15)
            assert "Interrupted the hol_send call" in reply.content[0].text, reply
            result = await asyncio.wait_for(spin, 15)
            assert result.content[0].text.startswith("INTERRUPTED"), result
            again = await client.call_tool("hol_send", {"command": "3;", "session": session})
            assert "val it = 3" in again.content[0].text, again
    finally:
        await hol_stop(session=session)


async def test_two_interrupts_still_get_the_call_its_reply(tmp_path):
    session = "cp_double"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        spin = asyncio.create_task(hol_send(
            "val _ = let fun f (x:int) = f (x + 1) in f 0 end;", timeout=120,
            session=session))
        await _started(spin, 1.5)
        first, second = await asyncio.wait_for(asyncio.gather(
            hol_interrupt(session=session), hol_interrupt(session=session)), 15)
        assert "Interrupted the hol_send call" in first, first
        result = await asyncio.wait_for(spin, 15)
        assert result.startswith("INTERRUPTED"), result
    finally:
        await hol_stop(session=session)


async def test_interrupt_during_a_half_written_command(tmp_path):
    session = "cp_half_write"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        hol = _sessions[session].session
        write = hol._write_command

        async def slow_write(code):
            if "777" not in code:
                return await write(code)
            data = code.encode() + b"\0"
            hol.process.stdin.write(data[:len(data) // 2])
            await hol.process.stdin.drain()
            await asyncio.sleep(2)
            hol.process.stdin.write(data[len(data) // 2:])
            await hol.process.stdin.drain()
        hol._write_command = slow_write
        call = asyncio.create_task(hol_send("val half = 777 + 1;", timeout=30, session=session))
        await _started(call, 0.5)
        reply = await asyncio.wait_for(hol_interrupt(session=session), 30)
        assert "Interrupted the hol_send call" in reply, reply
        result = await asyncio.wait_for(call, 30)
        assert result.startswith("INTERRUPTED"), result
        hol._write_command = write
        for n in (2, 3):
            assert f"val it = {n}" in await hol_send(f"{n};", session=session)
    finally:
        await hol_stop(session=session)


IGNORE_SIGINT_LOOP = ("val _ = Signal.signal (Posix.Signal.int, Signal.SIG_IGN); "
                      "val _ = let fun f (x:int) = f (x + 1) in f 0 end;")
INTERRUPTIBLE_LOOP = "val _ = let fun f (x:int) = f (x + 1) in f 0 end;"


async def test_interrupt_never_kills_a_command_that_ignores_sigint(tmp_path):
    session = "cp_never_kill"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        pid = _sessions[session].session.process.pid
        call = asyncio.create_task(hol_send(IGNORE_SIGINT_LOOP, timeout=300, session=session))
        await _started(call, 1.5)
        reply = await asyncio.wait_for(hol_interrupt(session=session), 40)
        assert "ignores SIGINT" in reply and "hol_stop" in reply, reply
        result = await asyncio.wait_for(call, 10)
        assert result.startswith("INTERRUPTED") and "ignores SIGINT" in result, result
        hol = _sessions[session].session
        assert hol.is_running and hol.process.pid == pid and hol.busy
        refused = await hol_send("1;", session=session)
        assert "Nothing was sent" in refused, refused
        stopped = await asyncio.wait_for(hol_stop(session=session), 20)
        assert "stopped" in stopped, stopped
    finally:
        await hol_stop(session=session)


async def test_restart_preempts_the_running_call(tmp_path):
    session = "cp_restart"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        call = asyncio.create_task(hol_send(INTERRUPTIBLE_LOOP, timeout=300, session=session))
        await _started(call, 1.5)
        restarted = await asyncio.wait_for(hol_restart(session=session), 40)
        assert "started" in restarted and "returns STOPPED" in restarted, restarted
        result = await asyncio.wait_for(call, 10)
        assert result.startswith("STOPPED: hol_restart"), result
        assert "val it = 4" in await hol_send("4;", session=session)
    finally:
        await hol_stop(session=session)


async def test_stop_preempts_the_running_call(tmp_path):
    session = "cp_stop"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        call = asyncio.create_task(hol_send(IGNORE_SIGINT_LOOP, timeout=300, session=session))
        await _started(call, 1.5)
        stopped = await asyncio.wait_for(hol_stop(session=session), 30)
        assert "stopped" in stopped and "returns STOPPED" in stopped, stopped
        result = await asyncio.wait_for(call, 10)
        assert result.startswith("STOPPED: hol_stop"), result
        assert session not in _sessions
    finally:
        await hol_stop(session=session)


async def test_waiting_call_notices_a_lost_reply(tmp_path, monkeypatch):
    from hol4_mcp.hol_session import HOLSession
    monkeypatch.setattr(HOLSession, "LOST_REPLY_INTERVAL", 0.5)
    session = "cp_watchdog"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        hol = _sessions[session].session
        read = hol._read_response
        dropped = []

        async def drop_first_frame(timeout):
            if not dropped:
                dropped.append(await read(timeout))
            return await read(timeout)
        hol._read_response = drop_first_frame
        t0 = time.monotonic()
        result = await asyncio.wait_for(hol_send("1;", timeout=60, session=session), 20)
        assert time.monotonic() - t0 < 10, result
        assert "without sending its reply" in result, result
        hol._read_response = read
        assert "val it = 5" in await hol_send("5;", session=session)
    finally:
        await hol_stop(session=session)


async def test_server_sigint_cancels_the_running_call(tmp_path):
    from hol4_mcp.hol_mcp_server import _sigint_handler, _signal_interrupts
    import signal
    session = "cp_server_sigint"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        call = asyncio.create_task(hol_send(INTERRUPTIBLE_LOOP, timeout=300, session=session))
        await _started(call, 1.5)
        _sigint_handler(signal.SIGINT, None)
        result = await asyncio.wait_for(call, 20)
        assert result.startswith("INTERRUPTED"), result
        await asyncio.wait_for(asyncio.gather(*_signal_interrupts), 20)
        assert "val it = 6" in await hol_send("6;", session=session)
    finally:
        await hol_stop(session=session)
