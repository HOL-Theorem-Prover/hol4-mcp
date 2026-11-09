"""Regression tests for the concurrency / lifecycle findings.

Each test asserts the CORRECT behaviour; they were written red under
``xfail(strict=True)`` and the markers came off when the fixes landed.

Covered findings (``MCP_BUGS_review.md``):

  #10 A ``_state_at_bounded`` overall-budget abort SIGINTs HOL and returns
      without ever reading the in-flight command's reply.  Recovery is left to
      the next ``send``'s ``_drain_pipe``, which gives up after 10 ms of
      silence, so a reply that lands later is read as the reply to the NEXT
      command -- and every reply after it is off by one for as long as commands
      keep taking longer than the 10 ms drain window.

  #11 Nothing serializes cursor-level navigation.  ``HOLSession.send`` holds a
      lock for the duration of one command, but two ``hol_state_at`` calls on
      the same session interleave between commands, so one navigation's
      ``drop_all()``/``gf`` runs in the middle of the other's replay and the
      goals that come back belong to whichever proof won the race.

Finding #10: how long HOL really takes to answer a SIGINT
=========================================================

The abort is only harmful when HOL's reply to the aborted command arrives
more than ~20 ms after the SIGINT (10 ms sleep inside ``HOLSession.interrupt``
plus the 10 ms ``_drain_pipe`` poll).  Measured against an unmodified HOL,
SIGINT-to-frame-completion is usually well under a millisecond -- 0.07-0.12 ms
for ``metis_tac``, ``simp`` and goalstack loops -- but allocation-heavy work
answers far later: ``EVAL`` on a large list reached 3.25 ms and
``List.tabulate(8000000, numSyntax.term_of_int)`` produced 0.22, 0.36, 12.84,
49.23, 58.40 and 352.04 ms over six runs.  Driving ``_state_at_bounded``
end-to-end against a real HOL with a 3-million-term ``List.tabulate`` mis-read
the next reply in 3 of 6 attempts.

Whether a given abort mis-reads is therefore a coin flip on real workloads.
The tests below pin the unwind time with an SML-level ``handle Interrupt``
delay so the outcome is deterministic; the phenomenon they exercise (the reply
landing hundreds of milliseconds after the SIGINT) is the measured one.

Finding #11: the interleaving
=============================

``repro_conc_navScript.sml`` holds two independent theorems.  With the cursor
parked inside ``conc_beta``, one navigation into ``conc_alpha`` and one into
``conc_beta`` issue alternating commands (traced: ``ABABABAB...``).  Both are
backward navigations, so both begin with ``drop_all(); gf ...``, and the
second one's ``drop_all()`` lands between the first one's ``gf`` and its
``goals_json()``.
"""

import asyncio
import shutil
from pathlib import Path

import pytest
import anyio

from hol4_mcp import hol_mcp_server as srv
from hol4_mcp.hol_cursor import StateAtResult
from hol4_mcp.hol_mcp_server import hol_start, hol_state_at, hol_stop
from hol4_mcp.hol_session import HOLSession


FIXTURES_DIR = Path(__file__).parent / "fixtures"
CONC_SCRIPT = FIXTURES_DIR / "repro_conc_navScript.sml"


# ---------------------------------------------------------------------------
# Finding #10 -- timeout-abort leaves the NUL-framed pipe frame-shifted
# ---------------------------------------------------------------------------

STALE_MARKER = "REPRO_CONC_STALE_FRAME"

# Time HOL spends unwinding the interrupt before it writes the aborted
# command's frame. Far above the ~20 ms recovery window, inside the range
# measured on an unmodified HOL (see module docstring).
UNWIND_MS = 400

# A spin loop that answers SIGINT only after `UNWIND_MS`, then completes
# normally -- so its frame (marker text + NUL) is written in one go, long
# after `_state_at_bounded` has given up on it.
SLOW_TO_UNWIND = (
    "val _ = (let fun spin (n:int) = if n <= 0 then 0 else spin (n-1) "
    "in spin 100000000000 end; ()) "
    f"handle Interrupt => (OS.Process.sleep (Time.fromMilliseconds {UNWIND_MS}); "
    f'print "{STALE_MARKER}\\n");'
)


def marked_command(tag: str, ms: int = 120) -> str:
    """A command that prints ``MARK_<tag>`` after ``ms`` of quiet.

    The quiet period exceeds the 10 ms ``_drain_pipe`` poll, which is what a
    real tactic replay looks like from the pipe's point of view: nothing to
    drain when the next command is written.
    """
    return (
        f"val _ = (OS.Process.sleep (Time.fromMilliseconds {ms}); "
        f'print "MARK_{tag}\\n");'
    )


class SendingCursor:
    """Cursor stub whose ``state_at`` issues one real ``session.send``.

    Mirrors what ``FileProofCursor.state_at`` does to the pipe (send a command
    and await its reply) without needing a script to replay; the code under
    test is ``_state_at_bounded`` plus ``HOLSession``'s recovery path.
    """

    def __init__(self, session: HOLSession, command: str):
        self.session = session
        self.command = command
        self.interrupted = 0

    async def state_at(self, line, col=1, skip_prefix=False):
        await self.session.send(self.command, timeout=300)
        return StateAtResult(
            goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=1,
            file_hash="h",
        )

    def mark_interrupted(self):
        self.interrupted += 1


@pytest.fixture
async def bare_session():
    """A plain HOL session -- no cursor, no tactic_prefix, no script."""
    session = HOLSession("/tmp")
    await session.start()
    yield session
    await session.stop()


async def abort_a_slow_navigation(session: HOLSession) -> None:
    """Drive ``_state_at_bounded`` to its overall-budget abort.

    Leaves HOL still unwinding the SIGINT, exactly as an expired
    ``hol_state_at`` budget does.
    """
    cursor = SendingCursor(session, SLOW_TO_UNWIND)
    result = await srv._state_at_bounded(cursor, 10, 1, timeout=0.5)
    assert result.error and result.error.startswith("TIMEOUT"), (
        f"test setup: expected the overall budget to expire, got {result.error!r}"
    )
    assert cursor.interrupted == 1, "test setup: cursor was not resynced"


@pytest.mark.asyncio
async def test_send_after_timeout_abort_returns_its_own_reply(bare_session):
    """The first command after an aborted navigation must get its own reply.

    ``_state_at_bounded`` cancels ``state_at`` mid-``send``, SIGINTs HOL and
    returns; the reply to the interrupted command is left in the pipe.  The
    next ``send`` drains for 10 ms, finds nothing (HOL is still unwinding),
    writes its command and reads the first NUL-terminated frame that arrives
    -- which is the aborted command's.
    """
    await abort_a_slow_navigation(bare_session)

    output = await bare_session.send("1 + 1;", timeout=15)

    assert "val it = 2" in output, (
        "the send issued after a timeout-aborted navigation was answered with "
        f"the ABORTED command's output instead of its own: got {output!r}"
        + (
            f" -- which is the {STALE_MARKER} frame the interrupted command "
            "wrote while unwinding"
            if STALE_MARKER in output else ""
        )
    )


@pytest.mark.asyncio
async def test_frame_shift_after_timeout_abort_does_not_persist(bare_session):
    """Replies must stay attributed to their own commands after an abort.

    ``_drain_pipe`` only recovers when the previous reply is already sitting in
    the pipe by the time the next command is written.  Commands that take
    longer than its 10 ms poll -- i.e. any real tactic replay -- keep the
    pipeline exactly one frame behind indefinitely, so a caller can be shown
    another navigation's goals long after the timeout that caused it.
    """
    await abort_a_slow_navigation(bare_session)

    tags = ["one", "two", "three"]
    outputs = [await bare_session.send(marked_command(t), timeout=15) for t in tags]

    misattributed = [
        (tag, out.strip()) for tag, out in zip(tags, outputs)
        if f"MARK_{tag}" not in out
    ]
    assert not misattributed, (
        f"{len(misattributed)} of {len(tags)} replies after the timeout abort "
        "belonged to the PRECEDING command -- the pipe stays one frame behind "
        f"for as long as commands take longer than the 10 ms drain poll: "
        f"{misattributed!r}"
    )


# ---------------------------------------------------------------------------
# Finding #11 -- no cursor-level concurrency guard
# ---------------------------------------------------------------------------

# repro_conc_navScript.sml:
#   conc_alpha  proof lines  8-10   (line 10 = state after the `by` step)
#   conc_beta   proof lines 16-18   (line 17 = state after the strip_tacs)
ALPHA_LINE = 10
BETA_LINE = 17
PARK_LINE = 18  # inside conc_beta, past both targets, so both are backward

ALPHA_GOAL_TEXT = "a + b + c = c + b + a"


def stable(rendered: str) -> str:
    """``hol_state_at`` output without its per-call timing/cache telemetry."""
    return "\n".join(
        line for line in rendered.splitlines()
        if not line.startswith(("[Timing:", "[Cache:"))
    ).strip()


@pytest.fixture
async def conc_session(tmp_path):
    """A registered session parked inside ``conc_beta`` with a live cursor."""
    name = "repro_conc_navigation"
    script = tmp_path / CONC_SCRIPT.name
    shutil.copyfile(CONC_SCRIPT, script)
    started = await hol_start(workdir=str(tmp_path), name=name, force=True)
    assert not started.startswith("ERROR"), f"test setup: {started}"
    try:
        init = await hol_state_at(
            line=PARK_LINE, col=1, file=str(script),
            workdir=str(tmp_path), session=name,
        )
        assert "Theorem: conc_beta" in init, f"test setup: cursor init failed: {init}"
        assert srv._sessions[name].cursor._base_checkpoint_saved
        yield name
    finally:
        await hol_stop(session=name)


@pytest.mark.asyncio
async def test_concurrent_state_at_calls_report_their_own_positions(conc_session):
    """Two ``hol_state_at`` calls batched together must each answer their own line.

    Agents routinely issue independent tool calls in one batch; FastMCP runs
    them as concurrent tasks against the same cursor.  Here one asks for a
    position in ``conc_alpha`` and the other for a position in ``conc_beta``.
    Each is first measured on its own, so the expected answers are the
    session's own serialized behaviour, not a hand-written expectation.
    """
    baseline_alpha = await hol_state_at(line=ALPHA_LINE, col=1, session=conc_session)
    baseline_beta = await hol_state_at(line=BETA_LINE, col=1, session=conc_session)
    assert "Theorem: conc_alpha" in baseline_alpha and "ERROR" not in baseline_alpha, (
        f"test setup: serialized navigation into conc_alpha failed: {baseline_alpha}"
    )
    assert "Theorem: conc_beta" in baseline_beta and "ERROR" not in baseline_beta, (
        f"test setup: serialized navigation into conc_beta failed: {baseline_beta}"
    )

    # Back to the parked position so both navigations have real work to do.
    await hol_state_at(line=PARK_LINE, col=1, session=conc_session)

    concurrent_alpha, concurrent_beta = await asyncio.gather(
        hol_state_at(line=ALPHA_LINE, col=1, session=conc_session),
        hol_state_at(line=BETA_LINE, col=1, session=conc_session),
    )

    # The silent corruption: a position inside conc_beta answered, without any
    # error, with a goal belonging to conc_alpha.
    assert "Theorem: conc_beta" in concurrent_beta and (
        ALPHA_GOAL_TEXT not in concurrent_beta
    ), (
        f"hol_state_at(line={BETA_LINE}) -- a position inside conc_beta -- was "
        "answered with conc_alpha's goal because a concurrent navigation "
        "reset the proof manager mid-replay, and reported no error:\n"
        f"{concurrent_beta}"
    )
    assert stable(concurrent_beta) == stable(baseline_beta), (
        f"concurrent hol_state_at(line={BETA_LINE}) differs from the same call "
        f"made serially:\n--- concurrent ---\n{stable(concurrent_beta)}\n"
        f"--- serial ---\n{stable(baseline_beta)}"
    )
    assert "ERROR" not in concurrent_alpha, (
        f"concurrent hol_state_at(line={ALPHA_LINE}) failed its replay because "
        f"a concurrent navigation dropped its goal:\n{concurrent_alpha}"
    )
    assert stable(concurrent_alpha) == stable(baseline_alpha), (
        f"concurrent hol_state_at(line={ALPHA_LINE}) differs from the same call "
        f"made serially:\n--- concurrent ---\n{stable(concurrent_alpha)}\n"
        f"--- serial ---\n{stable(baseline_alpha)}"
    )


@pytest.mark.parametrize("operation", ["check", "send", "goals", "switch", "cancel_waiter", "gc", "start", "setenv"])
async def test_other_operations_wait_for_navigation(conc_session, monkeypatch, tmp_path, operation):
    """A peer cannot inspect, reset or replace a session partway through
    navigation. hol_restart, which preempts, is in test_control_plane.py."""
    expected = await hol_state_at(line=ALPHA_LINE, session=conc_session)
    await hol_state_at(line=PARK_LINE, session=conc_session)
    cursor = srv._sessions[conc_session].cursor
    paused = asyncio.Event()
    release = asyncio.Event()
    peer_entered = asyncio.Event()
    original_state_at = cursor.state_at
    original_send = cursor.session.send
    original_init = srv._init_file_cursor

    async def paused_navigation(*args, **kwargs):
        paused.set()
        await release.wait()
        return await original_state_at(*args, **kwargs)

    async def observed_send(*args, **kwargs):
        if paused.is_set() and not release.is_set():
            peer_entered.set()
        return await original_send(*args, **kwargs)

    async def observed_init(*args, **kwargs):
        if paused.is_set() and not release.is_set():
            peer_entered.set()
        return await original_init(*args, **kwargs)

    monkeypatch.setattr(cursor, "state_at", paused_navigation)
    monkeypatch.setattr(cursor.session, "send", observed_send)
    monkeypatch.setattr(srv, "_init_file_cursor", observed_init)
    monkeypatch.setattr(srv, "_schedule_gc", lambda _: None)
    primary = asyncio.create_task(hol_state_at(line=ALPHA_LINE, session=conc_session))
    peer = None
    try:
        await asyncio.wait_for(paused.wait(), 5)
        if operation == "check":
            call = srv.hol_check_proof(theorem="conc_beta", session=conc_session)
        elif operation in ("send", "cancel_waiter"):
            call = srv.hol_send(command="drop_all();", session=conc_session)
        elif operation == "goals":
            call = srv.hol_goals(session=conc_session)
        elif operation == "gc":
            call = srv._do_gc(conc_session)
        elif operation == "start":
            call = hol_start(str(tmp_path), name=conc_session)
        elif operation == "restart":
            call = srv.hol_restart(session=conc_session)
        elif operation == "setenv":
            call = srv.hol_setenv({}, session=conc_session)
        else:
            other = tmp_path / "otherScript.sml"
            shutil.copyfile(CONC_SCRIPT, other)
            call = hol_state_at(file=str(other), line=BETA_LINE, session=conc_session)
        peer = asyncio.create_task(call)
        # If the peer is serialized, it cannot issue a HOL command or replace
        # the cursor while the navigation has yielded between commands.
        try:
            await asyncio.wait_for(peer_entered.wait(), .1)
        except TimeoutError:
            pass
        assert not peer_entered.is_set(), f"{operation} entered the active navigation"
        if operation == "cancel_waiter":
            peer.cancel()
            with pytest.raises(asyncio.CancelledError):
                await peer
    finally:
        release.set()
        results = await asyncio.gather(primary, *([peer] if peer else []), return_exceptions=True)
    assert stable(results[0]) == stable(expected)
    if operation == "cancel_waiter":
        assert isinstance(results[1], asyncio.CancelledError)
        return
    assert not isinstance(results[1], BaseException), results[1]
    if operation == "check":
        assert "Status: OK" in results[1], results[1]
    elif operation == "goals":
        assert ALPHA_GOAL_TEXT in results[1], results[1]
    elif operation == "switch":
        assert "Theorem: conc_beta" in results[1], results[1]


async def test_concurrent_start_enforces_single_session(tmp_path):
    names = ("race_start_a", "race_start_b")
    try:
        results = await asyncio.gather(*(hol_start(str(tmp_path), name=name) for name in names))
        assert sum("started" in result for result in results) == 1, results
        assert sum("refusing to start" in result for result in results) == 1, results
        assert sum(name in srv._sessions for name in names) == 1
    finally:
        for name in names:
            await hol_stop(session=name)


@pytest.mark.parametrize("cancellation", ["task", "scope"])
async def test_cancelled_tool_recovers_before_next_command(conc_session, monkeypatch, cancellation):
    session = srv._sessions[conc_session].session
    started = asyncio.Event()
    original_write = session._write_command

    async def observe_write(command):
        await original_write(command)
        if command == SLOW_TO_UNWIND:
            started.set()

    monkeypatch.setattr(session, "_write_command", observe_write)
    scopes = []

    async def call():
        if cancellation == "scope":
            with anyio.CancelScope() as scope:
                scopes.append(scope)
                await srv.hol_send(SLOW_TO_UNWIND, session=conc_session, timeout=300)
        else:
            await srv.hol_send(SLOW_TO_UNWIND, session=conc_session, timeout=300)

    task = asyncio.create_task(call())
    try:
        await asyncio.wait_for(started.wait(), 5)
        if cancellation == "scope":
            scopes[0].cancel()
            await task
        else:
            task.cancel()
            with pytest.raises(asyncio.CancelledError):
                await task
        result = await srv.hol_send("1 + 1;", session=conc_session, timeout=1)
        assert "val it = 2" in result, result
        result = await hol_state_at(line=ALPHA_LINE, session=conc_session)
        assert "Theorem: conc_alpha" in result and "ERROR" not in result, result
    finally:
        if not task.done():
            task.cancel()
        await asyncio.gather(task, return_exceptions=True)
