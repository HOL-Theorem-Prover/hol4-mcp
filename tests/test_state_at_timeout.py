"""Unit tests for the overall wall-clock budget on state_at navigation
(_state_at_bounded).

The per-tactic timeout bounds each tactic, but a large prefix replay or a long
\\-chain can sum to many minutes; _state_at_bounded caps the TOTAL so a
navigation can never hang unbounded. On expiry it SIGINTs HOL (recoverable) and
returns a TIMEOUT result instead of blocking.

These drive _state_at_bounded with a fake cursor/session, so they need no live
HOL session or FastMCP tool layer.
"""

import asyncio

import pytest

from hol4_mcp.hol_cursor import StateAtResult
from hol4_mcp import hol_mcp_server as srv


class _FakeSession:
    def __init__(self):
        self.interrupts = 0

    def interrupt(self):
        self.interrupts += 1


class _FakeCursor:
    """Cursor stub whose state_at sleeps `delay` seconds then returns `result`."""

    def __init__(self, delay, result=None):
        self._delay = delay
        self._result = result or StateAtResult(
            goals=[{"asms": [], "goal": "T"}], tactic_idx=3,
            tactics_replayed=3, tactics_total=3, file_hash="h",
        )
        self.session = _FakeSession()
        self.interrupted = 0
        self.state_at_calls = 0

    async def state_at(self, line, col=1, skip_prefix=False):
        self.state_at_calls += 1
        await asyncio.sleep(self._delay)
        return self._result

    def mark_interrupted(self):
        self.interrupted += 1


async def test_fast_navigation_passes_through_unchanged():
    cur = _FakeCursor(delay=0.0)
    res = await srv._state_at_bounded(cur, 10, 1, timeout=5.0)
    assert res is cur._result
    assert cur.session.interrupts == 0
    assert cur.interrupted == 0


async def test_slow_navigation_times_out_and_recovers():
    cur = _FakeCursor(delay=10.0)  # would hang well past the budget
    res = await srv._state_at_bounded(cur, 10, 1, timeout=0.05)
    # Returns a structured TIMEOUT result, never raises / hangs.
    assert isinstance(res, StateAtResult)
    assert res.error is not None and res.error.startswith("TIMEOUT")
    # tactics_total == 0 routes it through the structural-error path in the tools.
    assert res.tactics_total == 0
    assert res.goals == []
    # The HOL process was interrupted and the cursor resynced.
    assert cur.session.interrupts == 1
    assert cur.interrupted == 1


async def test_zero_budget_disables_the_bound():
    cur = _FakeCursor(delay=0.0)
    res = await srv._state_at_bounded(cur, 10, 1, timeout=0)
    assert res is cur._result
    assert cur.session.interrupts == 0


async def test_default_budget_used_when_timeout_is_none(monkeypatch):
    # A tiny default budget should fire for a slow navigation when timeout=None.
    monkeypatch.setattr(srv, "STATE_AT_TIMEOUT", 0.05)
    cur = _FakeCursor(delay=10.0)
    res = await srv._state_at_bounded(cur, 10, 1, timeout=None)
    assert res.error is not None and res.error.startswith("TIMEOUT")
    assert cur.session.interrupts == 1


async def test_interrupt_failure_does_not_mask_timeout():
    # Even if interrupt() raises, a TIMEOUT result is still returned cleanly.
    cur = _FakeCursor(delay=10.0)

    def boom():
        raise RuntimeError("sigint failed")

    cur.session.interrupt = boom
    res = await srv._state_at_bounded(cur, 10, 1, timeout=0.05)
    assert res.error is not None and res.error.startswith("TIMEOUT")
    assert cur.interrupted == 1  # cursor still resynced
