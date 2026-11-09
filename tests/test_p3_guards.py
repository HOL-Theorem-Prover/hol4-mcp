"""P3 guard rails.

P3a: RULE J server-side — hol_start refuses a second concurrent session
     (force=True overrides); hol_file_init refuses a workdir switch.
P3b: hol_send rejects `val <primitive> = ...` shadow bindings.
"""

import pytest

from hol4_mcp.hol_mcp_server import (
    hol_start as _hol_start,
    hol_send as _hol_send,
    hol_stop as _hol_stop,
    _check_shadow_binding,
)

hol_start = _hol_start
hol_send = _hol_send
hol_stop = _hol_stop


@pytest.mark.asyncio
async def test_rule_j_second_session_refused(tmp_path):
    a = "p3a_rule_j_a"
    b = "p3a_rule_j_b"
    r = await hol_start(workdir=str(tmp_path), name=a)
    assert "started" in r.lower()
    try:
        # Second session under a different name: refused with RULE J context
        r = await hol_start(workdir=str(tmp_path), name=b)
        assert r.startswith("ERROR"), f"expected refusal: {r}"
        assert "RULE J" in r
        assert a in r  # names the running session
        assert "force=True" in r

        # Same-name start stays idempotent (no refusal)
        r = await hol_start(workdir=str(tmp_path), name=a)
        assert "already running" in r

        # force=True overrides
        r = await hol_start(workdir=str(tmp_path), name=b, force=True)
        assert "started" in r.lower(), f"force should start: {r}"
    finally:
        await hol_stop(session=a)
        await hol_stop(session=b)


@pytest.mark.asyncio
async def test_shadow_binding_blocked(tmp_path):
    # Blocked before any session interaction
    for nm in ("gs", "fs", "rw", "simp", "e", "it", "concl", "drop"):
        r = await hol_send(command=f"val {nm} = 1;", session="nonexistent")
        assert "BLOCKED" in r and "shadows" in r, f"{nm} not blocked: {r}"

    # Prefixed and non-colliding names pass the guard
    assert _check_shadow_binding("val my_gs = 1;") is None
    assert _check_shadow_binding("val gs2 = 1;") is None
    assert _check_shadow_binding("DB.find \"CONJ\";") is None

    # End-to-end: an allowed binding executes normally
    session = "p3b_shadow_test"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        r = await hol_send(command="val my_x = 41 + 1;", session=session)
        assert "42" in r
    finally:
        await hol_stop(session=session)


@pytest.mark.parametrize("cmd", ['load "basis";', 'use "helpers.sml";', ' load "fooTheory"; foo_def;'])
async def test_hol_send_rejects_load_use(tmp_path, cmd):
    session = "p3_load_use"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        r = await hol_send(command=cmd, session=session)
        assert r.startswith("ERROR: hol_send BLOCKED"), r
        assert "Ancestors" in r and "open" in r and "hol_state_at(file=" in r, r
    finally:
        await hol_stop(session)
