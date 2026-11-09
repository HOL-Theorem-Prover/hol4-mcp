"""Navigation INSIDE a parenthesised group when the group is applied to
exactly one goal: there the file's per-goal distribution and a flat replay
coincide, so hol_state_at can show the state at a position inside the group
instead of the step's entry. With more than one goal at the group's entry the
entry state and the INSIDE note stay. Inside-group positions are never cached."""
import re

import pytest

from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    hol_check_proof,
    hol_state_at,
    hol_stop,
)

SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "pnav";

Theorem grp_nav:
  (T /\\ T) /\\ (F \\/ T)
Proof
  conj_tac >- (conj_tac >- ACCEPT_TAC TRUTH
               >- ACCEPT_TAC TRUTH)
  >> simp []
QED

Theorem grp_two:
  (T /\\ T) /\\ (T /\\ T)
Proof
  conj_tac \\\\ (conj_tac >- ACCEPT_TAC TRUTH
                >- ACCEPT_TAC TRUTH)
QED

Theorem grp_fail:
  (T /\\ T) /\\ (F \\/ T)
Proof
  conj_tac >- (conj_tac >- FAIL_TAC "boom"
               >- ACCEPT_TAC TRUTH)
  >> simp []
QED

Theorem later_thm:
  T
Proof
  simp []
QED

val _ = export_theory();
"""


def loc(script, needle, occurrence=1):
    """(line, col) of the start of the n-th occurrence of `needle`."""
    pos = -1
    for _ in range(occurrence):
        pos = script.index(needle, pos + 1)
    line = script[:pos].count("\n") + 1
    col = pos - script.rfind("\n", 0, pos)
    return line, col


def goals(output):
    m = re.search(r"=== Goal[^\n]*===\n((?:  .*\n?)+)", output)
    assert m, output
    return [ln.strip() for ln in m.group(1).split("\n") if ln.strip()]


async def setup(tmp_path, session):
    f = tmp_path / "pnavScript.sml"
    f.write_text(SCRIPT)
    r = await _init_file_cursor(file=str(f), session=session)
    assert "Theorems:" in r, r
    return f


async def test_single_goal_entry_navigates_inside_the_group(tmp_path):
    session = "pnav_inside"
    try:
        await setup(tmp_path, session)
        # Between the first and the second `>- ACCEPT_TAC TRUTH` of grp_nav: the
        # first conjunct is closed, the second (`T`) remains.
        line, col = loc(SCRIPT, ">- ACCEPT_TAC TRUTH)", 1)
        r = await hol_state_at(line=line, col=col, session=session)
        assert not r.startswith("ERROR"), r
        assert "INSIDE step" not in r, r
        assert goals(r) == ["T"], r
        assert re.search(r"\[inside opaque step \d+ .*sub-step", r), r
    finally:
        await hol_stop(session)


async def test_multi_goal_entry_keeps_entry_state_and_note(tmp_path):
    session = "pnav_multi"
    try:
        await setup(tmp_path, session)
        line, col = loc(SCRIPT, ">- ACCEPT_TAC TRUTH)", 2)
        r = await hol_state_at(line=line, col=col, session=session, all_goals=True)
        assert "INSIDE step" in r, r
        assert "=== Goals (2) ===" in r, r
    finally:
        await hol_stop(session)


async def test_inside_navigation_does_not_pollute_the_cache(tmp_path):
    session = "pnav_cache"
    try:
        await setup(tmp_path, session)
        line, col = loc(SCRIPT, ">- ACCEPT_TAC TRUTH)", 1)
        r = await hol_state_at(line=line, col=col, session=session)
        assert goals(r) == ["T"], r
        # A later theorem, then back to grp_nav's boundary after the group.
        lt_line, _ = loc(SCRIPT, "simp []", 3)
        r2 = await hol_state_at(line=lt_line, col=3, session=session)
        assert goals(r2) == ["T"], r2
        b_line, _ = loc(SCRIPT, ">> simp []", 1)
        r3 = await hol_state_at(line=b_line, col=6, session=session)
        assert goals(r3) in (["F ∨ T"], ["F \\/ T"]), r3
        assert "[inside opaque step" not in r3, r3
        chk = await hol_check_proof(theorem="grp_nav", session=session)
        assert "Status: OK" in chk, chk
    finally:
        await hol_stop(session)


async def test_failing_tactic_inside_group_names_sub_step_and_line(tmp_path):
    session = "pnav_fail"
    try:
        await setup(tmp_path, session)
        line, col = loc(SCRIPT, ">- ACCEPT_TAC TRUTH)", 3)
        r = await hol_state_at(line=line, col=col, session=session)
        fail_line, _ = loc(SCRIPT, 'FAIL_TAC "boom"', 1)
        assert "PROOF BROKEN inside opaque step" in r, r
        assert "sub-step" in r and f"line {fail_line}" in r, r
    finally:
        await hol_stop(session)
