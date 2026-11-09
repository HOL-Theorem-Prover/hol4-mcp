"""A theorem `hol_check_proof` just proved is bound in the session as the file
would bind it, so the next navigation past it does not prove it again; the
check reports its own prefix/setup cost."""
import pytest

from hol4_mcp import hol_mcp_server
from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    hol_check_proof,
    hol_send,
    hol_state_at,
    hol_stop,
)

# `counted` bumps a plain ref, which no rewind restores: `!runs` is the number
# of times t1's proof has run in the session.
CHECK_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "chk";

val runs = ref 0;
fun counted g = (runs := !runs + 1; ALL_TAC g);

Definition c_def:
  c = 3
End

Theorem t1[simp]:
  c + 1 = 4
Proof
  counted >> simp[c_def]
QED

Triviality tv:
  c = 3
Proof
  simp[c_def]
QED

Theorem t2:
  c + 1 = 4 /\\ T
Proof
  simp[]
QED

val _ = export_theory();
"""

DISPATCH_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "chd";

Theorem t1:
  T /\\ T
Proof
  conj_tac
  >- suspend "X"
  \\\\ simp[]
QED

Resume t1[X]:
  simp[]
QED

Finalise t1;

val _ = export_theory();
"""


def _line(text: str, needle: str) -> int:
    return next(i for i, ln in enumerate(text.split("\n"), 1) if needle in ln)


def _script(tmp_path, text=CHECK_SCRIPT, name="chkScript.sml"):
    script = tmp_path / name
    script.write_text(text)
    return script


async def test_a_checked_theorem_is_not_proved_again_by_the_next_navigation(tmp_path):
    script = _script(tmp_path)
    text = script.read_text()
    session = "chk_bind"
    try:
        await _init_file_cursor(file=str(script), session=session)
        result = await hol_check_proof(theorem="t1", session=session)
        assert "Status: OK" in result, result
        state = await hol_state_at(line=_line(text, "  simp[]"), col=3, session=session)
        assert "=== Goal" in state, state
        assert "val it = 1" in await hol_send("!runs;", session=session)
    finally:
        await hol_stop(session=session)


async def test_a_bound_checked_theorem_keeps_its_attributes(tmp_path):
    script = _script(tmp_path)
    text = script.read_text()
    session = "chk_attrs"
    try:
        await _init_file_cursor(file=str(script), session=session)
        assert "Status: OK" in await hol_check_proof(theorem="t1", session=session)
        assert "Status: OK" in await hol_check_proof(theorem="tv", session=session)
        # t2's `simp[]` closes only through t1's [simp] tag.
        state = await hol_state_at(line=_line(text, "  simp[]") + 1, col=1, session=session)
        assert "No goals" in state, state
        exported = await hol_send(
            'map #1 (DB.thms "-");', session=session)
        assert '"t1"' in exported and '"tv"' not in exported, exported
    finally:
        await hol_stop(session=session)


async def test_inside_a_checked_theorem_its_own_name_is_not_bound(tmp_path):
    script = _script(tmp_path)
    text = script.read_text()
    session = "chk_inside"
    try:
        await _init_file_cursor(file=str(script), session=session)
        assert "Status: OK" in await hol_check_proof(theorem="t1", session=session)
        state = await hol_state_at(
            line=_line(text, "counted >> simp"), col=14, session=session)
        assert "=== Goal" in state and "c + 1 = 4" in state, state
        assert "thm" not in await hol_send("t1;", session=session)
        assert "c + 1 = 4" not in await hol_send(
            'map (concl o #2) (DB.thms "-");', session=session)
    finally:
        await hol_stop(session=session)


async def test_a_checked_dispatcher_keeps_its_suspensions(tmp_path):
    script = _script(tmp_path, DISPATCH_SCRIPT, "chdScript.sml")
    text = script.read_text()
    session = "chk_dispatch"
    try:
        await _init_file_cursor(file=str(script), session=session)
        assert "Status: OK" in await hol_check_proof(theorem="t1", session=session)
        state = await hol_state_at(
            line=_line(text, "Resume t1[X]") + 2, col=1, session=session)
        assert "No goals" in state, state
    finally:
        await hol_stop(session=session)


async def test_a_check_reports_its_own_setup_cost(tmp_path, monkeypatch):
    monkeypatch.setattr(hol_mcp_server, "_SLOW_NAV_SECS", 0.05)
    script = _script(tmp_path)
    text = script.read_text()
    session = "chk_setup"
    try:
        await _init_file_cursor(file=str(script), session=session)
        result = await hol_check_proof(theorem="t1", session=session, fresh=True)
        assert "Slow prefix/setup" in result and "fresh verification" in result, result
        state = await hol_state_at(line=_line(text, "  simp[]"), col=3, session=session)
        assert "fresh verification" not in state, state
    finally:
        await hol_stop(session=session)
