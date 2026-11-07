"""Inside a Resume block whose header HOL does not read as written — a bare
second entry `t[a,b]` (an attribute, not a label path), a stacked `t[a][b]`
(a parse error), or a label another block already resumes — navigation names
the header problem and the lines involved instead of a position error."""
from hol4_mcp.hol_file_parser import resume_header_problems
from hol4_mcp.hol_mcp_server import (
    _init_file_cursor, hol_check_proof, hol_state_at, hol_stop)

SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "rh";

Theorem t:
  T /\\ T
Proof
  conj_tac
  >- suspend "num"
  \\\\ simp[]
QED

Resume t[num]:
  suspend "unsigned"
QED

{header}
  simp[]
QED

Finalise t;

val _ = export_theory();
"""

def test_key_value_entries_and_single_labels_are_not_problems():
    text = SCRIPT.replace("{header}", "Resume t[unsigned]:") + (
        "\nResume willsplit2[q,smlname=q2sg]:\n  cheat\nQED\n"
        "\nResume testTacMod[rtp_qpp, exclude_simps=AND_CLAUSES]:\n  cheat\nQED\n")
    assert resume_header_problems(text) == []


async def test_checking_a_doubly_resumed_label_names_both_blocks(tmp_path):
    script = tmp_path / "rhScript.sml"
    script.write_text(SCRIPT.replace("{header}", "Resume t[num,unsigned]:"))
    text = script.read_text()
    session = "resume_header_check"
    try:
        await _init_file_cursor(file=str(script), session=session)
        result = await hol_check_proof(theorem="t[num]", session=session)
        child = _lines(text, "Resume t[num,unsigned]:")[0]
        parent = _lines(text, "Resume t[num]:")[0]
        assert result.startswith("ERROR") and f"line {child}" in result, result
        assert f"line {parent}" in result, result
    finally:
        await hol_stop(session=session)


def _lines(text: str, needle: str) -> list[int]:
    return [i for i, ln in enumerate(text.split("\n"), 1) if needle in ln]


async def _navigate_into_child(tmp_path, header):
    script = tmp_path / "rhScript.sml"
    script.write_text(SCRIPT.replace("{header}", header))
    text = script.read_text()
    session = "resume_header"
    try:
        await _init_file_cursor(file=str(script), session=session)
        child = _lines(text, header)[-1]
        state = await hol_state_at(line=child + 1, col=3, session=session)
        return state, child, _lines(text, "Resume t[num]:")[0]
    finally:
        await hol_stop(session=session)


async def test_a_bare_second_entry_is_named_as_an_attribute(tmp_path):
    state, child, parent = await _navigate_into_child(tmp_path, "Resume t[num,unsigned]:")
    assert f"line {child}" in state and f"line {parent}" in state, state
    assert "Resume t[unsigned]:" in state and "attribute" in state, state


async def test_a_stacked_header_is_named(tmp_path):
    state, child, _ = await _navigate_into_child(tmp_path, "Resume t[num][unsigned]:")
    assert f"line {child}" in state and "Resume t[unsigned]:" in state, state


async def test_a_duplicate_label_is_named(tmp_path):
    state, child, parent = await _navigate_into_child(tmp_path, "Resume t[num]:")
    assert f"line {child}" in state and f"line {parent}" in state, state
    assert "already" in state, state
