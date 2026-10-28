"""A Definition's termination goal survives the string round trip: types are
kept when the file's grammar would resolve an overload differently, and SML
antiquotes in the body resolve to the session's values."""
from hol4_mcp.hol_cursor import definition_quotation
from hol4_mcp.hol_mcp_server import _init_file_cursor, _sessions, hol_state_at, hol_stop


def test_definition_quotation_splits_antiquotes():
    assert definition_quotation("f x = x") == '[QUOTE "f x = x"]'
    assert definition_quotation("f x = ^mem x") == \
        '[QUOTE "f x = ", ANTIQUOTE (mem), QUOTE " x"]'
    assert definition_quotation("f x = ^(select_ax tm)") == \
        '[QUOTE "f x = ", ANTIQUOTE (select_ax tm)]'
    assert definition_quotation("f (x :^ty) = x") == \
        '[QUOTE "f (x :", ANTIQUOTE (ty_antiq (ty)), QUOTE ") = x"]'
    assert definition_quotation('f x = "a\\b"') == '[QUOTE "f x = \\"a\\\\b\\""]'


INT_SCRIPT = """\
open HolKernel Parse boolLib bossLib;
open integerTheory intLib;

val _ = new_theory "tcint";

Definition count_up_def:
  count_up (a:num, b:num) = if b < a then count_up (a, b + 1) else b
Termination
  WF_REL_TAC `measure (\\(a,b). a - b)` >> simp []
End

val _ = export_theory();
"""

ANTIQUOTE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "tcanti";

val one = ``1:num``;

Definition count_down_def:
  count_down (a:num, b:num) = if b < a then count_down (a, b + ^one) else b
Termination
  WF_REL_TAC `measure (\\(a,b). a - b)` >> simp []
End

val _ = export_theory();
"""


async def init(tmp_path, name, script, session):
    f = tmp_path / f"{name}Script.sml"
    f.write_text(script)
    r = await _init_file_cursor(file=str(f), session=session)
    assert "Theorems:" in r, r
    return f


async def test_termination_goal_keeps_num_types_under_integer_grammar(tmp_path):
    session = "tc_int_types"
    try:
        await init(tmp_path, "tcint", INT_SCRIPT, session)
        r = await hol_state_at(line=10, col=1, session=session)   # End line
        goal = _sessions[session].cursor._tc_goals.get("count_up_def")
        assert goal and "WF" in goal and ":num" in goal, (goal, r)
        assert "PROOF BROKEN" not in r and "No goals" in r, r
    finally:
        await hol_stop(session)


async def test_termination_goal_resolves_sml_antiquotes(tmp_path):
    session = "tc_antiquote"
    try:
        await init(tmp_path, "tcanti", ANTIQUOTE_SCRIPT, session)
        r = await hol_state_at(line=11, col=1, session=session)   # End line
        goal = _sessions[session].cursor._tc_goals.get("count_down_def")
        assert goal and "WF" in goal, (goal, r)
        assert "PROOF BROKEN" not in r and "No goals" in r, r
    finally:
        await hol_stop(session)


ELIDED_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "tcdeep";

val _ = Globals.max_print_depth := 3;

Definition walk_def:
  walk (a:num, b:num, c:num, d:num) =
    if a < b + c + d then walk (a + 1, b, c, d) else a
Termination
  WF_REL_TAC `measure (\\(a,b,c,d). b + c + d - a)` >> simp []
End

val _ = export_theory();
"""


async def test_termination_goal_is_set_from_its_term_not_its_print(tmp_path):
    """With a low max_print_depth the printed goal is elided (`...`), which
    does not parse back; the goal must come from the term itself."""
    script = tmp_path / "tcdeepScript.sml"
    script.write_text(ELIDED_SCRIPT)
    session = "tc_elided"
    try:
        await _init_file_cursor(file=str(script), session=session)
        state = await hol_state_at(line=11, col=3, session=session)
        assert "Failed to set up goal" not in state and "parse" not in state.lower(), state
        assert "=== Goal (1 of 1)" in state, state
        done = await hol_state_at(line=12, col=1, session=session)
        assert "No goals" in done, done
    finally:
        await hol_stop(session=session)
