"""A `Quote f:` block runs an arbitrary SML function on its body; when that
function keeps state in a plain SML ref (CakeML's `add_cakeml` keeps the
translator's program state this way), an in-memory rewind to before the
block retires the constants it defined while the ref keeps its later value,
so sending the block again fails. Navigation must never rewind across one."""
from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    hol_check_proof,
    hol_send,
    hol_state_at,
    hol_stop,
)

# `stash` defines the constant its body names as equal to the last constant
# it defined (held in `st`), the shape of CakeML's program-state threading.
QUOTE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "qst";

val st = ref T;
fun stash q = let
  val toks = String.tokens (not o Char.isAlphaNum)
               (String.concat (map (fn QUOTE s => s | ANTIQUOTE _ => "") q))
  val n = List.last toks
  val th = new_definition (n ^ "_def", mk_eq (mk_var (n, bool), !st))
in st := lhs (concl th) end;

Theorem t0:
  T
Proof
  simp[]
QED

Quote stash:
  sone
End

Theorem t1:
  sone /\\ T
Proof
  conj_tac
  >- suspend "X"
  \\\\ simp[]
QED

Resume t1[X]:
  simp[definition "sone_def"]
QED

Finalise t1;

val _ = export_theory();
"""


SECOND_QUOTE = """\
Quote stash:
  stwo
End

Theorem t2:
  stwo
Proof
  simp[definition "stwo_def", definition "sone_def"]
QED

val _ = export_theory();
"""


def _line(text: str, needle: str) -> int:
    return next(i for i, ln in enumerate(text.split("\n"), 1) if needle in ln)


def _script(tmp_path, text=QUOTE_SCRIPT):
    script = tmp_path / "qstScript.sml"
    script.write_text(text)
    return script


def _assert_clean(output: str) -> None:
    assert "Out-of-date" not in output, output
    assert "out-of-date" not in output, output
    assert "prefix error" not in output, output


async def _navigate_past_t1(text: str, session: str) -> None:
    """To the QED of `Resume t1[X]`, so the whole of t1 has run."""
    state = await hol_state_at(
        line=_line(text, 'simp[definition "sone_def"]') + 1, col=1, session=session)
    assert "No goals" in state, state


async def _assert_no_stale_goal(session: str) -> None:
    goal = await hol_send("top_goal ();", session=session)
    assert "<-old" not in goal, goal


async def test_navigating_from_a_resume_back_into_its_parent_keeps_the_quote(tmp_path):
    script = _script(tmp_path)
    text = script.read_text()
    session = "quote_resume_parent"
    try:
        await _init_file_cursor(file=str(script), session=session)
        into_resume = await hol_state_at(
            line=_line(text, 'simp[definition "sone_def"]'), col=3, session=session)
        assert "=== Goal" in into_resume, into_resume
        into_parent = await hol_state_at(
            line=_line(text, "conj_tac"), col=3, session=session)
        assert "=== Goal" in into_parent, into_parent
        _assert_clean(into_parent)
        await _assert_no_stale_goal(session)
    finally:
        await hol_stop(session=session)


async def test_an_edit_inside_the_theorem_after_a_quote_keeps_the_quote(tmp_path):
    script = _script(tmp_path)
    session = "quote_edit_body"
    try:
        await _init_file_cursor(file=str(script), session=session)
        text = script.read_text()
        await _navigate_past_t1(text, session)
        script.write_text(text.replace("  \\\\ simp[]\n", "  \\\\ rw[]\n"))
        text = script.read_text()
        state = await hol_state_at(line=_line(text, "rw[]"), col=3, session=session)
        assert "=== Goal" in state, state
        _assert_clean(state)
        await _assert_no_stale_goal(session)
    finally:
        await hol_stop(session=session)


async def test_checking_a_theorem_after_moving_past_it_keeps_the_quote(tmp_path):
    script = _script(tmp_path)
    text = script.read_text()
    session = "quote_check_after"
    try:
        await _init_file_cursor(file=str(script), session=session)
        await _navigate_past_t1(text, session)
        script.write_text(text.replace("  \\\\ simp[]\n", "  \\\\ rw[]\n"))
        result = await hol_check_proof(theorem="t1", session=session)
        _assert_clean(result)
        assert "FAILED" not in result, result
    finally:
        await hol_stop(session=session)


async def test_an_edited_quote_defines_the_new_constant(tmp_path):
    script = _script(tmp_path)
    session = "quote_edit_quote"
    try:
        await _init_file_cursor(file=str(script), session=session)
        text = script.read_text()
        await _navigate_past_t1(text, session)
        script.write_text(text.replace("sone", "sthree"))
        text = script.read_text()
        state = await hol_state_at(line=_line(text, "conj_tac"), col=3, session=session)
        assert "sthree ∧ T" in state, state
        _assert_clean(state)
        assert "thm" in await hol_send('definition "sthree_def";', session=session)
        await _assert_no_stale_goal(session)
    finally:
        await hol_stop(session=session)


async def test_a_stateful_span_no_pattern_names_is_reloaded_once(tmp_path):
    script = _script(tmp_path, QUOTE_SCRIPT.replace(
        "Quote stash:\n  sone\nEnd", 'val _ = stash [QUOTE "sone"];'))
    session = "quote_backstop"
    try:
        await _init_file_cursor(file=str(script), session=session)
        text = script.read_text()
        await _navigate_past_t1(text, session)
        script.write_text(text.replace("Theorem t0:\n  T\n", "Theorem t0:\n  T /\\ T\n"))
        text = script.read_text()
        state = await hol_state_at(line=_line(text, "conj_tac"), col=3, session=session)
        assert "=== Goal" in state and "sone ∧ T" in state, state
        assert "treated as opaque" in state, state
        _assert_clean(state)
        await _assert_no_stale_goal(session)
        # Learned: the next rewind across it loads a file without a failure.
        script.write_text(text.replace("T /\\ T\nProof", "T /\\ T /\\ T\nProof", 1))
        text = script.read_text()
        state = await hol_state_at(line=_line(text, "conj_tac"), col=3, session=session)
        assert "=== Goal" in state and "treated as opaque" not in state, state
        _assert_clean(state)
    finally:
        await hol_stop(session=session)


async def test_a_rewind_past_a_second_quote_and_forward_again_is_clean(tmp_path):
    script = _script(tmp_path, QUOTE_SCRIPT.replace(
        "val _ = export_theory();\n", SECOND_QUOTE))
    session = "quote_second"
    try:
        await _init_file_cursor(file=str(script), session=session)
        text = script.read_text()
        state = await hol_state_at(
            line=_line(text, 'definition "stwo_def"') + 1, col=1, session=session)
        _assert_clean(state)
        script.write_text(text.replace("  \\\\ simp[]\n", "  \\\\ rw[]\n"))
        text = script.read_text()
        state = await hol_state_at(line=_line(text, "rw[]"), col=3, session=session)
        assert "=== Goal" in state, state
        _assert_clean(state)
        state = await hol_state_at(
            line=_line(text, 'definition "stwo_def"') + 1, col=1, session=session)
        assert "=== Goal" in state, state
        _assert_clean(state)
        await _assert_no_stale_goal(session)
    finally:
        await hol_stop(session=session)
