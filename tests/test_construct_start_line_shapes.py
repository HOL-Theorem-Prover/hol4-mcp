"""``construct_start_line`` must never leave a truncation point mid-construct.

The partial-reload path sets ``_loaded_to_line = construct_start_line(...)``
(exclusive: lines 1..n-1 are loaded) and resends from that line. If the returned
line falls *inside* a multi-line construct, HOL is handed a fragment and the
resulting ``Unknown identifier`` error is sticky across every later navigation
(``MCP_BUGS.md`` §3 #4, ``HOL_STATE_AT_DEF_EDIT_STALENESS_NOTES.md`` Defect B).

Each case below is a real file shape; the assertion is the invariant that makes
the resend safe: the boundary must be at or before the first line of whatever
multi-line construct the edited line belongs to.
"""

import pytest

from hol4_mcp.hol_file_parser import construct_start_line


def _lines(content: str) -> list[str]:
    return content.split("\n")


# --- shapes -----------------------------------------------------------------

THEOREM_PROOF_QED = """\
Theorem a:
  T
Proof
  simp[]
QED
"""

DEFINITION_TERMINATION = """\
Theorem a:
  T
Proof
  simp[]
QED

Definition f_def:
  f n = if n = 0 then 0 else f (n - 1)
Termination
  WF_REL_TAC `measure I`
  \\ simp []
End
"""

RESUME_BLOCK = """\
Theorem a:
  T
Proof
  simp[]
QED

Resume a[lab]:
  simp []
  \\ metis_tac []
QED
"""

MULTILINE_VAL = """\
Theorem a:
  T
Proof
  simp[]
QED

val thms = [foo,
            bar,
            baz];

Theorem b:
  T
Proof
  simp[]
QED
"""

MULTILINE_COMMENT_THEN_THEOREM = """\
Theorem a:
  T
Proof
  simp[]
QED

(* a comment that
   spans lines *)
Theorem b:
  T
Proof
  simp[]
QED
"""


@pytest.mark.parametrize(
    "content,edited_line,enclosing_open_line,label",
    [
        (THEOREM_PROOF_QED, 4, 1, "inside Theorem/Proof/QED"),
        (DEFINITION_TERMINATION, 8, 7, "inside Definition body"),
        (DEFINITION_TERMINATION, 11, 7, "inside Definition Termination"),
        (RESUME_BLOCK, 9, 7, "inside Resume body"),
        (MULTILINE_VAL, 8, 7, "inside multi-line val declaration"),
        (MULTILINE_COMMENT_THEN_THEOREM, 8, 7, "inside multi-line comment"),
    ],
)
def test_boundary_is_not_mid_construct(
    content, edited_line, enclosing_open_line, label
):
    boundary = construct_start_line(content, edited_line)
    assert boundary <= enclosing_open_line, (
        f"{label}: editing line {edited_line} returned boundary {boundary}, "
        f"so the reload resends from line {boundary} — inside the construct "
        f"that opens at line {enclosing_open_line}. HOL gets a fragment:\n"
        f"  {_lines(content)[boundary - 1]!r}"
    )
