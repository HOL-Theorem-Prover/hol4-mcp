# Bug: editing a `Definition` above the checkpoint leaves the session stale; forward replay then wedges with "Unknown identifier"

Status: **PARTIALLY RESOLVED (2026-08-28).** TWO defects — neither of the two
originally reported — were reproduced and fixed; together they account for the
`Unknown identifier` *symptom*: mid-gap truncation (2026-08-27) and an
off-by-one at the truncation boundary (2026-08-28). The originally reported
Defects A and B did **not** reproduce; they are open in
`complaints/2026-07-04-definition-edit-stale-session-unreproduced.md`.

## Resolved: mid-gap truncation (the `Unknown identifier` symptom)

`construct_start_line` protected the inside of a *block* (`Theorem`,
`Definition`, `Resume`, …) but, on meeting a closing `QED`/`End` while scanning
backwards, returned the edited line unchanged — "we are between blocks". The gap
between two blocks can itself hold multi-line content, and resending from the
middle of it hands HOL a fragment just the same:

* a multi-line **comment** — the fragment's words then parse as *terms*, so the
  error is `Unknown identifier: <a word of the comment>`, naming something that
  looks like an `Ancestors` constant and pointing nowhere near the edit;
* a multi-line **`val`/`fun` declaration**.

Fix: return the first line of the gap (`i + 2`) instead of the edited line —
`hol4_mcp/hol_file_parser.py`, `construct_start_line`.

Reproducers (red before, green after):

* `tests/test_construct_start_line_shapes.py` — unit, no HOL session; six file
  shapes, of which the multi-line-comment and multi-line-`val` cases failed.
* `tests/test_definition_edit_staleness.py::test_edit_inside_multiline_comment_does_not_wedge_replay`
  — integration; editing the last line of a three-line comment above a
  `Definition` gave `Error executing file content: Unknown identifier: spanning`,
  i.e. a word of the comment.

Field evidence that this is the defect actually hit in use: a session on
`compiler/backend/proofs/data_to_wordProofScript.sml` (2026-08-27) reported
`Unknown identifier: the` and `Unknown identifier: run` repeatedly. Both are
words inside multi-line comments in the gap above the constructs being edited
(`(* the oracle answers a data run consumes … *)`), and `misc$the` is a real
constant, which is what made the message so convincing. Shortening a comment to
one line appeared to "fix" it — a one-line comment cannot be truncated into.
Cost: ~6 diagnostic cycles chasing type variables and parentheses, plus one
correct edit reverted on the strength of the phantom.

## Resolved: off-by-one at the truncation boundary (the SAME symptom, second path)

The mid-gap fix above was necessary but not sufficient. The symptom recurred on
`data_to_wordProofScript.sml` (2026-08-28) with that fix live — `Unknown
identifier: goes` / `the` / `leaves`, each the first word of a two-line comment's
CONTINUATION line — because a second, independent defect reaches the same place.

`_loaded_to_line` is **exclusive**: lines `1 .. _loaded_to_line - 1` are loaded
and the next chunk is sent starting AT `_loaded_to_line` (see the three
`content_lines[:self._loaded_to_line - 1]` sites in `hol_cursor.py`). The edit
path nevertheless stored `boundary - 1`, so the resend began one line BEFORE the
construct boundary — handing HOL the last line of whatever sits immediately
above the edited block. When that is a multi-line comment, its tail parses as
terms.

Trigger shape (NOT the comment-edit case already covered): the edit lands
*inside the block below* the comment.

```
QED
                                       <- blank
(* … --                                <- comment, line A
   find_code_thm leaves … *)           <- comment, line B   <-- resent ALONE
Theorem lemma:                         <- boundary
  … edited line …
```

Fix: store the boundary itself — `hol_cursor.py`, `_loaded_to_line = boundary if
boundary > 1 else 0` (0 still means "cold" to the load path).

Reproducer (red before, green after):
`tests/test_definition_edit_staleness.py::test_edit_below_multiline_comment_does_not_wedge_replay`
— failed with `Unknown identifier: find_code_thm`, the exact field symptom.

Both fixes are needed: `construct_start_line` decides *where* the boundary is,
this one makes the resend actually start there.

## NOT reproduced — moved to the complaint inbox

The original Defects A and B (silent staleness / wedged forward replay) did not
reproduce. Their field evidence, the tests tried, and the remaining candidate
triggers now live in
`complaints/2026-07-04-definition-edit-stale-session-unreproduced.md`.
