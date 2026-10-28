# Editing a `Definition` above the active theorem leaves the session stale (Defect A) or wedges forward replay (Defect B)

**Status:** suspected; seen once (2026-07-04) and **not reproduced** by the
minimal tests. This report predates the checkpoint rewrite (prefix-hash
checkpoints, construct-boundary truncation, predecessor rewind), and its leading
hypothesis (a stale cross-session `*.dumpedheap`) no longer applies: the code
writes no `.dumpedheap` files now. Proposed disposition: **dismiss unless it is seen
again**. Keep it open until the maintainer decides.
**Component:** `hol4_mcp/hol_cursor.py` change invalidation (`_reparse_if_changed`,
`_invalidate_from_line`) and prefix reload (`_load_context_to_line`).
**Related:** `2026-10-24-statement-edit-incremental-stale-goal.md`, a current stale-goal report
with a different trigger.
(Migrated 2026-10-28 from `HOL_STATE_AT_DEF_EDIT_STALENESS_NOTES.md`. The two defects that
*were* found and fixed for the same `Unknown identifier` symptom stay documented there.)

## Defects as reported

- **A (silent staleness).** After editing a `Definition` that sits before the cursor,
  `hol_state_at` past it reported `file=changed` and returned a goal in about 140 ms
  without re-executing the Definition. The heap kept the old constant, and the next call
  reported `file=unchanged`, so the stale state could no longer be detected.
- **B (wedged forward replay).** After navigating backwards past the edited Definition and
  then forwards again, the call failed every time with
  `Error executing file content: Unknown identifier: mk_name`, where `mk_name` is a term
  constant from an `Ancestors` theory that `hol_send` could reach at that moment.

## Field sequence (cake-cp, branch `cp_enc_new`, 2026-07-04)

Workdir `~/research/cakes/cake-cp/examples/pseudo_bool/cp_encoding`, file
`cp_to_ilp_primScript.sml`, Ancestors `pbc pbc_encode cp ilp cp_to_ilp int_bitwise int_bitwiseExtra`.
Nine new `Definition`s sat at about lines 529–653. The edited one was
`cencode_mult_body_def` (about lines 584–645), followed by `Theorem encode_prim_constr_sem_1`
(Proof at 682). `encode_max_sem_2` ended at about line 523.

1. Cold `hol_state_at(line=683)` succeeded:
   `[Timing: total=20942ms, replay=42ms, method=replay]`,
   `[Cache: pos_before=(idx=0,uninit,hash=miss), target=(idx=0,partial), file=unchanged, replayed=0/3]`.
2. Lines 623–625 inside `cencode_mult_body_def` were edited: a pure string-literal change
   renaming 4 label tags.
3. `hol_state_at(line=683)` succeeded:
   `[Timing: total=139ms, replay=47ms, method=replay]`,
   `[Cache: pos_before=(idx=0,init,hash=match), target=(idx=0,partial), file=changed, replayed=0/3]`.
   `EVAL` still produced the OLD tags, and `hol_send cencode_mult_body_def` still showed the OLD rhs.
4. `hol_state_at(line=521)` succeeded, with `file=unchanged`, `replayed=1/3`.
5. `hol_state_at(line=683)` failed with `ERROR: Error executing file content: Unknown identifier: mk_name`,
   identically on retry. Meanwhile `hol_send "mk_name_def; cencode_mult_body_def;"` returned both.

## What has been tried

`tests/test_definition_edit_staleness.py`:
- `test_edited_definition_is_reexecuted_for_later_theorem` (Defect A) passes: the consumer
  stops closing after `d = 1` becomes `d = 2`.
- `test_backward_then_forward_navigation_after_definition_edit` (Defect B) passes: no wedge.

Both passed even before the fixes, so the minimal shape lacks the trigger.

## Remaining candidate triggers (untested)

- Checkpointing actually engaging: the minimal fixture may be too small to create checkpoints.
- `holmake` rebuilding the theory **under** a live session.
- A Definition block with many sibling Definitions in the gap between two theorems, as in the field file.

## Impact (when it occurred)

- A: goals and `EVAL` probes were computed against a constant that no longer matched the file.
- B: the region could not be reached until the session restarted.

## Acceptance

Either reproduce on current code with one of the remaining triggers and add a
regression test, or dismiss with the user's agreement.
