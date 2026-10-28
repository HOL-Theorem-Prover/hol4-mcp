# Restoring a cursor checkpoint fails with `loadState … SysErr ENOENT`, forcing a full-file prefix replay

**Status:** suspected; seen 4 times on one large file, no minimal reproducer yet.
The session recovers by itself, and no wrong result has been seen. The cost is
10–25 min per occurrence.
**Component:** `hol4_mcp/hol_cursor.py` checkpoint save/restore: `_new_checkpoint_path`,
`_save_context_checkpoint`, `_load_context_checkpoint`, `_load_checkpoint_and_backup`,
`_invalidate_checkpoint`, `_invalidate_from_line`.
Tools affected: `hol_check_proof`, `hol_state_at`.
**First seen:** 2026-10-23 · **Last seen:** 2026-10-25.
(Merged from the former `2026-10-25-checkpoint-enoent-full-replay.md`.)

## Environment

- Project: `~/research/cakes/cake-pb/examples/pseudo_bool/array/npbc_arrayProgScript.sml`
  (about 9000 lines; a cold prefix replay takes 10–25 min). Heavy suspend/Resume ladders.
- Checkpoint directory: `…/pseudo_bool/array/.hol/cursor_checkpoints/` (1.7 GB on 10-23, with
  many surviving `*_<nonce>_*_context.save` files). Free disk space was fine.

## Occurrences

Each one was an edit to the file, then a navigation or check that restored a
checkpoint. Every time, HOL raised
`PolyML.SaveState.loadState "<path>"` → `Exception- SysErr ("No such file or directory", SOME ENOENT)`,
and the session then replayed the file from the top.

1. **10-23.** Edited the Resume ladder of `core_from_range_arr_spec`: added a sub-suspend
   `>- suspend "Upd"` plus `Resume core_from_range_arr_spec[Upd]:` inside the `[Stored]` body.
   `[Upd]` checked OK. Then `hol_check_proof(theorem="core_from_range_arr_spec[Stored]")`.
   Load path: `…/core_from_range_arr_spec_Empty__d135fbca_000128_context.save` (failure evidence 7).
   `hol_sessions` then showed a replay of `check_rup_loop_arr_spec` (lines 1646–1742), and a
   check that should take about 2 s took more than 12 min.
2. **10-25.** Added a new `Theorem do_dom_check_NONE[local]` above `dom_check_arr_spec` and
   checked it (OK). Then edited `dom_check_arr_spec`, inlining two Resume bodies, and ran
   `hol_check_proof dom_check_arr_spec`.
   Load path: `…/do_dom_check_NONE_1163189f_000336_context.save` (evidence 57).
3. **10-25.** Edited several Resume bodies of `check_cstep_arr_spec` (the Obj/Cobj/Aobj/Cpres
   tails, and re-wrapped two lines in Obj/Sol). Then
   `hol_check_proof check_cstep_arr_spec[Cobj]`.
   Load path: `…/check_cstep_arr_spec_Store__1163189f_000488_context.save` (evidence 63).
   The full replay took about 25 min.
4. **10-25.** Checked `all_marked_arr_spec` (OK). Then edited the next theorem,
   `check_output_arr_spec` (a new body with suspends, and a `none` Resume inserted above `der`),
   and ran `hol_state_at` on the `none` Resume.
   Load path: `…/all_marked_arr_spec_1163189f_000676_context.save` (evidence 82).

In occurrences 2 and 4, the theorem whose checkpoint failed to load came
**before** the edit and had just been checked successfully, so it should not
have been invalidated.

## Expected

The checkpoint loads, or the server sees that it cannot be loaded and falls back
to the nearest checkpoint that still loads, not to a cold replay of the whole
prefix.

## Evidence

`failure-N.json` evidence lives in a private per-process directory
(`hol4_mcp/failure_evidence.py`, which keeps the newest 20) that is **removed at
server exit unless `HOL4_MCP_KEEP_EVIDENCE` is set**. Evidence 7/57/63/82 are
gone. Set that variable before the next attempt to reproduce.

## Source reading (2026-10-28; not executed)

- `_load_context_checkpoint` checks `ckpt.context_path.exists()` before it calls `loadState`,
  so the named file most likely **did exist**. A Poly/ML child save names its parent
  saves by path, and `loadState` loads the whole chain, so the missing file is probably an
  **ancestor** in the SaveState hierarchy, not the file named in the command. This is unconfirmed;
  the SysErr text does not name the path.
- `_new_checkpoint_path`'s docstring states the invariant: "Old saves remain until cursor GC
  because newer child states may name them as parents. Reusing or unlinking one while the heap
  is live can cause SaveState parent collisions or later ENOENT loads." Yet
  `_invalidate_checkpoint` unlinks `end_of_proof_path` and `context_path` immediately. It is
  called from `_invalidate_from_line` (for theorems whose `proof_end_line >= start_line`, and for
  any checkpoint key no longer among the parsed theorem names, which a Resume-label edit may
  rename), from `_invalidate_all_checkpoints`, from `_reparse_steps_on_edit` (on the active
  theorem), and when `_load_checkpoint_and_backup`'s `loadState` fails. If a deleted file is the
  parent of a later save, that save can no longer load. This is a lead to check, not a
  confirmed cause.
- On a failed `loadState`, `_load_context_checkpoint` also **unlinks** the checkpoint it tried to
  load. If that file is in turn a parent of other saves, one ENOENT could cascade into more.

## Untested

- Whether the missing file is the named checkpoint or an ancestor. Log the hierarchy, for
  example `PolyML.SaveState.showParent` or `showHierarchy`, before loading.
- Whether some size limit evicts checkpoints. None was found in `hol_cursor.py`.
- Whether adding a label to a Resume ladder is meant to invalidate the checkpoints of
  sibling labels.

## Impact

Each occurrence costs 10–25 min of replay on this file. No wrong result was observed.

## Acceptance

A test that saves a chain of child checkpoints, invalidates (edits) a theorem
whose checkpoint is an ancestor of a surviving one, and then restores the
surviving one. It should load, or fall back to a valid predecessor without a cold
replay. Either way, no `loadState` call should hit ENOENT.
