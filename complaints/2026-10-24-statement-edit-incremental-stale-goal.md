# Editing only a theorem's statement lets `hol_state_at` replay incrementally against the old goal

**Status:** suspected; seen twice in one session, no minimal reproducer. The source
reading finds a plausible mechanism (below).
**Severity:** silent wrong state. The shown goal and `No goals` do not match the file.
**Component:** `hol4_mcp/hol_cursor.py` `_reparse_if_changed`, `_compute_target`,
`_reparse_steps_on_edit`, `_try_incremental_navigate`.
**First seen:** 2026-10-24.
**Related:** `2026-07-04-definition-edit-stale-session-unreproduced.md` (an older stale-after-edit report).

## Observed: occurrence 1

File `~/research/cakes/cake-pb/examples/pseudo_bool/spt_to_vecScript.sml`, theorem `ALOOKUP_sort`.

1. The statement `ALOOKUP (sort (λx y. FST x ≤ FST y) l) n = ALOOKUP l n` resolved `≤` to `int`
   ("more than one resolution of overloading"). `hol_state_at` line 186 showed the goal
   (`[Cache: … method=replay …]`).
2. Only the **statement** was edited, to `… (l:(num # 'a) list)) n = …`. The proof body was unchanged.
3. `hol_state_at` line 185 reported `method=incremental`, `replay=0ms`,
   `incr=(first_diff=9,old_idx=4)`, `file=changed`, and showed the goal unchanged.
4. A `hol_send` probe of `top_goal ()` showed the constants still typed at `int`
   (`$<= : int -> int -> bool`, `ALOOKUP : (int # 'a) list -> int -> 'a option`).

## Observed: occurrence 2 (same session)

In `MAP_shift_unshift`, the statement was edited from `lo ≤ k` (overload warning,
int) to `(lo:num) ≤ k`. `hol_state_at` past QED reported
`method=incremental, replay=0ms, incr=(first_diff=2,old_idx=2)` and "No goals", which
is the cached int-typed result. Navigating to the first proof line and back forced
`method=replay`.

## Expected

A change to the active theorem's statement invalidates every cached step of that
theorem (`first_diff = 0`), and the goal is elaborated again from the file.

## Source reading (2026-10-28; not executed)

- `_reparse_if_changed` clears `_active_theorem` (forcing re-entry) only when
  `first_changed <= self._loaded_to_line`. While a theorem is being navigated,
  `_loaded_to_line` covers the content **before** it, so an edit to its statement lines
  probably falls after that boundary, and the theorem stays active.
- `_compute_target` then calls `_reparse_steps_on_edit`, which compares **only the old and new
  step plans** (`_common_prefix_length(old_plan)`). The statement (`thm.goal`) is not compared.
  Since the body is unchanged, `first_diff` is greater than 0, and the incremental strategy
  navigates from the live goal stack, which was built from the old statement.

## Untested

- Whether any statement edit triggers this, or only one that changes types but not the printed form.
- Whether the same happens to a `Resume` header or a `Definition`'s Termination goal.

## Side observation (may be unrelated)

Just before occurrence 1, one `hol_state_at` ran for more than 120 s and was moved
to the background. `hol_sessions` then showed a session aged 3 min (a cold restart).

## Impact

The state shown is misleading: tactics are tuned to a goal that the file no
longer states, and "No goals" can be reported for a statement that has not been
proved.

## Workaround

Force a full replay by navigating outside the theorem and back.

## Acceptance

A test in which a theorem is navigated, then only its statement is edited (for
example, adding a type annotation that changes an overload resolution). The next
`hol_state_at` must not use `method=incremental`, and `top_goal()` must show the new
types.
