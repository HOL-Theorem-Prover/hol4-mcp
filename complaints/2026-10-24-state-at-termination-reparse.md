# `hol_state_at` inside a Definition's `Termination` block fails: the termination goal is re-parsed from its printed (elided) form

**Status:** suspected; seen once. The source reading confirms that the goal makes a
print → parse round trip, which is the same bug class as the resolved Resume-goal
defect.
**Component:** `hol4_mcp/hol_cursor.py` `_extract_tc_goal` and the Definition branch of
`_setup_proof_goal` (`gf `{tc_goal}``); SML `extract_tc_goal_json_q` in
`hol4_mcp/sml_helpers/tactic_prefix.sml`.
**First seen:** 2026-10-24.
**Related:** `git show 62481d6:HOL_STATE_AT_RESUME_BUG_NOTES.md`. The same round trip in the
Resume path was fixed by setting the goal from terms (`set_resume_goalfrag_json`).

## Observed

- Call: `hol_state_at(file=~/research/cakes/cake-pb/examples/pseudo_bool/array/npbc_slotScript.sml, line=1761)`.
  Line 1761 is inside `Definition sat_slot_aux_def … Termination WF_REL_TAC … End`.
- Output: `ERROR: Failed to set up goal: HOL_ERR (at Parse.parse_type: on line 18, characters 25-27:
  Type parsing failure with remaining input: ...),len,r) (wv,cs,vs,i,len,r)) ∧ …`.
  The remaining input is the pretty-printed termination goal, with elided pieces:
  `R (wv,cs,vs,i + (1 :...),len,... − ... )`.
- At the time, the theory's ancestors were built with `Holmake --fast`.

## Expected

The termination goal, the same one `Defn.tgoal` gives in a REPL, or a clear
message that Termination blocks cannot be navigated.

## Source reading (2026-10-28)

- `extract_tc_goal_json_q` runs `Defn.tgoal` and then returns
  `Lib.with_flag (Globals.show_types, true) term_to_string t`, a **string**.
- `_setup_proof_goal` for `thm.kind == "Definition"` sends `gf `{tc_goal}`;`, which re-parses that
  string in the current parse context.
- Any term that does not survive `term_to_string` and `Parse.Term` will break here. In this
  case the printed form contains `...`, which suggests print-depth elision
  (`Globals.max_print_depth` or a similar setting in the session) produced unparseable text. This
  is not verified.

## Untested

- Whether every Termination block in that file, or any large termination goal, reproduces it.
- Which printer setting produced the `...`.

## Impact

None this time, because the agent navigated elsewhere; the target line was chosen by
mistake. But a Termination proof cannot be developed with `hol_state_at` when its goal
prints with elision.

## Acceptance

A fixture `Definition … Termination … End` whose termination goal is printed with
elision (for example, set `max_print_depth` low in the fixture) or does not
otherwise round-trip. `hol_state_at` inside the Termination block then shows the
`Defn.tgoal` goal (compare with `term_to_string` under the same settings) and does
not fail with a parse error.
