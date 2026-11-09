(* Regression fixture: Resume goal whose stored term contains a free variable
   whose name later clashes with a constant of *different type* in the parse
   context. Exercises the cursor's Resume goal-setup path.

   The suspended subgoal carries an assumption `v + w <= v + w` where v and w
   are free numeric variables. After the Theorem block, we introduce a
   boolean constant v_def: v = T, which puts a `:bool` constant `v` into the
   parse context. The suspension store still holds v as a :num Var (the
   resumption was captured before v_def was processed).

   A goal-setup path that round-trips through term_to_string + Parse.Term
   would print `(v :num) + (w :num) <= v + w`, then crash on re-parse with
   `Type constraint failure: Term: v :bool, Constraint: :num`.

   The correct path passes the term directly from the suspension store to
   proofManagerLib.set_goalfrag — see markerLib.set_suspended_goal. *)

open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "suspendRename";

Theorem bar:
  !w:num. w + 1 > 0
Proof
  gen_tac >>
  Q.SPEC_THEN `v + w` MP_TAC arithmeticTheory.LESS_EQ_REFL >>
  strip_tac >>
  suspend "case_v"
QED

Definition v_def:
  v = (T:bool)
End

Resume bar[case_v]:
  decide_tac
QED

Finalise bar

val _ = export_theory();
