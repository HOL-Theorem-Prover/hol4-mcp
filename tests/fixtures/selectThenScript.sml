(*
  Fixture exercising the >>~- (LSelectThen / SELECT_LT_THEN) tactic, whose
  step decomposition historically caused a false "PROOF BROKEN at the opaque
  step" during state_at / check_proof navigation.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "selectThen";

Theorem select_then_thm:
  T /\ T
Proof
  conj_tac >>~- ([‘T’], SIMP_TAC bool_ss [])
QED

val _ = export_theory();
