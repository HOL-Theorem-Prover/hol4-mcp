(*
  Fixture whose proof fails by a RAISED EXCEPTION (a qpat_x_assum whose
  pattern matches no assumption -> HOL_ERR) rather than by leaving an
  unsolved goal. Used to check that the replay reporting softens the
  confident step pin in this case.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "raiseExc";

Theorem exc_thm:
  !x:bool. x = x
Proof
  gen_tac \\
  qpat_x_assum `F` mp_tac
QED

val _ = export_theory();
