open HolKernel Parse boolLib bossLib;

val _ = new_theory "repro_conc_nav";

Theorem conc_alpha:
  !a b c:num. a + b + c = c + b + a
Proof
  strip_tac >> strip_tac >> strip_tac
  >> `a + b = b + a` by decide_tac
  >> decide_tac
QED

Theorem conc_beta:
  !p q:bool. p /\ q ==> q /\ p
Proof
  strip_tac >> strip_tac >> strip_tac
  >> `~ ~q` by asm_rewrite_tac[]
  >> asm_rewrite_tac[]
QED

val _ = export_theory();
