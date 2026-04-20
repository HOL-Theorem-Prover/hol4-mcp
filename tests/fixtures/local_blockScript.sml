open HolKernel Parse boolLib bossLib;
val _ = new_theory "local_block";

Theorem before_block:
  T
Proof
  REWRITE_TAC []
QED

local
  open listTheory
in

Theorem inside_block_a:
  LENGTH [1;2;3] = 3
Proof
  simp[]
QED

Theorem inside_block_b:
  !l. LENGTH (APPEND l []) = LENGTH l
Proof
  Induct \\ simp[]
QED

end

Theorem after_block:
  T
Proof
  REWRITE_TAC []
QED

val _ = export_theory();
