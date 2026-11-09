(*
  A theorem inside an SML local block whose proof contains a HOL
  quotation with `let ... in` and no `end`, preceded by [local]
  attributes. The block must be sent to HOL as one unit.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "localQuoteLet";

Overload one_tm[local] = “1n”

Theorem helper[local]:
  !n. n + 0 = n
Proof
  simp[]
QED

local

val th = helper

in

Theorem inside_local:
  (let k = i in k + 0) = (i:num)
Proof
  `(let k = i in k + 0) = (i:num)` by simp[LET_THM, th]
  \\ asm_rewrite_tac []
QED

Theorem inside_local_plain:
  !n. n + 0 = n
Proof
  simp[]
QED

end;

Theorem after_local:
  !n. 0 + n = n
Proof
  simp[]
QED

val _ = export_theory();
