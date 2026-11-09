open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "repro_parser_surplus_end";

Theorem end_surplus:
  p /\ (p ==> q) ==> p /\ q
Proof
  strip_tac >> conj_tac
  >- suspend "p_case"
  >- suspend "q_case"
QED

(* The surplus ')' on the next block's last line is INTENTIONAL: this
   fixture reproduces MCP_BUGS_review.md finding #2 (a Resume body whose
   file form does not parse). Do not "fix" the parenthesis. *)
Resume end_surplus[p_case]:
  (ASM_REWRITE_TAC[]))
QED

Resume end_surplus[q_case]:
  RES_TAC
QED

Finalise end_surplus

val _ = export_theory();
