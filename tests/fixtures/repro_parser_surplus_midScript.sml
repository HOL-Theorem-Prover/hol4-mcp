open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "repro_parser_surplus_mid";

Theorem mid_surplus:
  p /\ (p ==> q) ==> (p /\ p) /\ q
Proof
  strip_tac >> conj_tac
  >- suspend "pp_case"
  >- suspend "qq_case"
QED

Resume mid_surplus[qq_case]:
  RES_TAC
QED

(* The surplus ')' closing the first arm below is INTENTIONAL: this
   fixture reproduces MCP_BUGS_review.md finding #2 (the second arm is
   silently dropped from the step plan). Do not "fix" the parenthesis.
   This block is last in the file so nothing needs to load past it. *)
Resume mid_surplus[pp_case]:
  conj_tac
  >- (ASM_REWRITE_TAC[]))
  >- (ASM_REWRITE_TAC[])
QED

Finalise mid_surplus

val _ = export_theory();
