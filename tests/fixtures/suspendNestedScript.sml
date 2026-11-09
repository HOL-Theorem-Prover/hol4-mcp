(* Regression fixture: nested Resume blocks where the OUTER Resume body
   issues a SUB-suspend that a LATER Resume block needs to resume.

   Demonstrates the canonical lifecycle that file replay MUST preserve:
     1. Theorem nested:  suspends "A"
     2. Resume nested[A]: suspends "B" + closes one arm
     3. Resume nested[B]: closes the other arm

   Step 3 can only succeed if step 2's processing registered "B" as a
   sub-suspension. The hol4-mcp bug: verify_resume_json (set_goalfrag +
   proof manager) does NOT register sub-suspensions; only the canonical
   markerLib.resume path does. *)
open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "suspendNested";

Theorem nested:
  p /\ p ==> p /\ p
Proof
  suspend "A"
QED

Resume nested[A]:
  strip_tac >> conj_tac
  >- suspend "B"
  >- first_assum ACCEPT_TAC
QED

Resume nested[B]:
  first_assum ACCEPT_TAC
QED

Finalise nested

val _ = export_theory();
