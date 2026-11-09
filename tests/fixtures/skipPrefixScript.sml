open HolKernel boolLib bossLib Parse arithmeticTheory;

val _ = new_theory "skipPrefix";

(* A prefix theorem whose PROOF fails fast if replayed (first_x_assum with no
   assumptions raises HOL_ERR immediately) but whose STATEMENT is true. In
   skip_prefix navigation mode it is bound by `cheat` without replaying, so the
   target below can still use it; with skip_prefix off it is replayed, fails,
   and is auto-cheated into _failed_proofs instead. *)
Theorem broken_prefix:
  !n:num. n + 0 = n
Proof
  first_x_assum mp_tac
QED

(* A second prefix theorem with a clean, fast proof — should NOT be skipped's
   only member; it is also cheated in skip mode (statement only). *)
Theorem good_prefix:
  !n:num. 0 + n = n
Proof
  simp[]
QED

(* Target: replays for real and depends on broken_prefix's statement. *)
Theorem uses_prefix:
  5 + 0 = 5
Proof
  simp[broken_prefix]
QED

val _ = export_theory();
