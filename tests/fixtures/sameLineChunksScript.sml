(*
  Minimal repro for the state_at chunk-parser bug.

  Two related symptoms both rooted in goalfrag_step_plan_json:

  (A1) The chunk parser tracks SML-level `let ... in ... end` and
       `case ... of` structure, but does NOT recognise that
       ``‘...’`` (HOL term quotation) is a context in which
       these keywords belong to the TERM language (no `end`,
       different `of` semantics). So `let` inside ``‘...’``
       opens an unbalanced SML let in the parser's mental model and
       it swallows the rest of the proof body as a single chunk.

       Workaround: wrap the let in extra parens — the parser
       correctly tracks `(...)` balance.

  (A2) The chunk parser returns BYTE positions for step `end`
       offsets (SML strings are byte arrays), while the Python
       cursor compares them against character positions in
       `proof_body` and adds them to `proof_body_offset` (also a
       character count). Bodies containing non-ASCII characters
       like ``‘``/``’`` (3 UTF-8 bytes, 1 char) get a
       systematic over-count that mis-maps the QED cursor to a
       mid-body tactic.

  Real cake-datacut trigger that exposed both: ``size_of_app_Number``
  in ``compiler/backend/proofs/data_to_word_assignProofScript.sml``.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "sameLineChunks";

(* Theorem 1: triggers A1 — `let` inside a term quotation. *)
Theorem let_in_term_quotation:
  T
Proof
  ‘let x = T in x’ by simp []
  >> simp []
QED

(* Theorem 2: triggers A2 — non-ASCII unicode chars in proof body. *)
Theorem unicode_in_proof:
  !x:num. x = x
Proof
  strip_tac
  >> Cases_on ‘x’ >> simp []
QED

val _ = export_theory();
