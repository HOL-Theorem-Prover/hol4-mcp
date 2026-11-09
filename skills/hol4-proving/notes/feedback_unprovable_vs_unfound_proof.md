---
name: feedback_unprovable_vs_unfound_proof
description: Three failure modes for a stuck cheat — wrong tactic / wrong structure / unprovable-as-stated. Case 3 needs a definition or spec fix, not more proof engineering.
metadata:
  type: feedback
---

When a cheated theorem won't close:

1. **Wrong tactic** — goal provable, chain wrong. Fix the chain.
2. **Wrong structure** — goal provable but needs decomposition (suspend/Resume, lemma extraction). Fix structure.
3. **Unprovable as stated** — goal has a literal counterexample under the current definitions. No tactic helps; the **definition** or **theorem statement** needs to change.

**Why distinguish:** cases 1–2 reward more investigation; case 3 punishes it. Hours disappear into "the proof must be there somewhere" when actually a definitional gap needs to be patched.

**How to apply:** before assuming 1/2, try to construct a concrete counterexample. Pick literal values; trace through the assumptions and the goal. If the counterexample is consistent with all hypotheses, you have case 3.

**Case-3 resolution options (in preference order):**
1. Patch the **definition** so the gap closes (often: add a runtime check that errors on the offending shape). Then update dependent proofs.
2. Add a **side condition** to the theorem statement (and propagate through callers).
3. Restructure **upstream code** to avoid producing the offending shape.

**Pattern.** Suggestive of case 3: the cheat is *post-rewrite*; the residual goal is small and concrete; the surrounding chain was tuned for a tighter version of the spec and the new shape admits cases the tighter one couldn't.
