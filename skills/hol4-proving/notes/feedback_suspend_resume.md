---
name: feedback_suspend_resume
description: HOW to dispatch across goals, HOW to inline cleanly, and how to recover a lost suspension / "No such label". Rules themselves live in the hol4-proving skill.
metadata:
  type: feedback
---

# RULES

## ⛔ ALWAYS `>- suspend "L"`, NEVER THEN-form `suspend`
**Absolute syntactic rule.** THEN distributes its right operand across ALL remaining goals; `suspend "L"` is a single-goal tactic. THEN-form `suspend` ANYWHERE — top level, inside `(...)`, end of a chain — is banned.

Banned surface forms (all THEN, semantically identical, all rejected — including INSIDE parens, e.g. `>- (tac1 >> suspend "L")` / `>- (tac1 \\ suspend "L")`):
- `>> suspend "L"`
- `\\ suspend "L"` (CakeML preamble synonym for `>>`)
- `THEN suspend "L"` (literal word, with word boundary; `THEN1`/`THENL`/`THEN_LT` are fine)

Symptom when one slips through: at Resume time either `resconj`-merged bundle (multiple goals tagged), OR — even with EXACTLY 1 residual goal — the file-replay engine silently refuses to commit the suspension, so the dispatcher's QED is never reached and every downstream sub-suspend reports "No such label". Interactive `proofManagerLib.e (suspend "L")` on the same goal succeeds, which makes the file-only failure mode confusing. The fix is always: replace with `>-` (THEN1).

Correct forms — `>-` (THEN1) sits immediately before every `suspend`:
- `>- suspend "L"`                              (canonical, single residual goal)
- `>- suspend "L1" >- suspend "L2" >- suspend "L3"`   (N sequential dispatches: each `>-` closes the next first-of-remaining)
- `tac1 >> tac2 >> tac3 >- suspend "L"`         (chain-then-suspend on single goal: `>>`/`\\` for the non-suspend steps, `>-` only at the boundary to suspend)
- `>- (tac1 >> tac2 >- suspend "L")`            (closes outer first goal by running the parenthesised chain that ends in suspend)
- `>~ [pat] >- suspend "L"`                     (pattern-guided)

⚠️ **Common trap**: `tac1 >- tac2 >- suspend "L"` is **NOT** chain-on-first-goal. It's left-associative `(tac1 >- tac2) >- suspend "L"`: tac2 closes tac1's FIRST subgoal, then suspend closes the SECOND. Only fires correctly when tac1 leaves ≥2 subgoals. For chain-on-single-goal, use `tac1 >> tac2 >- suspend "L"` (no inner `>- suspend` after intermediate transforming tactics).

## ⛔ Committed form: a GENUINE multi-arm induction keeps ONE Resume per CASE; everything else fully inlines
Rule owner: **skill Gate 1** — it defines the committed default and the two keeper cases; do not re-derive them here. What Gate 1 leaves to craft, and this section supplies: for a keeper induction, the shape is EXACTLY one `>- suspend "Ctor"` + `Resume thm[Ctor]:` per dispatch case.
- **Refactor a monolithic proof to the per-case shape FIRST, before fixing anything.** A `recInduct`/`Induct`/`Cases_on` proof that is one opaque `\\`-chain dispatching by `THEN1 (...)`/`>- (...)` replays as a single step `hol_state_at` can't enter ("target INSIDE step 0"), so you can't read any arm's goal. Convert EVERY case — including already-passing arms (else the prefix still replays opaquely and a regression in a "passing" arm hides), whether the break is in old arms or new ones (datatype gained a case; `evaluate_def`/`_ind` regenerated). Bonus: each Resume re-validates with a short arm-only replay, not the whole-file one.
- **Keep the per-case Resume bodies** — even trivial ones stay (the flat ladder of Resume blocks IS the committed table-of-contents); do NOT collapse them back into a monolithic `THEN1 (arm)` chain.
- **But inline sub-suspends back into their case-Resume** — labels nested *inside* one case for dev navigation are dev scaffolding (Gate 1); "build passes" / "precedent" do not license them. Keeper (b) is approval-gated PER INSTANCE; absent approval, inline (innermost-first, §Inlining technique), however large the case.

## ⛔ No-overengineering — minimal dispatcher, observe, then add
Before writing a multi-arm dispatcher with sub-suspends, **write the trivial body first** and observe what survives `Cases_on x >> simp []`. Half the arms you anticipate often close by simp itself; the rest often need just one inline chain. Sub-suspends are scaffolding for cases you actually CAN'T close inline — not a default partitioning device. (Local instance of CLAUDE.md "Fall back to simpler, not fancier".)

Workflow:
1. Write `Resume thm[X]: Cases_on q >> simp [] >- suspend "X_a" >- suspend "X_b" QED` (two suspends max; `>-` before each `suspend`, never `>>`/`\\`).
2. Probe `hol_state_at` at each suspend. If only one survived simp, drop the unused label and merge the body inline. If two survived, give them distinct labels and continue.
3. Add further sub-suspends ONLY after you see a body you can't close in <30s of inline tactics.

Skipping this produces a tree of `Loop_resX_qY_…` labels none of which match the live goal stack.

## Dispatch — pick by goal-order predictability
- **Order known** (post `Cases_on x >> gvs[]`, residual goals in datatype-constructor order): chain bare `>- suspend "A" >- suspend "B" >- suspend "C"`. `>-` is THEN1.
- **Order unpredictable** (post `recInduct evaluate_ind`, goals keyed by syntax constructors): `>~ [‘Module$Con’] >- suspend "Name"` for each arm.
- ⛔ `>~ [pat]` matches **subterms**, not whole goals. If the discriminator (e.g. `evaluate (Loop _ _ _, _)`) appears inside one of the case-tree arms of the OTHER goal, `>~` can land on the wrong goal. Either pick a discriminator that ONLY appears in the target goal's conclusion shape, or partition positionally with `>-`/`>>` after a Cases_on.

When dispatch is flaky, fall back to **simpler** (`>-` from `>~`), not fancier (`>>~`, `>>~-`) — CLAUDE.md Working principle.

## Locality and form of `Resume` blocks
A Resume block is `Resume thm[Label]: <tactics> QED` — always QED-terminated, like a `Proof` — and lives IMMEDIATELY after its parent's `QED`, not at the bottom of the file. One screen between suspend point and body.

## ⛔ "No such label" / lost suspension / `replayed=0` / same goal at two lines → an ancestor failed (YOUR fault); find it
The framework stashes a suspension only once the dispatcher that issued `suspend "X"` runs through to its `QED`. A broken tactic in ANY ancestor — the parent `Theorem … QED` or any intervening `Resume thm[Parent]: … QED` — stops replay there, so every later suspend never fires. This is the cause >99% of the time: a proof/navigation fault YOU made (a tactic that fails in file-form, a mis-targeted line, an unparenthesised `by`-chain, a wrong-context subgoal), NOT a cache that needs "warming" and NOT an MCP bug (RULE D).
- `replayed=0/N` (or the same goal at two consecutive lines) means replay never advanced past a `PROOF BROKEN at line L` — read L and fix it; stop re-probing line numbers.
- Find the break: `hol_state_at` each ancestor's `QED` in source order until one fails; repair that body, re-navigate.
- Forbidden: manual `hol_send` of the parent to repopulate; sprinkling `proofManagerLib.set_goalfrag`; re-probing a line for the cache to "warm up"; backward-nav/restart "resets".
- ONLY a genuine Holmake-vs-MCP divergence on a provably-correct proof is an MCP bug → surface a minimal reproducer (Holmake is source of truth). Report, never work around.

## ⛔ One label per goal: a `\\`-distributed `>- suspend "L"` over N parallel goals = DUPLICATE label → dispatcher RAISES at load
When the prefix has split into N independent goals (e.g. two stack-frame cases from an early `Cases_on h`, Env vs Exc), a single `\\ conj_tac >- suspend "L"` is applied to EACH goal by THEN-distribution, so label `L` is registered N times. `markerLib.suspend` rejects the duplicate → the dispatcher `Theorem … QED` raises an exception "at load" (NOT an unsolved-goals "PROOF BROKEN"), so NO sub-suspension records and every Resume reports its ancestor "failed at load". Symptom: `hol_state_at` past a Resume QED prints `first broken ancestor: Theorem … (line L) — failed at load: error: Exception-`.
- **Fix**: suspend at the SPLIT point with DISTINCT labels — one per parallel case (`>- suspend "X_env" >- suspend "X_exc"`) — BEFORE the shared conjunct work; put the common tail in an SML `val tac_tail = (…)` above the theorem and use it as each Resume body (`Resume thm[X_env]: tac_tail QED`). No duplication, distinct labels, both navigable.
- **Don't** try to localise the failing leaf by re-running `hol_check_proof` on the opaque `\\`/`>-` chain (RULE C violation; the failure stays wrapped in "Tactic execution failed", and `hol_state_at`/`show_partial` only show the step ENTRY). Sub-suspend FIRST — the per-Resume QED checks then localise immediately (which frame, which conjunct). The whole point of sub-suspending is that the FILE owns each prefix.

## Nested Resume / sub-suspensions work mechanically (dev only — inline back per the canonical-form gate)
A Resume body MAY itself issue `suspend "X"` for further sub-labels; a later `Resume thm[X]: …` then resumes those. Both `Holmake` and the MCP file-replay path handle nesting; after file replay, deep Resume sub-bodies are reachable through normal navigation — no manual repopulation needed.
- ⛔ **The header takes ONE label level however deep the nesting** — labels are a flat namespace per THEOREM. A sub-suspend issued inside `thm[a]` is resumed by `Resume thm[b]:`, on the BASE theorem name. Neither `Resume thm[a][b]:` (a HOL parse error) nor `Resume thm[a,b]:` (HOL reads the entries after the first as proof attributes, so a bare `b` is an unknown attribute) is a label path: H17 refuses either once, and navigating into such a block names the header. Corollary: labels must be unique across the WHOLE theorem, not just within one case.

## Reading / developing / validating a Resume sub-goal — `hol_state_at` is primary
- **Develop in the script file**: write the body inside `Resume thm[Label]: … QED` and navigate with `hol_state_at` — it replays the FULL prefix in file order, so the goal is exactly the file-form (accurate) one. **VALIDATE** the body by `hol_state_at` PAST its OWN `QED` → "No goals" (per the hol4-proving skill suspend/Resume procedure: dispatcher's QED first, then each sub-resume's own QED).
- `markerLib.set_suspended_goal {…}` (directly, or vim `hG`) only LOADS the stored goal — a suspension-store LOOKUP, not a dispatch replay. The loaded goal is correct (aconv-identical to the file-form goal) ONLY once the dispatcher reached its QED in the same file state, but loading it re-runs NOTHING and tells you nothing about whether the surrounding tactics replay. Prefer `hol_state_at`; never conclude "the dispatch works" from being able to load a sub-goal.

# ADVICE

## Inlining technique — diff-and-bridge
When inlining `suspend "X"` / `Resume thm[X]: <body> QED`:
1. Snapshot the suspend-site goal with `hol_state_at` BEFORE editing.
2. Inline the body; delete the Resume block. Non-final arms inline as `>- (body)`. The FINAL arm is usually the main line of reasoning — flatten it onto the main thread as `\\ tac1 \\ tac2 …` (a LARGE closing `>- (…)` there is a style violation; safe because one goal remains: `\\` ≡ `>-` on a single goal). Keep `>-` when the final goal is genuinely just another sibling subgoal — judgement call.
3. Snapshot the inline-site goal AFTER editing.
4. Diff. Common deltas: extra subgoals from `>>` distribution, different asm order, missing/extra case-split. Patch with `>~ [pat]`, asm rename, or a head `Cases_on` — usually 1–3 lines.
5. Revert only if the gap is substantive. Don't `fs[]`/`gvs[]` blindly hoping it closes.

**Script-based inline-back of a large case tree**: use a FIXPOINT leaf-inliner — repeatedly inline any sub-suspend whose body has no further `>- suspend` (a leaf), until only the top-level case Resumes remain; this auto-handles arbitrary nesting with no manual innermost-first ordering. ⛔ Make the wrapper SHAPE-AWARE: if the body is already exactly one balanced `( … )` group (the common leaf), emit `>- body`, not `>- (body)` — the extra layer leaves redundant `>- ((X))` / cascading `))` to strip later. And flatten each dispatcher's FINAL arm onto the main thread (`\\`-chain) when it is the main line of reasoning, per step 2 above. (A positional "first paren group" extractor mishandles dispatcher bodies that aren't single groups; a parenthesis-balance walk handles both.)

## `>~` gvarify pitfalls
See [[feedback_hol4_mcp_proving]] §gvarify trap. Patterns must use `_` wildcards for any name that should NOT rename context; qualify overloaded constructors `Module$Con`.
