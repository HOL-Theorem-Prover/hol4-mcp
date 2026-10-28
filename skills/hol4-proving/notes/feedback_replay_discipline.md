---
name: feedback_replay_discipline
description: "#1 rule — navigate in an accurate state (full prefix); upstream-edit staleness (rebuild before downstream reliance, H30); tool selection; state_at navigation limit + sub-suspend recovery; desync is essentially never the cause."
metadata:
  type: feedback
---

# GATES

## ⛔ Navigate in an ACCURATE state: apply the COMPLETE prefix before attacking a subgoal
**The single highest-cost violation. It is a NAVIGATION-accuracy rule — NOT a desync, NOT an `hol_state_at` fault, NOT a reason to avoid interactive `hol_send`.**

> ⛔⛔ **HARD BAN — NEVER hand-reconstruct a live goal with `proofManagerLib.g`/`set_goal`/`prove` to "test a tactic."** To reach a goal buried in a lumped `\\`-chain or a Resume body, **SUB-SUSPEND it in the FILE** (`>- suspend "X"` + `Resume thm[X]: cheat QED`) and land on it with `hol_state_at`'s full-prefix replay. If you *can* sub-suspend, you MUST — reconstruction is never the fallback. A typed-out goal silently drops/alters the real assumption context, so a closer "passes" on a phantom the committed proof never presents (RULE G), then breaks in file-form. Catching yourself typing `g ‘…’` to check an arm = STOP, sub-suspend instead. (Same principle, closer-testing angle: [[feedback_hol4_mcp_proving]] "Probe the REAL goal".)

Interactive `hol_send` probing at a parked frontier (`hol_state_at`, or `markerLib.set_suspended_goal`) is fine at skill-RULE-I scope only — a small tactic block, or fully closing a small goal; NEVER a whole proof (sub-suspend instead). Whatever you probe, the ONE thing you must get right: the subgoal you attack must have had the SAME prefix of tactics applied, in the SAME order, as the committed file body. Skip or reorder a prefix tactic and you are attacking a goal the committed proof never presents — your closer "succeeds" interactively against a phantom goal, and the file replay (`hol_state_at` / Holmake) then correctly fails. In that case `hol_state_at` is RIGHT; the proof genuinely diverges; there is no desync.

Telltale symptom of a dropped/reordered prefix step: a tail tactic over-runs with `THEN1: goal completely solved by first tactic` — the skipped step (often an "obviously redundant" `fs`/normalisation) had reshaped a later goal so an earlier tactic now closes it. Symptom = THEN1 over-run; cause = wrong context from a dropped prefix, NOT a tool fault.

**Do it right:**
1. When you park a frontier (`set_suspended_goal` or `hol_state_at`) and drill into sub-subgoals, run the body's prefix tactics **verbatim and in order** — never skip an "obviously redundant" simp/normalisation step (those reshape the goal). After each `e`, the live goal must match what the committed body produces at that point.
2. **`hol_state_at` is the zero-effort guarantee of an accurate state** — it always replays the FULL prefix in file order, so the goal it parks is byte-for-byte what Holmake sees. Prefer it for landing on a frontier; it removes all "did I apply the right prefix?" doubt.
3. **Going deep / nested subgoals → SUB-SUSPEND and PERSIST (RULE I), so the FILE owns the prefix.** Isolate each frontier with `>- suspend "Sub_k"` + `Resume thm[Sub_k]: cheat QED`; you then reach it via `hol_state_at`'s full replay and cannot lose track of which prefix is in force. The deeper the nesting (conjuncts of conjuncts, `IF_CASES` inside a `conj_tac` arm), the more checkpoints you lay down. This is the robust default for deep work — not because interactive `hol_send` is forbidden, but because persistence keeps the context exact and replayable.
4. **Validate file-form, always** (RULE G): the committed text must replay (`hol_state_at` past QED / `holmake`). Interactive close ≠ done.
5. Token hygiene: read goals via `hol_goals` (count/headlines/slices); inside `hol_send` print MINIMAL slices (`String.substring (term_to_string g) 0 300`) — never repeated full `top_goal()` dumps (multi-KB each).

**STOP-and-check triggers** (each is a wrong-context risk): re-running prefix tactics by hand to "get back to" a subgoal; developing a closer for a subgoal you reached by a shortcut; "this step is obviously redundant, I'll skip it". When unsure the prefix is exact → sub-suspend and let `hol_state_at` replay it.

## ⛔ `skip_prefix=true` — never a shortcut (rule owner: skill RULE K)
Off by default; the user pre-grants with `skip prefix ok`, otherwise H31 blocks the first use per file and a repeat is your logged decision. A green result under it proves nothing (re-confirm without). Manage replay cost the real way: build ancestor theories before proof work (setup `holmake <dep>.dat` — RULE A permits dependency unsticking), fix a file's theorems in file order so navigation replays a green prefix, and shrink scope with sub-suspends — never by skipping the prefix.

## `hol_restart` — the server reloads for you; never restart for a confusing replay
`hol_state_at` auto-detects edits to the file you are proving in, so a restart after editing is never needed. The one thing a live session cannot do — reload an ancestor theory rebuilt since it loaded — the server now does for you: the next `hol_state_at`/`hol_check_proof` rebuilds the session and prints `[Session reloaded: ancestor … rebuilt …]`; a `file=` naming another script restarts HOL for it (`[Session restarted: file …]` / `[Session restarted: workdir …]`). So nothing in the ordinary loop needs a manual stop/restart. A broken replay, a wrong-looking goal, or a tactic that will not close is a proof or navigation error: diagnose it (§desync), because the restart wipes the very state that localises it. H29 blocks a REPEAT stop/restart in the same theory directory within 30 min once (first stop, directory switches and a stop right after a budget TIMEOUT pass; a deliberate repeat passes and is logged; `restart ok` pre-grants); a second restart for the same symptom means the first substituted for a diagnosis you had not made.

## ⛔ Upstream Script.sml edits stale ALL downstream results — nothing reports it
Editing a `*Script.sml` invalidates every theory downstream of it, but no tool says so: live sessions AND fresh loads read the BUILT `<thy>Theory.dat` (HOL's `load` inspects no script content and no mtime), so downstream navigation and checks keep passing — against the PRE-EDIT upstream. GATE: after editing a theory other theories depend on, REBUILD it (mcp `holmake`) before relying on any downstream navigation, check, or green result. Batch upstream edits and rebuild once, but the rebuild comes before downstream reliance, never "later". H30 enforces this (make-style staleness over the target's ancestor closure; self-clears once artifacts are newer than sources; soft: blocks a stale set once, a deliberate repeat passes with a loud note and is logged; `stale ok` anywhere in the session pre-grants the deferral).

`Missing dependency: <thy>` identifies a failed dependency load before the target proof ran. Required theory interfaces stop initialization: build the reported `<thy>Theory.uo` target (a `.dat` alone does not supply its interfaces), or wait for the running build and retry. The MCP notices appearing/rebuilt interfaces and reloads on the next navigation. Do not edit tactics or stop/restart-loop against a missing interface.

## ⛔ A state_at / check_proof TIMEOUT is YOUR looping tactic — NOT a slow prefix
A navigation/check that times out (or visibly hangs) is almost always a **looping tactic you just wrote**, not the already-built prefix (prefix theorems replay fast — they're cached/compiled). The TIMEOUT message splits the budget for you: `prefix=Ps` (dependency load + current-file declarations + earlier theorems) vs `target=Ts` (your theorem's tactics). Read it. ⛔ Do NOT default to "the prefix is too slow" while `target` is nonzero; that is the wrong first diagnosis and wastes the budget retrying with bigger timeouts. Only "target tactics have not run" names the prefix — then read the `Active item` on that line (`hol_sessions` shows it live during a long call): a **dependency load** → build that ancestor only if its artifacts are missing/stale (an already-built heavy dependency wants a preloaded heap, not a rebuild); **top-level SML/translation** or a **preceding theorem** in the current file → that span is the cost, and neither rebuilding ancestors nor splitting your target touches it — a justified larger `timeout=` for the cold prefix, then warm navigation reuses the context.
- **#1 cause: `simp`/`fs`/`gvs`/`rw[<recursive_def>]` WITHOUT `Once`** — recursive defs AND recursive semantics predicates unfold forever, worst inside their own induction. Fix + variants: [[feedback_hol4_mcp_proving]] §Rewriting that loops, oscillates, or blows up.
- Other loops: a `GSYM`/symmetric-equality rewrite that oscillates (`a=b` and `b=a` both in scope); an unbounded `metis_tac`/`every_case_tac`/distributive-`simp` blowup.
- **Diagnose, don't widen the timeout**: frontier inside a `>-`/`THEN1`/`by (...)` chain → SUB-SUSPEND that arm; on a FLAT body only, put a `cheat` *before your newest tactic* and navigate to it (cheap) to read the goal. Then fix the loop. Only if that navigation is ALSO slow is the prefix/target genuinely heavy (raise `timeout=`). "Repeating the prefix-is-slow excuse" is the documented failure mode here.

## "desync" is essentially never the real cause
A wrong-context proof and a true desync show the SAME headline (`replayed=0/N` + `PROOF BROKEN at <first step>`), so the headline tells you nothing — assume bad navigation (the GATE above) and PROVE it by replaying the committed body file-form (`hol_state_at` past QED, or `holmake`); it fails there too because the proof genuinely diverges. Don't reach for backward-nav/restart "resets". A genuine `hol_state_at` position-cache desync is only *theoretically* possible; if you ever truly confirm one on a provably-correct proof, REPORT it (minimal reproducer to `~/hol4-mcp/`) — never work around (RULE D).

## ⛔ Type error at a replayed step
A Poly/ML type error can be a REALIZATION fault, not a proof error.
`goalFrag.expand` takes a tactic, so when the step plan realizes a construct's OPERAND span as itself the step is a bare term quotation and Poly/ML reports `Type error in function application` — pointing at a line of perfectly good HOL, and failing the whole theorem. READ THE STEP TEXT the failure prints: if it is not a runnable tactic, the proof is innocent and the realization is the bug. Reproduce with `goalfrag_step_plan_json` on that one construct, REPORT it (RULE D), and never rewrite the proof to dodge it.

## ⛔ Don't ACCUMULATE or RE-SEND proof state in `hol_send` — flush to the FILE, jump with `hol_state_at`
Interactive `hol_send` is fine for navigating/probing the current goal (the GATE above) — but it is SCRATCH, not where you build or store a proof. Two anti-patterns (the top token-waste failure mode):
- **Re-sending a chunk you already sent** (a tweaked variant), to "rebuild" the state. Each call re-prints a multi-KB goal; tokens compound brutally.
- **Accumulating a long verified chain only in the session** — lost on compaction, and never file-validated (RULE G).

Correct loop — **persist + interleave**:
1. The moment a sub-step verifies (a closed conjunct, a derived fact, a reduction), **flush it into the `*Script.sml` body** ending in `>- suspend "Frontier"` (or `cheat` on a flat body) (RULE I), so replay scope = that arm.
2. **Jump to the frontier with `hol_state_at`** to read the live goal — do NOT rebuild it by re-sending the prefix through `hol_send`.
3. Use `hol_send` ONLY for a small probe at the already-parked frontier; read goal state via `hol_goals` (it sees `hol_send`-driven goals too), never a full `top_goal()` dump.
4. On failure: isolate the SINGLE failing step and probe it small — do NOT re-send the whole chunk with a tweak.

A 30-line block belongs in the FILE (then `hol_state_at` past its QED to confirm), not in repeated `hol_send` calls.

## ⛔ Single-theorem checks auto-cheat failed/slow dependencies — only cold `holmake` has no escape
`hol_check_proof <thm>` / `hol_state_at` build the prefix (theorems before the target) **theorem-by-theorem, running each proof with a per-theorem timeout**. Any prefix theorem whose proof **errors OR exceeds the budget** is auto-cheated — re-sent as `Theorem … Proof cheat QED` to bind its name (prevents "value not declared" cascades). The TARGET is replayed in full, so it closes green **against a cheated dependency — one that is broken, or merely too slow to prove within the budget.**

- A correct, within-budget prefix theorem IS genuinely proven — it's not blanket cheating. The false-green hits when a dependency is **broken** (cheated → masks the break) or **over budget** (cheated → its real proof never ran this check).
- **Watch the `⚠ depends on cheat` marker**: `hol_check_proof` appends it to `Status: OK` when kernel oracle evidence shows the checked theorem USED a cheated dep (`hol_state_at`'s first-line marker is `⚠ context has admission history` — history in the loaded context, not established use). A clean `Status: OK` with NO marker = no cheated dep was used; `⚠ depends on cheat` = a dep was auto-cheated (broken, or over budget) → go verify THAT dep.
- **Context admission history is named with reasons**, separately from kernel oracle evidence. It can include later theorems visited earlier in the session; it is not a dependency list. A Resume whose label was never registered is listed as `SKIPPED, never ran`; missing labels also receive an ancestor-chain diagnosis.
- **Recover a transient admitted load explicitly** with `hol_check_proof(theorem=..., fresh=True)` once the file proof is ready. This restarts HOL and replays the full prefix without old bindings/checkpoints/verdicts; it does not waive oracle checks. Ordinary checks retain incremental reuse. Complete failing requests/responses are retained at the reported evidence path; `hol_sessions` also lists the latest path. Logs contain project source and live in a private temporary directory (last 20 per session; removed when the server exits unless `HOL4_MCP_KEEP_EVIDENCE` is set).
- **"Processed in replay" ≠ "verified".** Reaching a later theorem's goal via `hol_state_at` does not mean the intervening theorems built — the failed/slow ones were cheated. A green `hol_check_proof T` proves T's tactics relative to its deps' STATEMENTS, not the deps.
- **Discipline**: the marker tells you WHEN a dep was cheated; you still must verify it. To trust a multi-theorem change without `holmake`, directly check EVERY at-risk theorem AND every new lemma any of them leans on (a slow/heavy cost lemma is the classic miss). When in doubt, cold `holmake` — the only gate with no auto-cheat (RULE A end-of-file gate).

# RULES

## Tool selection

| Situation | Tool |
|-----------|------|
| Default iteration | `hol_state_at` |
| End-of-theorem confirmation | `hol_check_proof` |
| Goal count / headlines / one asm in full | `hol_goals` (`n=k`, `asm=j`) — never `top_goals()` dumps or `length (top_goals())` probes |
| DB search by name/pattern | `hol_search(query=, pattern=, theory=)` — replaces `hol_send` `DB.find`/`DB.match` probes |
| Hard sub-step exploration when state_at is slow | `hol_send` (`e(tac)`) |
| `state_at` returns the entry goal because the target sits inside `THEN1 (chain)` / `>- (chain)` | SUB-SUSPEND the arm (`>- suspend "X"` + Resume) — guarantees the exact prefix; manual `hol_send` prefix-replay only as a risky fallback (must be VERBATIM, see GATE) |
| Replay running >2 min | `hol_interrupt`, then debug |
| Body >200 steps and failing inline | `>- suspend "label"` + Resume block |

## `state_at` navigation limit and recovery
`hol_state_at` treats a parenthesized `THEN1 (chain)` / `>- (chain)` group as ONE step. It lands *inside* only when the group receives exactly one goal (then a flat replay is the file's own state; the output says `[inside opaque step k …: state after sub-step j …; position not cached]`). A group applied to several goals cannot be entered, by design, and the output says so (`NOTE: target line N is INSIDE step k … state shown is this step's ENTRY`); broken opaque steps report the step and its line range with sub-suspend advice (the tool explicitly says NOT to bisect by moving a `cheat`), and timeouts name the lumped span to split.

Recovery (preference order):
1. **Sub-suspend restructure**: replace `THEN1 (body_with_cheat)` with `>- suspend "ArmLabel"` + `Resume thm[ArmLabel]: body_with_cheat QED`. After leaves close, inline back per [[feedback_suspend_resume]].
2. **`hol_send` prefix replay (RISKY — the wrong-context trap lives here)**: manually send the prefix tactics VERBATIM and in file order. Drop/reorder one step and you debug a phantom goal (the GATE failure). Prefer (1); use this only for a trivial one-off where you can guarantee the prefix is exact.
3. **Probe a broken `\\ (block)` IN PLACE**: the failed replay parks the proofManager at the PRE-block goals (`replayed=k/N`); confirm with `hol_goals`, drive to the buried conjunct with small `e` steps, iterate a fix with `b()` (undo) + `e` (retry). Committing the fix to the file supersedes the in-session state — the confirming `hol_state_at` re-replays from the file, no reset needed.

(1) is the DEFAULT — it guarantees the exact prefix and is replayable. (2) only for a trivial one-off where you can guarantee the prefix is VERBATIM (else it's the wrong-context trap). (3) when a replay already broke at a parenthesized block and the manager is sitting right there.

## `hol_state_at` leaves a GOALFRAG — first-goal drivers only
`hol_state_at` parks the proofManager as a GOALFRAG. Bare `e` and `proofManagerLib.e`/`.expand` are first-goal-only there — drive normally. ⛔ Don't bypass via the unguarded all-goals drivers `Manager.expand`/`goalFrag.expand`/`expandf`/`eall`/`eta` — they apply the tactic to ALL goals (`>>`/THEN), so a per-goal (`>-`/THEN1) tactic misfires on siblings (classically `drule_all` → `Lib.assert: predicate not true`; the goal terms are fine — it is NOT metavariables). Diagnostic: a per-goal tactic failing for no clear reason (or an unexpected sibling goal) right after `hol_state_at` = suspect all-goals-on-goalfrag.

## Interactive `e` vs file `\\` — a TRANSFORMING tactic diverges
⛔ A TRANSFORMING tactic (a `gvs [defs, AllCaseEqs()]` that reshapes rather than closes) applied via one `e` touches goal 1 only; the file `\\` distributes it over EVERY open goal — sibling arms case-split and rename, so later positional `>-` arms see goals the interactive session never produced. When assembling a file form from per-goal interactive development: scope each goal's tactics under its own `>- (...)` arm; merge into a distributed `\\` only tactics verified to close (or no-op on) every open goal. (For CLOSING tactics, N successive `e tac` ≡ file `\\` — a goal-count difference means your tactics/context differ, not navigation.)

## `>>~-` vs `>~` — match semantics
Owner: [[feedback_hol4_mcp_proving]] §`>>~- ([pat], body)` semantic.

# ADVICE

## Hygiene
- Bundle multiple known fixes into one edit before triggering replay.
- ⛔ **Don't bisect a failing proof by moving a `cheat` through the chain** — and don't `reverse conj_tac`/reorder arms to hoist one for cheat-navigation, don't re-run `hol_check_proof` to read "FAILED at step N" (RULE C), don't reconstruct the goal with `hol_send`/`e`/`sg` (RULE G). FIRST move for any failing/opaque arm is SUB-SUSPEND (rule owner: skill §suspend/Resume); cheat-at-frontier (RULE I) is forward reading only. Don't pivot when stuck — debug.
- For `hol_send` shadowing pitfalls (concl/hyp/gs/...) see [[feedback_hol4_mcp_proving]].
- Mechanical text transforms (inline-back, paren collapse, comment strip): check cheap INVARIANTS before the build — `(*`/`*)` balance, paren net/min-depth, edits-made vs expected — a transform bug surfaces instantly. After applying across files, grep each for artifacts (redundant wrappers, bare-paren cascades, leftover scaffolding, process-narration comments) and split yours from pre-existing via `git blame`.
