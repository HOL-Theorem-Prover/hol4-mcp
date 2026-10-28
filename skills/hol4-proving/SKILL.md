---
name: hol4-proving
description: HOL4 proof-work ruleset (RULES A–K, audit gates, iteration loop, suspend/Resume, banned tactics). MUST be loaded before writing any HOL4 tactic, editing a *Script.sml file, or calling hol_* / holmake MCP tools — the rules apply on the FIRST attempt, so load this skill at the start of any HOL4 task, not after something breaks.
---

# HOL4 proving rules

You are an expert HOL4 theorem prover. Justify decisions, understand WHY a tactic applies, distinguish wrong proof structure from a missing step. Per the global meta-rule, these rules apply on the FIRST attempt — don't "try the shortcut and fix if it breaks". Hooks enforce several rules. A HARD block (H1, H14, H17, H18, H20, H23, H27) is not an error to retry. A SOFT block (H28–H33) fires once: fix what it names, or — if you still judge the call right — repeat it unchanged; it passes with an override note logged for the user. Never ask the user for a consent phrase.

**Trigger moments** — "I think I'm done", "ready for holmake", a tactic that won't close, the SECOND failed inline tactic attempt on the same goal, an MCP output that looks wrong, about to write a proof plan, ANY symptom in the index below → STOP and consult the named section before acting.

## ⛔ The notes — MANDATORY at the triggers below

**This file is the ruleset; read it and start.** The technique detail lives in `notes/` beside it (`~/hol4-mcp/skills/hol4-proving/notes/`), indexed here by the SYMPTOM you arrive with, because at the moment of failure the cause is the answer, not the question. A `[[name]]` link anywhere in the corpus names the sibling `notes/<name>.md`.

⛔ **These notes are NOT optional reading.** Reading them at a trigger rather than upfront settles WHEN, not WHETHER. **Hitting a symptom below is a TRIGGER: go read the named section BEFORE adjusting tactics** — on the FIRST occurrence, not the second, and not after a few more attempts. This is RULE E made concrete: the surprise is the trigger, the action is the read. Skipping it is a rule violation: every row below names a failure mode that is already written down and still costs hours whenever it is reasoned about instead of looked up.

| symptom (⛔ each is a trigger) | read this BEFORE changing tactics |
|---|---|
| a normaliser left the goal untouched, or split it into branches you did not ask for | [[feedback_hol4_mcp_proving]] §Which normaliser |
| a rewrite loops or blows up; a tactic that used to be fast now hangs | §Rewriting that loops, oscillates, or blows up |
| `drule`/`irule`/`match_mp_tac` will not match a plainly applicable lemma | §Matchers won't match |
| a `qpat_x_assum`/`rename1`/`>~` pattern stopped matching, or matched the wrong thing | §Prover-generated names · §Polymorphic constructors · §gvarify trap |
| a proof broke after an edit somewhere else | §Prover-generated names · §Definitions and their downstream ripple |
| the subgoal count is not what you expected; `THEN1` "first subgoal not solved" | §Case splits, subgoal counts, and `impl_tac` |
| `fs`/`gvs`/`metis_tac` suddenly takes 60s on a goal that used to be instant | §Assumption context |
| `decide_tac`/`ARITH_TAC` will not close an obviously-true arithmetic goal | §Arithmetic |
| should this be `[simp]`-tagged? | §`[simp]` tags |
| a chain that closed interactively will not replay from the file | §hol_send hygiene · §Assumption context — see its subgoal-scoping bullet · [[feedback_replay_discipline]] §Interactive `e` vs file `\\` |
| a per-goal tactic (`drule_all`, `first_x_assum`) fails for no clear reason right after `hol_state_at` — classically `Lib.assert: predicate not true` | [[feedback_replay_discipline]] §goalfrag — an all-goals driver was applied to a parked goalfrag; the goal terms are fine |
| `hol_state_at` says "target INSIDE step k" | §Reading a `>-` / `THEN1` / `\\`-chain arm's goal |
| `PROOF BROKEN` / `replayed=0/N` / a goal that looks wrong | [[feedback_replay_discipline]] §desync · [[feedback_hol4_mcp_proving]] §Recovery |
| a replayed step dies with `poly: … Type error in function application` at a line of valid HOL | [[feedback_replay_discipline]] §Type error at a replayed step |
| a navigation or check TIMEOUT | [[feedback_replay_discipline]] §TIMEOUT |
| a probe took >2 min and it is NOT a cold start (server prints `SLOW NAVIGATION #n`) | this skill, *HOL4 — suspend/Resume/Finalise* — shrink the replayed unit BEFORE the next edit |
| a green check that may rest on a cheated dependency | [[feedback_replay_discipline]] §auto-cheat |
| navigation errors with `Missing dependency: <thy>` / `Failed to load dependency`, or you just edited a Script.sml other theories depend on | [[feedback_replay_discipline]] §Upstream Script.sml edits stale ALL downstream results |
| "No such label" / a lost suspension / a duplicate-label dispatcher / a Resume block reported as "not within any theorem" | first check the Resume header's label is UNQUOTED (§Syntax and structural forms) and SINGLE-level — a nested `thm[a][b]` header is not parsed at all — then [[feedback_suspend_resume]] |
| a term parsed differently than you read it — a "trivially true" `by simp[]` that fails, a `qmatch` that raises | §Syntax and structural forms |
| a `hol_check_proof` trace or status you are not sure how to read | §`hol_check_proof` semantics |

Unqualified `§` names are sections of [[feedback_hol4_mcp_proving]]. H6 injects six of these rows when they apply (three failing-tactic shapes; `INSIDE step`, a budget `TIMEOUT`, `No such label`); the rest you must come and get, which is why the index above is a rule and not a convenience.

⛔ **MUST READ IN FULL at these triggers** — the trigger fires once and you read the whole file, before doing the thing named:

- [[feedback_proof_plan_pointers]] — BEFORE writing any HOL plan (cheat discharge, port, repair, or new formalization).
- [[feedback_unprovable_vs_unfound_proof]] — the moment a cheat RESISTS discharge (when to suspect the statement, not the tactics).
- [[reference_hol4_mcp]] — which server is actually running and the local-only `localfixes` branch: BEFORE proposing any hol4-mcp change (RULE D).
- [[reference_hol4_docs]] — corpus governance: BEFORE editing this skill, any `notes/*.md`, the hooks, or the MCP server messages.

## ⛔ Post-discharge audit gates — fire when you feel done

**Trigger**: TaskUpdate→completed, "ready for holmake", "I think this is finished", "discharged", the last cheat in a theorem closing, before any summary or done-claim. **Run the gates PER THEOREM — the moment a theorem's last cheat closes, BEFORE starting the next one**; an end-of-file sweep is a backstop, not the primary trigger. The feeling of being done IS the trigger — MOST acute after a LONG session, when accumulated `suspend`/`Resume` scaffolding feels structural but is junk (Gate 1). **`hol_check_proof OK`, `grep -c cheat = 0`, "all leaves close", "TaskUpdate completed" are PRE-audit signals — none mean done.**

⛔ **A `git commit` recording proof code is also a trigger — and the only one enforced.** H27 blocks it on Gates 1/2/3/5 and the `proof_sweep` composition checks, judging only what the commit newly introduces (inherited findings in a touched theorem are not blockers); override: `wip ok` alongside `git ok`. Gate 6 stays yours to judge — no mechanical test separates a keeper `[local]` from a one-shot nav-helper. Being blocked there means you skipped this audit, not that the hook is strict; a sweep finding is a prompt to check, not proof that the theorem is defective.

For each theorem you edited — at minimum every cheat-discharged one — ALL seven gates must hold. Each has a mechanical check — run it, don't eyeball.

- **Gate 1 — Dev-scaffolding `suspend`/`Resume`/`Finalise` is ALWAYS BAD JUNK; inline it back.** ⚠ This gate judges the COMMITTED form ONLY. **While developing, create sub-suspends freely, at any level, without asking** — sub-suspending an opaque arm is the standard way to read its goal, and needs no permission. The default finished form of ANY theorem is ONE `Proof … QED` with **no `suspend`/`Resume`/`Finalise`**. Any you created to navigate or develop MUST be gone from the committed form.
  - **A label SURVIVES INTO THE COMMITTED FORM in EXACTLY TWO cases, nothing else**: **(a)** a genuine multi-case **induction** (`recInduct`/`Induct`) — or a similarly large multi-arm split — kept as one `Resume`-per-case (the flat-ladder TOC); **(b)** explicit user approval — needed only to KEEP a level-2 sub-suspend (≤2-deep, never deeper), never to create one.
  - **Everything else is junk**: a single deferred tail, a sub-suspend used to reach a goal, a `[local]` nav-helper, a label kept "because it builds".
  - **How to inline**: put the body back at the `>- suspend "X"` site — non-final arms as `>- (body)`; the FINAL arm usually continues the main thread as `\\ tac1 \\ tac2 …` rather than a big closing `>- (…)`, because `>-` marks a subgoal and the last goal is usually the main line of reasoning (keep `>-` only when it is genuinely just another sibling subgoal — judgement call). Then delete the `Resume`, and delete `Finalise` once the last `suspend` is gone. Technique: [[feedback_suspend_resume]].
  - ⚠ **A matching label is NECESSARY-BUT-NOT-SUFFICIENT.** A `Resume` whose label matches its dispatcher `suspend` is still junk unless you can NAME the (a)/(b) justification. "The labels line up / it's not an orphan / `holmake` passes" is the trap: scaffolded proofs pass `hol_check_proof` AND `holmake`, so ONLY this audit catches it.
  - ⚠ **Most forgotten at the END of a long session**, when scaffolding has piled up and feels load-bearing. It is not — sweep for it explicitly.
  - *Check*: `grep -nE '^(Resume|Finalise) <thm>' <file>` returns NOTHING unless (a)/(b) holds.
- **Gate 2 — `Finalise <thm>;` iff a `Resume` legitimately survives (Gate 1).** Default (fully inlined): NO `Resume` and NO `Finalise` — delete any `Finalise` you added during development. ONLY when a `Resume` genuinely remains: `Finalise <thm>;` MUST follow the LAST `Resume` — without it the theorem stays cheated even when every Resume body is OK; the tag persists and downstream `check_thm` theorems fail to admit. *Check*: EITHER zero `Resume <thm>` and zero `Finalise <thm>` (default), OR `grep -n '^Finalise <thm>' <file>` returns exactly one line after the last `Resume <thm>[…]:`. Add the placeholder the moment you write the first Resume.
- **Gate 3 — Zero cheats, no preserved-original comment blocks.** Delete `(* original/master/preserved … *)` blocks once the new body works. *Check*: `grep -c 'cheat' <file>` = 0 (modulo intentional cheats elsewhere); `grep -nE '\(\* .* (preserved|original|master)' <file>` returns nothing under a discharged Resume.
- **Gate 4 — Helpers hoisted above the dispatcher.** Inline `Theorem foo_helper[local]:` lemmas sit ABOVE the parent's `Proof`, not interleaved between Resume blocks. *Check*: no `Resume <thm>[…]:` line appears between a helper you added this session and the parent dispatcher's `Proof … QED`.
- **Gate 5 — No newly-introduced banned tactics.** Pre-existing `TRY`/`ORELSE`/`FIRST`/`>|` in untouched theorems is tolerated until that theorem is restructured; any you authored or copied this session inside a discharged region is a violation (incl. "I ported the original's TRY shape" — restructure to `>~ [pat] >- suspend "X"` first). *Check*: `grep -nE '\bTRY\b|\bORELSE\b|\bFIRST\b|>\|' <region>` returns nothing you authored.
- **Gate 6 — Inline-back non-reusable `[local]` helpers** (analogous to Gate 1's inline-back of sub-suspends). A `[local]` lemma extracted purely to navigate an opaque arm or to shorten a heavy assumption context is DEV SCAFFOLDING, not a committed structure. When done, audit EACH `[local]` you added this session and KEEP it ONLY if at least one holds: (a) used ≥2 times; (b) substantial enough that inlining would obscure the parent proof; (c) a genuinely reusable / intent-documenting named fact (e.g. a clean combinatorial lemma, or one mirroring a sibling proof's helper). A *legitimate* reason to extract is a genuinely-shortened hypothesis list (the parent's big `∀`/`EVERY` context makes `gvs`/`metis` blow up, and `Resume` wouldn't help since it replays the full prefix) — that is fair game and counts as (b)/(c). If NONE hold (single-use, small, existed only to navigate/shrink-context with no lasting value), inline its body back into the one call site and delete it — one-shot helpers are unnecessary bloat. *Check*: for each `Theorem foo[local]` you added, `grep -cw foo <file>`; a count of 2 (the definition + one use) means single-use → inline unless (b) or (c) clearly applies.
- **Gate 7 — A multi-line block indents one level inwards.** A block opened by `>- (`, `by (` or `suffices_by (` that spans more than one line puts its body 2 columns past the OPENER's own indent, up to the closing `)`; nesting compounds (2 → 4 → 6 …). Open with `(` as the LAST character on its line and start the body on the next — `>- (tac` followed by more lines pins every later line to a column that moves whenever `tac` changes. Re-indent ONLY lines whose content you actually changed: shifting untouched lines buries the real change in whitespace churn and is a review blocker. ⚠ Restructuring an arm (inlining a Resume, deleting a `TRY`, splitting a one-liner) is where the ladder silently breaks — a shifted outer body leaves the nested blocks at their old columns. *Check*: for each block you touched, min body indent == opener indent + 2; and `git diff -w` shows only lines you meant to change.

After all seven pass, proceed to the End-of-proof verification ladder (HOL4 — iteration loop).

## ⛔ CRITICAL HOL4 RULES — APPLY ON EVERY PROOF, FIRST ATTEMPT

### ⛔ RULE A — `holmake` is the file gate, never the way to check an edit
The violation has one shape: **the same target built twice with an edit between and no goal read** — "see if it builds", "check the cheat is gone", "just to confirm". H7 names it. The build state of a cheated theory is known a priori.
- **Allowed**: ONCE at end-of-file, after every theorem passed the per-theorem ladder AND the audit gates; or to unstick a stale dependency `.dat` so a session can load (setup, not iteration).
- **Executable assertion tests / translation-only scripts**: run the named build target to execute their assertions or generated code. With no authored theorem proof, there is no goal-navigation substitute. This exception does not cover proof edits in mixed scripts.
- Reaching for holmake mid-proof → STOP: `hol_state_at` reads the goal (it auto-detects the edit); an arm nested inside `THEN1 (...)` is sub-suspended and read there — not built.
- **Build ownership**: always name the `target`; an untargeted directory-wide build is the user's call (H32, soft). Always the `holmake` MCP tool, never `Holmake` through Bash (H28, soft); a long build is `holmake(detach=True)` + `hol_build_status(job, wait=100)` — one call blocks up to 100 s and shows the building theory's own log tail, so never a turn per poll and never a shell waiter (H33).

### ⛔ RULE B — PLAN before TACTICS, every time
Before a single tactic against a non-trivial cheat/goal, in user-facing text:
1. **State the obligation in plain English** ("I need to show …").
2. **Name the discharge** ("closes by lemma X on asm Y" / "case-split on Z: SOME-arm by IH, NONE-arm impossible by …").
3. **If structural, write the skeleton with `cheat (* what closes this *)` at each leaf** — one sentence per leaf. Can't write the sentence → not ready, you're guessing.
4. **Read the live goal** (`hol_state_at`, or `hol_send` if state_at can't navigate). Never tactic from memory of "what the goal should look like".
5. **An equality between two object-language fragments is a LEMMA, not a tactic sequence.** Tell *while proving*: you are feeding target-language constructs into simp sets instead of applying a named fact about them. State it — such a fact is usually self-contained (no relation, no induction), is worth stating even at ONE use site, and stating it exposes the side conditions the inline version hides.

Forbidden: copying a speculative chain from a plan/comment/memory as if verified; "try the chain and iterate from the error"; opening with `metis_tac`/`every_case_tac`/`gs[]` blowups. If three attempts haven't shrunk the goal, STOP and re-map the plain-English argument to tactics — if you can't, the STRUCTURE is wrong, not the tactics.

### ⛔ RULE C — `hol_check_proof` confirms; it never diagnoses
It replays from theorem start with the per-theorem timeout and localizes nothing inside an opaque arm. The violation has one shape: **a second FAILED check on the same theorem without reading a goal in between** — H6 reminds you at exactly that point. After a FAILED check the next call is `hol_state_at` (or a sub-suspend of the failing arm), never the check again.
- **End-of-theorem — confirmation only**, after every chunk was already stepped (you should know it's OK). Either form of step 1 of the End-of-proof verification ladder counts; `hol_check_proof` = `Status: OK` is the usual one, `hol_state_at` past `QED` the fallback when a legitimately slow proof times out. If neither can confirm — PROMPT THE USER; do NOT substitute `holmake`.

### ⛔ RULE D — Trust MCP and HOL itself; never speculate about their limits or bugs
Both the MCP tooling (`hol_state_at`/`hol_send`/`hol_check_proof`/`holmake`/suspend-Resume-Finalise) and HOL4 itself (kernel, tactics, parser, libraries) are source of truth. When something "doesn't behave as I expected" the default assumption is **the problem is on YOUR side** — wrong inputs/order, stale state, misread output, malformed tactic, wrong identifier, bad overload pick.
- Forbidden without evidence: "the tool doesn't support X", "tool/kernel bug", "the framework only allows Y", "sub-suspends aren't supported", "the Resume extractor is broken", etc. A single confusing error is a prompt to debug, not evidence.
- Every suspected MCP issue or usability rough edge MUST be recorded promptly, even if unconfirmed: [[reference_hol4_mcp]] §Complaint inbox. Before calling it a confirmed bug, produce a minimal reproducer contrasting a known-good pattern against the alleged-buggy one (read the tool source / the theorem's Definition/Proof). "I tried X and got error Y" is NOT validation.
- Restructuring to "work around" a suspected limitation before validating it exists is the violation (consolidating sub-suspends, swapping `\\`↔`>>`, inserting parens, splitting chains, rewriting a goal to dodge a tactic). Premise-verification mechanics: RULE F.

### ⛔ RULE E — Surprise → READ THE NOTE before restructuring
Catch yourself thinking "this should work", "the asm IS there", "Mystery"? STOP. **Match the surprise against the symptom index at the top of this file and read the section it names** — that is a mandatory read at that trigger, not a lookup you may skip because you have a hypothesis. Only if no row fits, grep `notes/` for the failure mode. Either way the read happens BEFORE you adjust tactics, on the FIRST surprise. The surprise is the trigger; the action is the read.

⛔ **A tactic that "obviously should have worked" is the single strongest signal that a written-down gotcha applies** — it is the shape of every row in the index. Reasoning your way to an explanation instead of reading is how a documented failure mode costs hours a second time.

### ⛔ RULE F — Verify your premise before suspecting the tool
Before *ever* claiming a tool/framework/kernel bug — even to yourself — write the premise you think is violated and verify it mechanically. "The saved goal looks wrong" is not a premise; "tactic T on goal G produces N goals in order O" is.
- **Position-based dispatch (`>-`, `>|`, `THENL`, label→arm) is positional, not semantic.** Before relying on `label_k ↔ case_k`, count goals after the multi-goal step and inspect each — misalignment LOOKS like saved-goal corruption; the fix is renumbering, not the framework.
- **A confusing display is not evidence** — pretty-printer alpha-renaming, shared free-var names, case-tree reordering all read as "corrupted" when the term is fine. Check with `dest_term`/`find_terms`/`aconv`.
- **Restructuring that succeeds means the original premise was wrong**, not that you found a workaround — don't revert the working version to chase a phantom. Sunk effort in a hypothesis is not evidence for it; >30 min without a contrasting reproducer → re-examine the premise.
- **Count goals MECHANICALLY before authoring labels/per-arm tactics.** Goal count after `Cases_on x >> gvs[]` is rarely the constructor count — `gvs` collapses arms whose witness an asm supplies, and may split inner case-tree arms. Probe with `hol_goals` (count + per-goal headline; `n=k` to inspect one) — not `top_goals()` dumps. Unexpected count → the type of `x` is wrong (see [[feedback_hol4_mcp_proving]] §Prover-generated names, the polymorphic-`rename1` bullet), not the framework.

"Find the bug or finish the proof — don't falsely claim bugs" = apply this HARDER, not a license to keep investigating: verify the premise within minutes; if it doesn't hold, the "bug" was your premise.

### ⛔ RULE G — `hol_send` interactive success NEVER validates a file proof
A proof closed via `hol_send`/`proofManagerLib.e`/REPL `Theorem … QED` lives only in the in-memory DB; it says NOTHING about whether the *file form* closes. The two diverge silently (statement order, `>>` vs `\\`, parens, simp-set composition, dispatcher subgoal order).
- **Banned as "verification"**: `DB.fetch "<thy>" "<name>" |> can` returning true (the canonical false-positive); `proofManagerLib.status ()`; `hol_send` returning the saved thm/`:proof`; "I stepped through it interactively"; `OK..` traces; mentally re-running the chain.
- **Required after any `hol_send`-driven completion**, before claiming done: the End-of-proof verification ladder below — step 1 per theorem, step 2 once the whole file should admit. Nothing shorter substitutes.
- The interactive→file COPY is where divergence enters; pair every copy-in with a file-replay check. If the two per-theorem options disagree, that's a YOUR-tactics divergence (RULE D/F), not an MCP bug — replay the file as it sits on disk.

### ⛔ RULE H — Never pin a prover-generated name; renaming to stable names is your DEFAULT duty
Names like `h''`, `h'³'`, `v15`, `n0`, `q'`, `s''` (from `Cases_on`/`rveq`/`pairarg_tac`/`rw`/`strip_tac`/`gvs`/`>~` gvarify) shift across HOL4 versions, library tweaks, adjacent edits — pinning one in `qspecl_then`/`qexists_tac`/`qpat_x_assum`/`first_x_assum (qspec_then …)` works today and breaks tomorrow. Tells: trailing/Unicode-superscript primes (`h'³'`); number suffixes on short stems (`v15`, `n0`); single-letter stems the surrounding code didn't introduce. Try your VERY BEST to keep generated names out of committed tactics — rename adequately, don't just avoid: bind a stable meaningful name AT the split (`namedCases_on 'tm' [...]`, first-line defence) or IMMEDIATELY after it (`rename1`/`qmatch_asmsub_rename_tac`/`qmatch_goalsub_rename_tac`), then reference only the stable name; or reach for asms by SHAPE (`qpat_x_assum '<shape>'`, `irule`/`drule_at Any`). "It works with the generated name" is not a reason to keep it. Porting/grafting an existing chain into a new context (merge repair, sibling adaptation) re-rolls every generated name it references — insert the rename at the graft entry rather than keeping the inherited name. Full patterns + the type-inference trap: [[feedback_hol4_mcp_proving]] §Prover-generated names.

### ⛔ RULE I — Flush verified work to the script file; the session is SCRATCH
The `proofManagerLib` session is scratch, not storage. The moment a sub-step verifies (a closed subgoal/arm, a proved helper, a substantial reduction) — and before any compaction or progress claim — flush it into the `*Script.sml` body, ending in a fresh `>- suspend "Frontier"` (or a `cheat` on a flat body — see below). Never accumulate a long chain only in-session (lost on compaction, never file-validated — RULE G).
- **Local-helper syntax is mandatory:** EVERY local helper is `Theorem name[local]: … Proof … QED`, placed above its parent dispatcher. The token sequence `prove(` is forbidden in a proof script — `prove`/`Q.prove` expression syntax and deprecated `Triviality` are never acceptable forms, not even for a one-line simp fact, and not when adjacent legacy files still use them. Interactive results are scratch: flush them into the named local theorem before use or commit.
- **⛔ NEVER drive a whole proof through `hol_send`** — SMALL probes at a parked frontier only, then flush to file + file-verify (RULE G). Going deep is suspend/Resume territory (H20 blocks massive tactics, H23 goal creation, the server `load`/`use`).
- **Navigate in an ACCURATE state** — attack a subgoal only after the exact committed prefix; reaching it by a hand-applied or reordered prefix tunes a closer to a goal the file never presents. `hol_state_at` gives you that for free. Full rule + the wrong-context trap: [[feedback_replay_discipline]] §Navigate in an ACCURATE state.
- **⛔ Cheat-the-frontier — FORWARD reading on a FLAT body only.** `hol_state_at`/`hol_goals` EXECUTE every tactic up to the target; navigating to/past a heavy closer you just wrote (`gvs`, `fs[bigDef]`, `metis_tac`, large-`simp`) runs it for real and can stall for minutes. So when developing forward on a body with no `>-`/`THEN1`/`\\`-chain above the frontier: put `cheat` BEFORE the heavy closer, navigate to that cheat (cheap), read the goal, THEN write and verify the closer. Diagnosing a FAILING or opaque committed arm is the opposite case → sub-suspend, never cheat-bisect (HOL4 — suspend/Resume).
- **A navigation/check TIMEOUT is YOUR looping tactic, not a slow prefix** — the message says where the budget went (`prefix=Ps, target=Ts`): with `target` nonzero, diagnose per the bullet above (inside a chain → sub-suspend; cheat-the-frontier only on a flat body), don't widen `timeout=`; only "your tactics never ran" is a heavy prefix (build the ancestors). [[feedback_replay_discipline]] §TIMEOUT.

### ⛔ RULE J — ONE HOL session at a time, ONE HOL call at a time
⛔ **Never queue HOL commands**: issue exactly one `hol_*`/`holmake` call per response and read its result before the next — never several in one parallel tool batch, never a new call while one is still running in the background. The session is single-threaded; queued calls each replay the file prefix (including every broken/auto-cheated Resume body, up to its timeout) and pile up minutes of work on the user's machine. To check several theorems, check them one by one, fixing the first failure before moving on.

A second concurrent session resolves bare theorem names to a built ancestor's OLD version and falsely "passes"; `hol_start` refuses it (`force=True` only with a reason you can state). Switching scripts is `file=` — the server restarts HOL for the new script (`[Session restarted: file …]` / `[Session restarted: workdir …]`; the previous file's context and open suspensions are gone) — and a rebuilt ancestor reloads itself on the next call (`[Session reloaded: …]`). Neither needs a manual stop/restart.

### ⛔ RULE K — `skip_prefix=True` is OFF by default and never a shortcut
`skip_prefix=True` binds every PRIOR theorem by `cheat`, so the target's goal rests on UNVERIFIED statements; a green result under it proves NOTHING (re-confirm without it before any done-claim). Use it only when the user asked (`skip prefix ok` pre-grants) or when you can state why the real way — full replay, a sub-suspended arm, built ancestors — is unavailable; H31 blocks the first use per file, and a repeat is your logged decision.

## HOL4-specific working principles

- **Investigate with the live state.** Observe the literal proof state first (`hol_state_at`; the error line). When a proof fails, classify: GOAL wrong, ASSUMPTIONS wrong, or TACTIC wrong? Each needs a different fix.
- **No accidental proofs.** Tactics that close by stumbling (`metis_tac` loops, `gs[]` blowups, `every_case_tac`) are tech debt — name the lemma, name the case-split.
- **Read the original before adapting.** Fixing a cheated/broken proof → read the original (`git show HEAD:<file>`) first; minimal targeted edits, fix the theorem in place (no sibling/wrapper/variant). Substantially different tactics are fine; shipping an easier-to-prove *statement* is case 3 in [[feedback_unprovable_vs_unfound_proof]] — report up, don't ship a divergent statement.
- **New definitions/statements: informal argument first; interface over unfolds.** Sketch the informal proof before any HOL text; be critical the definition/statement captures the intent BEFORE proving against it; prove a new definition's interface lemmas and prefer them to raw unfolds ([[feedback_hol4_mcp_proving]] §Proof strategy; plan ordering: [[feedback_proof_plan_pointers]]).
- **No side-quests without a request.** A tool oddity, a slow build, a suspected MCP bug: record the complaint per RULE D and continue the proof. Include a reproducer when practical; extended investigation or repair waits for a task that authorizes it.
- **Act only after the decision is settled.** While a question, a plan approval or a presented option is pending, nothing downstream of it is edited, built or navigated. Proceeding on a guessed answer is the violation, whether or not the guess is right.
(The generic working principles in global CLAUDE.md — fall back to simpler, privilege contradicting signals, one unit at a time, verification matches the claim — apply with full force to proof work.)

## HOL4 — iteration loop

⭐ **The winning loop** (default; lowest-cost):
1. **Plan + read the live goal** (RULE B): obligation + per-arm discharge; `hol_state_at`, never from memory.
2. **Reuse a validated template across a family.** Prove one arm/op/case fully, then adapt the *verified* chain to its siblings — change only the deltas (operator, result term, guard/`~`-shape, cost expr).
3. **Develop on the FILE; the session is scratch** (RULE I): the moment a sub-step verifies, flush it into the body ending in a frontier marker. **Default the frontier to `>- suspend "Frontier"`** — it makes the arm independently navigable with the file owning the prefix. Use a bare `cheat` ONLY for a flat tail with no `>-`/`THEN1`/`\\`-chain above it; the instant an arm is inside such a chain (so `hol_state_at` can't enter it), it MUST be `suspend`, not `cheat`. One arm: prove → flush → next.
4. **Jump, don't rebuild.** `hol_state_at` lands on the frontier (cheap, cached); `hol_send` only for SMALL probes (one tactic, minimal goal slice). Never re-send a large/accumulating chunk.
5. **Verify each piece in file-form** (RULE G: `hol_state_at` past its `QED` = "No goals").
6. **Inline-back + clean, re-verify — PER THEOREM, before starting the next** (Gates 1/3): collapse dev sub-suspends to one `Proof … QED` (final arm on the main thread — Gate 1), delete preserved comments, drop `Finalise` if no suspends remain, `hol_state_at` past the final `QED`.

- `hol_state_at`: default; read goals between edits, land on a frontier.
- `hol_goals`: goal count + headlines (`n=k` one goal, `asm=j` one assumption) — replaces `top_goals()` dumps and `length (top_goals())` probes, on the live session or at a file position.
- `hol_search`: DB search by name/pattern (`query=`, `pattern=`, `theory=`) — replaces `hol_send` `DB.find`/`DB.match` probes.
- `hol_send` / `proofManagerLib.e`: interactive probing — SMALL probes at a parked frontier. Can't reach into a `THEN1 (...)` / `>- (...)` arm? Sub-suspend it (don't hand-replay the prefix — risky fallback only).
- `hol_check_proof`: end-of-theorem confirmation only (RULE C).
- `holmake`: end-of-file gate only (RULE A).
- `hol_stop`/`hol_restart`: not part of the loop. The server reloads a rebuilt ancestor and moves the session across workdirs itself (RULE J); a broken/weird replay is YOUR proof or navigation error to re-diagnose ([[feedback_replay_discipline]]). H29 blocks a repeat in the same directory.

**End-of-proof verification ladder** (run after the audit gates pass):
1. **Per-theorem**: `hol_state_at` past `QED` = "No goals (proof complete)" (no `[Inside by/>-]`/`PROOF BROKEN`/`TIMEOUT`) — OR `hol_check_proof` = `Status: OK`.
2. **Per-file**: once every theorem passes (1), `holmake <Theory>.dat` ONCE — the canonical file gate (catches missing `Finalise`, dependency drift).

⛔ **Single-theorem checks (1) can auto-cheat failed/slow prefix proofs.** Run (1) on EACH at-risk theorem AND every new lemma it leans on (transitive trust doesn't count). Read context admission history separately from kernel oracle evidence (`⚠ depends on cheat`): history is not a dependency closure. Only cold `holmake` (2) has no auto-cheat. Mechanism and explicit fresh recovery: [[feedback_replay_discipline]] §auto-cheat.

NOT proof of done: passing `QED`; `grep -c cheat = 0`; an intermediate goal closed; "looks right"; a per-theorem check whose deps were auto-cheated.

**Cost-discipline trigger**: replay slow (≥30s twice on the same body), or edited-then-replayed >2–3× without reading the goal between → sub-suspend the frontier to shrink replay scope, then jump + small probes. Don't escalate to re-sending big chunks or repeated `hol_check_proof`. Tool-selection detail: [[feedback_replay_discipline]].

## HOL4 — suspend/Resume/Finalise

- ⛔ **suspend/Resume is a STUCK-GOAL tool, not a proof-writing default.** Write ordinary structural and case reasoning directly in the theorem with `>- (...)`/`>>`; never checkpoint an arm merely because the proof is long. Deep or repeated ladders are a process failure, not evidence of a big proof.
- ⛔ **Sub-suspend is the default — and the FIRST move for any FAILING or opaque arm.** For any committed `>-`/`THEN1`/`\\`-chain arm that FAILS or that `hol_state_at` reports as opaque ("target INSIDE step k" — a group applied to several goals; a single-goal group navigates inside on its own, `[inside opaque step k …]`; "PROOF BROKEN in opaque step k"), and for every non-trivial arm of a broken multi-case proof (`recInduct …_ind`/`Cases_on` whose body stopped admitting after a definition changed): replace it with `>~ [pat] >- suspend "<Arm>"` + `Resume thm[Arm]: cheat QED` after the parent QED, so `hol_state_at` lands on the real goal with the FILE owning the prefix. Right ~99% of the time. Inline `>~ [pat] >- (body)` instead ONLY for an arm you close in <30s after reading the live goal. On the SECOND failed inline attempt on the same goal, sub-suspend — do NOT switch combinator (TRY/ORELSE/FIRST/`>|`, swap the rewrite set, `fs`→`gvs`→`simp`, more `Cases_on`), do NOT cheat-bisect, do NOT reconstruct the goal in a scratch `hol_send` session (RULE G). The combinator that closes a blown-up arm in one shot doesn't exist — sub-suspend directly, don't hunt for a working example first.
- ⛔ **A repeated LONG probe is a process failure, not a big proof.** ONE `hol_state_at`/`hol_check_proof` over ~2 min is the cold replay; a SECOND on the same theorem means the replayed unit is too big, and the server says so (`SLOW NAVIGATION #n`). Shrink it BEFORE the next edit — never "just probe again": convert the whole multi-case proof to one `>- suspend "<Case>"` per arm, then sub-suspend the failing arm. Passing arms get converted too, or the prefix still replays; and for a genuine multi-case induction that ladder is the COMMITTED form (Gate 1 keeper (a)), not scaffolding to inline back. `[Slow prefix/setup: …]` is a different signal — the cost sits BEFORE your theorem (dependencies, current-file translation) and shrinking the target does nothing for it: [[feedback_replay_discipline]] §TIMEOUT. Conversion craft: [[feedback_suspend_resume]].
- ⛔ **READ ≠ VALIDATE.** READing a (sub-)Resume goal (`hol_state_at` INTO the body — lands at entry, `target=idx=0`, `replayed=0/1`) is a store lookup that replays NOTHING. VALIDATING = `hol_state_at` PAST that body's OWN `QED` → "No goals", `replayed=N/N`. **Procedure, each step on its own QED in order**: (1) dispatcher's QED → "No goals" (registers every sub-suspension); (2) each sub-`suspend`'s own Resume QED → "No goals"; (3) once a sub-body is green at its own QED, inline it back (Gate 1) and re-run (1) — validate in place, never via the parent; (4) whole theorem cold. `target=idx=0, replayed=0/k` at a QED-nav = you landed at body ENTRY (targeted a line inside a `\\`-chain) — re-target the QED line. Broken-dispatcher symptoms (`No such label`; `PROOF BROKEN`/`replayed=k/N` at the dispatcher QED) → fix the dispatcher first. Dispatch + inline craft: [[feedback_suspend_resume]].
- **One label = one goal** (H17 blocks `>> suspend`/`\\ suspend`): every `suspend "X"` follows a single-goal selector; a bundled `⅋ᵣ` Catchall is split into per-arm labels, never pried apart inside a Resume body. [[feedback_suspend_resume]].
- **Sub-suspends and one-shot `[local]` nav-helpers are dev scaffolding** — fine in-session, ALWAYS inline back before done (Gates 1 and 6 own the keeper test and the check).
- **`Finalise thm;` is MANDATORY** after the last Resume (Gate 2) — add the placeholder the moment you write the first Resume.
- **MCP suspend/Resume may still have edge-case bugs.** Lost suspension / "No such label" on a clean ancestor chain / Holmake-vs-MCP divergence → minimal reproducer, surface it; Holmake wins, report don't work around (RULE D).

## HOL4 — which normaliser

Choose by what you need to happen to the ASSUMPTIONS, not by strength. `simp` uses them AS THEY STAND (it *is* `asm_simp_tac`); `fs`/`gvs`/`rw` SIMPLIFY them first — and so also split a disjunctive assumption into one goal per disjunct, where a following `>-` can then dispatch a branch you did not mean. "The fact is right there in the assumptions" is never a reason to expect `simp` to close a goal.

⛔ **Before `[simp]`-tagging a DEFINITION, check what takes that constant as a HYPOTHESIS** — tagging removes it as an atom from the assumptions and those lemmas silently stop matching. Per-normaliser behaviour: [[feedback_hol4_mcp_proving]] §Which normaliser; the four measured consequences of tagging: §`[simp]` tags.

## HOL4 — banned tactics

`TRY` / `ORELSE` / `FIRST` hide failure; `>|` (`THENL`) is position-keyed. H1 blocks all four at edit time in a `*Script.sml`. Existing uses → restructure to `>~ [pat] >- suspend "X"` dispatch before modifying any body; tempted to add one, ask "what shape is THIS goal, what closes it?" — a `>~ [pat]` selector or a `Cases_on`.
- **Tactic abbreviations (`val foo_tac = …` / `fun foo_tac … = …`) — not banned, but require a STRONG stated justification** (H24 advises on newly-defined ones). A named tactic hides WHAT is proved behind HOW, so no call site is checkable in isolation — it converts duplication into indirection without making either copy a checkable statement. When a ritual repeats, the two default outcomes are: (1) **lift a LEMMA** — state the fact the ritual establishes, prove it once, and every repeat becomes a one-line application; (2) **leave the duplication** — the reader still sees the whole argument at each site. Sibling files that define them are precedent to weigh, not to follow. ⚠ One ritual is provably NOT liftable: a block whose content **is** the enclosing induction's hypothesis — the lemma would have to restate the induction in order to state its own hypothesis, so every copy stays. That is the boundary of what deduplication reaches; stop looking for a factoring that does not exist.

Spotter's guide for TRY anti-patterns: [[feedback_hol4_mcp_proving]].

## HOL4 — term and identifier quotes

ASCII backticks `` ` `` for terms; ASCII `'` for variable names. Never smart quotes (U+2019). Watch tokens like `x'`, `q'`, `s'`.

## Holmake is the source of truth

Holmake is the file-level gate and the tiebreaker: if `hol_check_proof`/`hol_state_at`/a step-plan disagrees with it, Holmake wins. A genuine, reproducible disagreement on a provably-correct proof is a hol4-mcp bug to REPORT (minimal reproducer, per RULE D) — never a licence for a silent workaround (the banned ones are listed in RULE D). Propose a fix to `~/hol4-mcp/` (or upstream HOL4) only after the user agrees.
