---
name: feedback_proof_plan_pointers
description: Required-pointer checklist for any plan that discharges cheats, ports proofs, or fixes broken HOL4 proofs, plus ordering rules for new-formalization plans. Plans MUST lead with these.
metadata:
  type: feedback
---

When writing a plan for proof work (discharging cheats, porting a proof, fixing a broken theorem, building a new formalization), the plan **must** start with an "Operating principles" section pointing to the rules below. Rules belong up front so the implementer cannot skip them.

# GATES — rules to cite in every proof-plan's "Operating principles" section

(All HOL4 sections below live in the `hol4-proving` skill — `~/hol4-mcp/skills/hol4-proving/SKILL.md`.)

- **⛔ RULE A** (skill)
- **⛔ RULE B** (skill)
- **⛔ RULE C** (skill)
- **⛔ RULE D** (skill)
- **⛔ Post-discharge audit gates** (skill — particularly Gate 1, inline-back)
- **HOL4 — suspend/Resume/Finalise** (skill, plus [[feedback_suspend_resume]] for dispatch + inline-back craft)
- **HOL4 — banned tactics** (skill)
- **HOL4 — iteration loop** (skill — tool selection + end-of-proof verification ladder; details in [[feedback_replay_discipline]])
- **Read the original before adapting** (skill §HOL4-specific working principles, plus [[feedback_unprovable_vs_unfound_proof]] for the case-3 framework)
- **⛔ Editing and git** (global CLAUDE.md)

# RULES — required structure of the plan body

- **Per cheat: obligation in plain English, then discharge sketch in one sentence per leaf** (per RULE B). Not "use lemma X" — say what each `Cases_on`/`>~` arm is and what closes it. If you can't write the sentence, the plan isn't ready.
- **Navigation note**: identify any cheat whose live goal sits inside a `THEN1 (…)` / `>- (…)` block; default to sub-suspend restructure (`hol_send` prefix replay only as a risky fallback) before writing tactics. See [[feedback_replay_discipline]] §state_at navigation.
- **Plan the inline-back as the final step.** Skill Gate 1 owns what may survive and what must go — read it there rather than restating it in the plan. What the PLAN must add: state up front which final form each cheat targets, so the inline-back is scheduled work and not a surprise at the end. Gate: `grep -nE 'suspend|^Resume |^Finalise '` returns ONLY Gate-1 keepers (nothing, in the default case). Inline-back craft: [[feedback_suspend_resume]].
- **Verification step**: cite the End-of-proof verification ladder (hol4-proving skill, HOL4 — iteration loop). Do not invent variant verification steps.

# RULES — new formalization / new-feature plans

- **Informal argument first.** Write the pen-and-paper proof sketch before any HOL text; if you can't write it, you're not ready to formalize.
- **Order: definitions → theorem STATEMENTS (cheated) → proofs.** Be critical that each definition/statement captures the intended concept BEFORE proving against it — a wrong definition costs every downstream proof, and late detection is [[feedback_unprovable_vs_unfound_proof]] case 3.
- **Interface before consumers**: prove each new definition's basic lemmas up front ([[feedback_hol4_mcp_proving]] §Proof strategy).
- **Statement changes**: generalizing a statement YOU authored is fine iff the intended result still follows by instantiation; weakening (extra hypothesis, dropped case) needs explicit justification in the plan. Diverging from a user-approved statement — even provably stronger — is a report-up (global CLAUDE.md, deviations rule).

# ADVICE

- **Out-of-scope reminders**: plans focused on one file should note deferred cheats in adjacent files as one-liners only — do NOT detail strategy for them.
- **Refactor plans: stages are not frozen.** When the proof for the new shape gets stuck, the fix is often upstream (definition, invariant, helper lemma), not downstream (more tactics). Indicate willingness to revisit earlier stages. Anti-pattern: papering over a definition bug with proof gymnastics.
