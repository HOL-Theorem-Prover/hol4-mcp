---
name: reference_hol4_docs
description: Governance for the HOL4 documentation corpus — the layering (where each fact lives), the 7 quality criteria every entry must pass, and the procedure for adding/changing a note so the files stay consistent. Consult BEFORE editing the hol4-proving skill, any HOL4 feedback_*.md, the hol4-mcp hooks, or the MCP server messages.
metadata:
  type: reference
---

# HOL4 documentation corpus — architecture + edit governance

The HOL4 guidance is a LAYERED system. Each fact lives at ONE layer; other layers
POINT to it (a one-line `[[link]]` or "see X"), never copy it. Edit at the layer
that OWNS the fact; fix pointers, don't fork content.

## Layers — where a fact belongs
| Layer | File(s) | Owns | Loaded |
|-------|---------|------|--------|
| Generic behaviour | `~/.claude/CLAUDE.md` | non-HOL4 rules (git, editing, memory-writing, working principles) + the pointer to the skill | every session |
| HOL4 RULES | `~/hol4-mcp/skills/hol4-proving/SKILL.md` | the proof-interaction ruleset: audit gates, RULES A–K, iteration loop, suspend/Resume rules, banned tactics. Imperatives + triggers + one-line pointers | every HOL4 task |
| HOL4 technique | `~/hol4-mcp/skills/hol4-proving/notes/*.md` (this dir) | the detailed HOW the rules point to (tactic behaviour by symptom, dispatch/inline craft, replay discipline, plan pointers, unprovable-vs-unfound). One source per topic | MANDATORY at a trigger, not upfront: the skill's symptom index makes each section a required read when its symptom appears (RULE E), and four notes are whole-file trigger reads |
| Runtime enforcement | `~/hol4-mcp/hooks/h*.py` (+ `README.md`) | mechanical blocks/reminders at the tool call. Message = terse restatement of the rule it enforces | fires during work |
| Point-of-contact | `~/hol4-mcp/hol4_mcp/hol_mcp_server.py` (`instructions=`, tool docstrings, runtime output) | "how to read THIS tool's output/params" + the actionable markers it emits | every session (always in context) |

The whole HOL4 corpus lives in the `hol4-mcp` repo under `skills/hol4-proving/` — deliberately NOT under that repo's `.claude/`, so it is a proof-work skill available everywhere (via the `~/.claude/skills/hol4-proving` symlink) and not a project skill that auto-loads when developing the MCP server itself. HOL4 technique notes are no longer global memory: they are `notes/*.md` here, reached through the skill's symptom index and its trigger reads.

**Single-source map** (topic → owner; everyone else points):
- sub-suspend-is-first-move → skill *HOL4 — suspend/Resume*
- banned tactics, tactic abbreviations, audit gates → skill (H1/H17/H24 enforce or advise)
- which normaliser to reach for, and the `[simp]`-tag decision → skill *which normaliser* (the rule) → `feedback_hol4_mcp_proving` (the measured consequences)
- tactic behaviour by symptom / prover-gen names / gvarify / matcher traps → `feedback_hol4_mcp_proving`
- auto-cheat / TIMEOUT / desync / navigate-in-accurate-state → `feedback_replay_discipline`
- dispatch & inline-back craft / "No such label" recovery → `feedback_suspend_resume`
- symptom → note routing → the skill's symptom index (the ONLY such index; do not add per-note copies)
- proof-composition defects (adjacent normalisers, `>-` not marking a sibling, near-identical arms) → `hooks/proof_sweep.py`, surfaced by H25
- running-server install / `localfixes` branch → `reference_hol4_mcp`; dev/test commands → `~/hol4-mcp/CLAUDE.md`

## The 7 quality criteria — every entry must pass ALL
1. **Clear** — one reading; states the trigger AND the action.
2. **Non-contradictory** — no line conflicts with any other line OR any tool/hook/runtime message.
3. **Succinct, guidance-not-history** — minimum tokens for the imperative; cut narrative/emphasis/pedagogy, all provenance (dates, commit hashes, "verified in X", fixed-bug stories), and internal tool details; state the CORRECT form, not the negative example (these files cost tokens every read).
4. **Non-overlapping** — one home per fact; elsewhere a one-line pointer. Reinforcement allowed ONLY as a pointer at a point-of-contact.
5. **Correct & current** — matches the running tools/hooks/server TODAY (stale advice silently becomes a contradiction).
6. **Right altitude** — the fact sits at its owning layer (table above); wrong layer = dead weight or unfindable.
7. **Actionable, prioritised** — keyed to an observable trigger; tagged GATE (must fire) > RULE (when relevant) > ADVICE.

## Procedure — adding or changing a note
1. **Find the owner** (single-source map / layer table). Exists already? EDIT there; do NOT fork a parallel note.
2. **New fact → place by altitude** (criterion 6): an imperative → skill; a technique detail → the matching `feedback_*` (extend it, don't spawn a new file unless it's a genuinely new topic); a tool-output marker → the docstring; a mechanical guard → a hook.
3. **Add pointers, not copies** (criterion 4). Catch yourself pasting a paragraph that exists elsewhere → stop and link.
4. **Move the whole row together** (criteria 2+5). A changed tool BEHAVIOUR means the hook message + docstring + skill rule that describe it must ALL update in the same pass — grep the other layers for the topic and reconcile.
5. **Verify mechanically — run `corpus_check.py`** (from `skills/hol4-proving/`). It resolves every `[[link]]`, every `§Section` citation, every cited path and H-number, and reports any long verbatim run shared by two files. ⛔ It is the guard against the commonest defect this procedure exists to prevent: **renaming a section silently orphans every pointer to it**, and nothing else complains. Then re-read the changed sections end-to-end — the checker cannot judge whether a claim is still TRUE. Hooks additionally: `install_hooks.py --check`, and `python3 -c "import ast; ast.parse(open(f).read())"`.
6. **hol4-mcp repo edits** (hooks/server/README): a git repo, often dirty with WIP — edit only on a real defect (staleness/contradiction), leave the tree dirty, no commit without `git ok`.

(Generic memory-writing hygiene — global-vs-project placement, search-before-write, rule-not-war-story — stays in `~/.claude/CLAUDE.md`; this file is only the HOL4-corpus specifics.)

## Health signals (smells that mean "fix the source")
- A fact **rediscovered by debugging although it is already written down** → it is indexed by CAUSE and was searched for by SYMPTOM. Add a symptom-index row, or a runtime hint at the failing tool call (H6's symptom table). Do NOT restate the fact; a second copy makes retrieval worse, not better.
- A rule needing an "ignore the tooling message that says X" carve-out → the message is the bug; fix the message, delete the carve-out.
- The same imperative restated >2× across layers → collapse to one owner + pointers.
- A hook/docstring/runtime message recommending a now-discouraged tactic (e.g. `eall`/`expandf` on a goalfrag, cheat-bisection, `hol_send` reconstruction) → a live contradiction; fix at the message's source, not by adding a counter-rule.
