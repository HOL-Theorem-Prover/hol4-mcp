# hol4-mcp Claude Code hooks

This document describes the Claude Code registration of the shared `h*.py`
policy scripts. The additive Codex registration is `hooks/hooks.json`; its
payload and state-isolation adapter is documented in
`integrations/codex/README.md`. The Codex layer does not change
`~/.claude/settings.json` or the Claude hook-state directory.

Runtime-enforced interaction policies for HOL4 proof work. Each hook is a
standalone script invoked by Claude Code at a defined lifecycle event
(`PreToolUse`, `PostToolUse`, ...); see
<https://docs.claude.com/en/docs/claude-code/hooks> for the framework.

Hooks are wired in `~/.claude/settings.json` under the top-level `hooks` key
and point at scripts in this directory. The scripts are policy code, kept
under `~/hol4-mcp/` because they enforce HOL4-specific behaviour; settings.json
just references them.

## Why hooks

CLAUDE.md / skill rules are advisory — the model can violate them and rely on the
audit gates to catch it later. Hooks are **runtime-enforced**: a PreToolUse
hook returning exit 2 blocks the tool call entirely, with the stderr message
surfaced to the model as a tool error. This forecloses entire failure modes
(e.g. newly-authoring `TRY` in a `.sml` file) rather than relying on post-hoc
catch.

## Suite map

Status legend: ✅ shipped · 🚧 in progress · 📝 proposed (not yet implemented) · ⏭ skipped (won't implement).

| ID  | Status | Event(s)              | Matcher                | What it does |
|-----|--------|-----------------------|------------------------|--------------|
| H1  | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Block newly-authored banned HOL4 tactics (`TRY`, `ORELSE`, `FIRST`, `THENL`, `>\|`) in `*Script.sml` edits |
| H2  | ⏭     | PreToolUse            | `Edit\|Write\|MultiEdit` | ~~Nudge to run `check_quotes.py` when smart-quote U+2019 appears in a variable-name position~~ — skipped (high FP risk; HOL4 fancy quotes `‘…’` legitimately use U+2018/U+2019, distinguishing variable-name position from term position is brittle) |
| H3  | ⏭     | PreToolUse            | `Write`                 | ~~Block writes to `~/.claude/memory/` containing project-specific anchors~~ — skipped (token fingerprint list is high-maintenance; not worth the upkeep for a placement rule the audit gates already catch on read) |
| H4  | 📝     | PreToolUse            | `Edit\|Write\|MultiEdit` | Warn on `Resume` body starting with `‘Q’ by tac` (step-plan splits at `by`) |
| H5  | ⏭     | PreToolUse            | `mcp__hol4__hol_check_proof` | ~~Block re-call after FAILED with no intervening `hol_state_at` (RULE C)~~ — skipped (H6 covers the failure-time nudge; the block-step needs per-session state that wasn't worth the machinery) |
| H6  | ✅     | PostToolUse           | `mcp__hol4__hol_check_proof\|hol_state_at\|hol_goals` | On `FAILED` / `TIMEOUT` / `PROOF BROKEN`: the symptom-table hint for the failing tactic on every failure; the RULE C reminder only from the SECOND consecutive failure on the same theorem (per-session state; a pass or another theorem resets). Silent first failure with no matching row. Advisory only |
| H7  | ✅     | PostToolUse           | `mcp__hol4__holmake`    | RULE A reminder on repeated builds of the same target within 30 min after an authored proof-block change. Assertion-only, translation-prefix-only, unrelated-file, timestamp-only and already-validated proof revisions are silent. Advisory only |
| H8  | ✅     | PostToolUse           | `mcp__hol4__hol_state_at` | Inject cost-discipline reminder on any single `hol_state_at` call whose `replay` time ≥ 30s (stateless; cache hits and error paths skipped) |
| H9  | ⏭     | PreToolUse            | `mcp__hol4__hol_restart` | ~~Default-block; CLAUDE.md says "effectively never"~~ — skipped (escape-hatch design too messy for the rare legitimate case; CLAUDE.md text is sufficient deterrent) |
| H10 | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Inject Finalise reminder when a Resume block introduces a new theorem to a `Script.sml` without a matching `Finalise <thm>;` (diff-aware on theorem names; sub-Resumes on existing theorems silent) |
| H11 | ⏭     | PreToolUse            | `mcp__hol4__holmake`    | ~~Gate 1: no leftover sub-Resume labels outside the dispatcher's `suspend` set~~ — skipped (parsing complexity not justified now; Gate 1 audit at end-of-discharge still covers) |
| H12 | ⏭     | PreToolUse            | `mcp__hol4__holmake`    | ~~Gate 3: no `(* preserved/original/master *)` comment blocks in discharged regions~~ — skipped (low-value debris check) |
| H13 | ⏭     | PreToolUse            | `mcp__hol4__holmake`    | ~~Gate 5 cross-check: scan git-modified theorems for banned tactics~~ — skipped (subsumed by H1 at write-time; safety-net value low) |
| H14 | ✅     | PreToolUse            | `Bash`                  | HARD. Block destructive git ops without literal `git ok` in the latest user message (transcript-aware; fail-open if transcript unreadable). Quoted strings are blanked first; `merge-base`, `stash list/show` and `clean -n/--dry-run` are read-only and pass. A `git commit` also reports the soft hooks the session overrode |
| H15 | ⏭     | PreToolUse            | `Write`                 | ~~On `~/.claude/plans/` writes, advise if "Operating principles" section is missing~~ — skipped (high FP on non-proof plans; marker regex fragile; plan template is the better forcing function) |
| H16 | ✅     | PostToolUse           | `mcp__hol4__hol_state_at\|mcp__hol4__hol_send\|mcp__hol4__hol_check_proof` | Inject advisory when goal display contains `⅋ᵣ` / `resconj` — the canonical indicator that multiple subgoals were bundled into one Resume body via a shared `suspend` label (hol4-proving skill "one label = one goal" violation) |
| H17 | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Block newly-authored non-canonical `suspend` in `*Script.sml` edits: THEN-form (`>>` / `\\` / `THEN` then `suspend "..."`) and the `by (suspend "...")` justification form — must be `>-` (THEN1) per "one label = one goal" (edit-time guard for the runtime failure H16 detects) |
| H18 | ✅     | PreToolUse            | `mcp__hol4__hol_send\|Edit\|Write\|MultiEdit` | Block the `markerLib` suspension-lookup query (the `(string*thm) option` one — returns NONE in a bare session, tempts guessing the suspended goal); point to `set_suspended_goal` to actually load it |
| H19 | ⏭     | PreToolUse            | `mcp__hol4__hol_restart` | ~~Advise (never block) on `hol_restart` without the user asking~~ — superseded by H29 (repeat-keyed block covering `hol_stop` + `hol_restart`); file and wiring removed |
| H20 | ✅     | PreToolUse            | `mcp__hol4__hol_send`   | Block sending a massive tactic chain through `hol_send` (≥6 THEN-combinators, or ≥8 non-blank lines with ≥2 combinators) — RULE I: flush to the file, jump with `hol_state_at`; small probes pass |
| H22 | ✅     | SessionStart          | (all sessions)          | In HOL4 directories (Holmakefile/.holpath in cwd or ≤3 ancestors, or `*Script.sml` in cwd), inject a directive to load the `hol4-proving` skill before any proof work. In any directory, name hook-wiring drift (`install_hooks.drift`: scripts here not in settings.json, or wired but absent) |
| H23 | ✅     | PreToolUse            | `mcp__hol4__hol_send`   | Block the standalone-`prove` workflow in `hol_send` (`prove(` / `store_thm(` / `save_thm(` / `TAC_PROOF(`) — RULE I + RULE G: a proof closed in the scratch session with a hand-typed goal proves nothing about the file form; write a `Theorem … QED` or sub-suspend the arm (`>- suspend` + `Resume`) |
| H24 | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Advise (never block) on newly-defined tactic abbreviations (`val foo_tac = …` / `fun foo_tac … = …`) in `*Script.sml` — lifting a tactic needs a strong stated justification; defaults are lift a LEMMA or leave the duplication. Diff-aware on binding names; `*Lib.sml`/`*Syntax.sml` out of scope by the path test |
| H25 | ✅     | PostToolUse           | `mcp__hol4__hol_check_proof\|mcp__hol4__hol_state_at\|mcp__hol4__holmake` | Sweep finished proof text for composition defects (adjacent normalisers, `impl_tac` sandwich, `>-` not marking a sibling, near-identical sibling arms, nested splitter ladders, n-ary tactic forms, self-feeding lambdas). Fires per theorem on `hol_check_proof` → `Status: OK`; counts-only backstop on `holmake` for git-modified scripts. Advisory; checks live in `proof_sweep.py` |
| H26 | ✅     | —                     | —                      | **Implemented inside H6**, not as its own hook: it fires on the same event with the same payload, so a separate hook would mean two messages on one failure. See "The symptom table" under H6 |
| H27 | ✅     | PreToolUse            | `Bash`                  | HARD. Audit the `*Script.sml` content a `git commit` would record (index blobs, or the selected worktree files for `-a`/`--only`/`--include`; `--amend` against HEAD), never mutating the index. Blocks newly introduced findings — Gates 1/2/3/5 on added lines plus `proof_sweep` per touched theorem, minus the lone-`>-` and trailing-`>-` prompts (H25's advisories) — not inherited debt, including a finding that stood on a line the commit merely retouched; a deleted `Finalise` counts. In a repository that tracks `*Script.sml`, a command form it cannot model (compound, substitution, shell wrapper, unknown option) is refused with the reason; elsewhere every form passes. Override with `wip ok` |
| H28 | ✅     | PreToolUse            | `Bash`                  | SOFT. Block shell invocations of `Holmake` / raw `poly`\|`hol` once, redirecting to `mcp__hol4__holmake` / `hol_start` (`detach=True` for long builds); an identical retry passes with an override note. Command-position match only, after quoted strings and heredoc bodies are blanked (`hook_payload.visible_command`), so prose, log paths, grep patterns, `hol=...` assignments and `--help`/`-v` queries pass. Pre-grant: `shell holmake ok` |
| H29 | ✅     | PreToolUse            | `mcp__hol4__hol_stop\|mcp__hol4__hol_restart` | SOFT. Block a REPEAT `hol_stop`/`hol_restart` within 30 min while the cached working file (H25's `hol4_file`) is still in the same directory once — the ritual-stop signature; stop/restart is never part of the edit-check loop (`hol_state_at` auto-detects edits, reloads after an ancestor rebuild and moves the session across workdirs itself; every stop costs a cold prefix reload). First stop, any stop once the working file is in another directory, and a stop within 10 min of a budget TIMEOUT (recorded by H6) pass; an identical retry passes with an override note. Pre-grant: `restart ok` |
| H30 | ✅     | PreToolUse            | `mcp__hol4__hol_state_at\|hol_goals\|hol_check_proof\|hol_send\|hol_start` | Block HOL navigation of a file whose ANCESTOR theories are stale — script newer than its built artifacts, artifacts missing (mid-rebuild), or built before their own ancestors' artifacts. Forecloses "edited upstream, kept working downstream": sessions and fresh loads read the built `.dat`, so downstream checks silently run against the pre-edit upstream with no native symptom. Make-style check over the `Ancestors`/`open` closure (comment-stripped, duplicate names resolved nearest-first, mtime-memoized under `~/.claude/hook-state/h30/`); self-clears on rebuild; target file itself exempt; also keeps H25's `hol4_file` cache current for `hol_goals`/`hol_start`. SOFT: a given (file, stale set) is blocked once with rebuild commands from each ancestor's own directory; an identical retry passes with an override note; a newly stale theory blocks again. Pre-grant: `stale ok` |
| H31 | ✅     | PreToolUse            | `mcp__hol4__hol_state_at\|mcp__hol4__hol_goals` | SOFT. Block `skip_prefix: true` once per file with the RULE K caveat (prefix-skip binds every earlier theorem by `cheat`); an identical retry passes with an override note and is logged. `false`/absent never fires. Pre-grant: `skip prefix ok` |
| H32 | ✅     | PreToolUse            | `mcp__hol4__holmake`    | SOFT. Build ownership (RULE A): block a `holmake` with no `target` (whole-directory build) once per workdir; an identical retry passes with an override note. Targeted builds always pass — rebuilding stale ancestors in other directories is what H30 asks for. Pre-grant: `build ok` |
| H33 | ✅     | PreToolUse            | `Bash`                  | SOFT. Block a self-defeating background waiter once — `pgrep -f` with no bracket-escape or `-x` (it matches its own command line, so the loop never ends), an `until`/`while … do … sleep` poll loop, or `sleep N` followed by a log read — redirecting to one read of the job's log, to `hol_build_status(job, wait=…)` for a detached MCP build, or to backgrounding the command itself; an identical retry passes with an override note. Matched on the raw command (these loops sit inside `bash -c '…'`). General shell policy, not HOL4: Claude-only like H14. Pre-grant: `waiter ok` |

Skipped: H2, H3, H5, H9, H11, H12, H13, H15. H21 (holmake-on-cheated-theory
blocker) was proposed and rejected. H4 is the only live proposal.

The live wiring is `~/.claude/settings.json`; `install_hooks.py --check`
reports any drift between it and the scripts in this directory.

## H1 — banned-tactics scanner

**File**: `h1_banned_tactics.py`
**Event**: `PreToolUse`
**Matcher**: `Edit|Write|MultiEdit`
**Effect**: blocks the tool call (exit 2) if the new content of a `*Script.sml`
file contains any banned HOL4 tactic that did not appear in the pre-edit
content. Library SML files (`*Lib.sml`, `*Syntax.sml`, `Tactical.sml`, `Q.sml`,
etc.) are exempt — they legitimately define `TRY` / `ORELSE` as identifiers.

### What counts as banned

From the `hol4-proving` skill (`HOL4 — banned tactics` section; formerly in `~/.claude/CLAUDE.md`):

- `TRY` — hides failure.
- `ORELSE` — hides failure.
- `FIRST` — hides failure.
- `THENL` and its operator form `>|` — position-keyed brittleness.

### How it decides

1. Reads PreToolUse JSON on stdin (fields: `tool_name`, `tool_input`).
2. Skips if `tool_name` is not in `{Edit, Write, MultiEdit}` or `file_path`
   does not end `Script.sml`.
3. Computes pre-edit and post-edit content per tool:
   - `Edit` → `old_string` vs `new_string`.
   - `Write` → existing file content (read from disk) vs `content`.
   - `MultiEdit` → concatenated `old_string`s vs concatenated `new_string`s.
4. Strips `(* ... *)` comments and `"..."` string literals (non-nested),
   then counts each banned-tactic regex in both sides.
5. Exits 2 + stderr if any banned tactic's post-edit count exceeds its
   pre-edit count. Otherwise exits 0.

The diff-based check means a pre-existing `TRY` carried verbatim through an
edit does NOT trigger the hook — only **newly introduced** occurrences do.
This mirrors Gate 5 in the skill, which tolerates pre-existing uses until the
theorem is restructured and treats anything you authored or copied this
session inside a discharged region as a violation.

### Bypass

The hook intentionally has no env-var override (an env set at Claude Code
launch is not a useful per-edit escape hatch). To bypass, comment out the H1
entry in `~/.claude/settings.json`:

```json
{
  "hooks": {
    "PreToolUse": [
      // { ... H1 entry ... }
    ]
  }
}
```

…and restart Claude Code (or re-source settings if the version supports
hot-reload).

### Limitations

- Comment / string stripping is non-nested. `(* (* TRY *) *)` would incorrectly
  leave the inner `TRY` visible after one strip pass. This is acceptable
  because nested comments are vanishingly rare in this codebase.
- `Write` reads pre-existing content from disk. If the file is being created
  for the first time, pre-edit content is treated as empty (correct).
- Matches the HOL4 proof-script suffix `Script.sml`. If you ever hand-edit a
  HOL4 internal proof script (e.g. under `~/research/HOL/src/.../*Script.sml`)
  where `TRY` is used as an SML identifier rather than a banned tactic, the
  hook will still fire — comment it out in settings.json for that session.

## H6 — post-`hol_check_proof` failure reminder + symptom hint

**File**: `h6_check_proof_failure.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__hol_check_proof`
**Effect**: never blocks. On a failed check or navigation, injects — when the
failing tactic matches the symptom table — the corpus fact that explains that
symptom, and from the SECOND consecutive failure on the same theorem the RULE C
reminder as well. A first failure with no matching row is silent. State:
`~/.claude/hook-state/<session_id>/h6_failures.json` (theorem, count); a pass
on that theorem or a failure on another one resets it.

### What triggers it

A failure signature in the tool result: `TIMEOUT after Ns`, `Status: FAILED`,
`Status: INCOMPLETE`, `Status: ERROR`, `<-- FAILED`, `Tactic execution failed`,
`PROOF BROKEN`. Miss → silent exit 0.

`Status: CHEAT (not verified)` is intentionally **not** a trigger — reaching a
parked `cheat` is the expected result of the cheat-the-frontier pattern
(hol4-proving skill RULE I), not a failure.

Exact wording of the reminder lives in the hook (`REMINDER`); it is not
duplicated here, so the two cannot drift.

### The symptom table

The corpus already contains the facts that would prevent the most expensive
debugging detours — and they still do not reach the point of use. Two
structural reasons, neither fixable by wording: **volume vs recall** (dense
facts read at session start are not available at hour six), and **indexed by
cause, searched by symptom** (sections are named for causes; at the moment of
failure the cause is the ANSWER, not the question). H6 already fires at the
right moment and already has the failing tactic in its payload.

| failing tactic | failure shape | injected hint |
|---|---|---|
| `qpat_x_assum` / `qpat_assum` / `rename1` / `qmatch_*` | raised | pattern no longer matches: a prover-generated name that got re-rolled, or a tyvar mismatch that prints identically |
| `drule*` / `irule*` / `match_mp_tac` / `mp_then` | raised | free tyvar in the lemma's OWN statement; or the constant is `[simp]`-tagged and no longer an atom; or the assumption is not yet in the lemma's shape |
| `simp` / `simp_tac` / `asm_simp_tac` / `srw_tac` | left goals | `simp` uses assumptions as they stand; `fs`/`gvs`/`rw` simplify them first — and split a disjunctive assumption |

Three more rows key on the server's own diagnostic line instead of a tactic,
and fire whether or not the call counted as a failure:

| output line | injected hint |
|---|---|
| `NOTE: target line N is INSIDE step k` | the goal shown is the step's entry; the sub-suspend recipe with its `Resume thm[X]: cheat QED` terminator |
| `TIMEOUT: state_at exceeded ... prefix=Ps, target=Ts` | how to read the split: target nonzero → your tactic; "never ran" → the prefix, build the ancestors |
| `No such label` | header label unquoted first, then the dispatcher's own QED and the "Ancestor chain" line |

**Calibration.** The hint fires only when all of these hold, because a hint
that is wrong at the moment of failure is worse than silence — it is read when
trust is highest:

- the failing step is **short** (≤200 chars) — a token buried in a lumped
  opaque arm is not evidence about that arm, and the server already tells you
  to sub-suspend those;
- the matched tactic is the step's **first** one — a tactic after a combinator
  may never have run;
- the **failure shape matches the row**. `raised` rows need a HOL_ERR /
  exception signature, so a matcher that ran fine and merely left goals gets
  nothing. The `simp` row needs the opposite: goals left, no exception. No row
  matches a TIMEOUT — the server already prints a looping-tactic advisory
  there, and a second opinion on top of it is noise.

Rows deliberately exclude `fs`/`gvs`/`rw`: for those the simp hint is not just
unhelpful but false. `srw_tac` counts as `rw` and is excluded with it — in
`bossLib`, `srw_tac` is `BasicProvers.srw_tac` and `rw` is `PRIM_SRW_TAC`,
the same family.

### Limitations / known unknowns

- The PostToolUse JSON schema for MCP tool results is not canonical across
  Claude Code versions. `hook_payload.output_text` scans several plausible
  field names and collects every string leaf. If a future version uses a name
  outside that list the trigger silently doesn't fire — failing open is the
  right default.
- The repeat count is per session and per theorem name; a failure whose
  output carries no `Theorem:` line is keyed on the tool's `theorem` argument.
- The hint is keyed on the failing tactic alone. It cannot see the goal, so
  it is a checklist to run, not a verdict; it says so.

## H8 — `hol_state_at` replay-cost nudge

**File**: `h8_state_at_replay_cost.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__hol_state_at`
**Effect**: never blocks. On a `hol_state_at` call whose `replay` time crossed
30s, injects a system reminder framed for the *repeated-use* anti-pattern from
the hol4-proving skill cost-discipline trigger.

### What triggers it

The hook parses the trailing `[Timing: total=Nms, replay=Mms, startup=Sms, method=...]`
line emitted by hol4-mcp's `hol_state_at`. If `replay >= 30000ms` (30s) and
the call did real replay (not a cache hit), inject. Otherwise silent.

Skips (silent exit 0):
- Missing `[Timing:` line → error path; no replay happened.
- `replayed=0/N` in the cache-state diagnostics → cache hit; replay
  didn't run despite the timing field.
- `replay < 30000ms` → under threshold.
- `tool_name` not `mcp__hol4__hol_state_at`.

### What the reminder says

Points at the two cheap alternatives — sub-suspend the frontier, or `hol_send`
SMALL probes at the already-parked frontier — and explicitly acknowledges that
a single slow call may be legitimate (first touch, cold cache), so it reads as
conditional advice rather than a per-call accusation. Exact wording lives in
the hook (`REMINDER_TEMPLATE`).

### Threshold rationale

30s matches the skill's cost-discipline trigger text verbatim. `replay` is
used in preference to `total` because hol_send / sub-suspend address replay
overhead specifically; if `total` were dominated by file load (`replay` low),
neither tactic would help and the nudge would be misleading.

### Limitations

- Single-call decision. A genuinely cold-cache first call on a large file
  triggers the reminder once; the wording is calibrated for this, but the
  reminder still appears. If this proves noisy, escalate to a stateful
  variant that requires two consecutive slow calls.
- Output-format dependent: relies on hol4-mcp's `[Timing: ... replay=Nms]`
  format. A future hol4-mcp change to this format would silently disable the
  hook (fails open — no false blocks).

## H7 — holmake iteration-discipline reminder

**File**: `h7_holmake_advisory.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__holmake`
**Effect**: never blocks. Injects a RULE A reminder via `additionalContext`
only when the call fits the edit-then-rebuild loop: the same (workdir, target)
was built within the last 30 minutes AND the named target's authored proof
blocks changed. The first build, unchanged proofs, assertion-only scripts,
top-level translation edits and changes to unrelated scripts are silent. A
changed proof revision that has since completed `hol_state_at` at its QED or a
clean `hol_check_proof` is also silent; every changed block must have such a
validation before the next build.

State: `~/.claude/hook-state/<session_id>/h7_builds.json`, a timestamp and proof fingerprints per
(workdir, target), plus exact successful proof revisions recorded by H25 in
`h7_validations.json`. The reminder names the interval and says what to do
with the edit instead (hol_state_at, hol_check_proof; rebuild once at the end).

## H10 — Resume-needs-Finalise reminder

**File**: `h10_resume_needs_finalise.py`
**Event**: `PreToolUse`
**Matcher**: `Edit|Write|MultiEdit`
**Effect**: never blocks. When an Edit/Write/MultiEdit on a `Script.sml`
file introduces a new Resume theorem whose `Finalise <thm>;` line is not in
the post-edit content, injects a one-line `additionalContext` reminder.

### Diff-aware on theorem NAMES

The hook computes pre-edit and post-edit content (reads the file from disk,
applies the edit virtually) and fires only when a Resume theorem name is
**newly added** in this edit (`post_names - pre_names`). Consequences:

- Adding `Resume foo[A]` to a file that has no other Resume foo: fires if
  no `Finalise foo;` present.
- Adding a **sub-Resume** `Resume foo[A_subarm]` to a file that already has
  `Resume foo[A]:` and `Finalise foo;`: silent. The theorem name `foo` is
  not newly introduced; sub-suspending is a normal mid-discharge operation.
- Re-editing an existing Resume body (no new Resume header): silent.

### Reminder content

Names the theorem(s) missing a `Finalise` and cites Gate 2; separate wordings
for the one-theorem and several-theorem cases. Exact text lives in the hook.

## H14 — destructive git ops require `git ok` consent

**File**: `h14_git_destructive_consent.py`
**Event**: `PreToolUse`
**Matcher**: `Bash`
**Effect**: blocks (exit 2) destructive `git` invocations unless the literal
phrase `git ok` (case-insensitive) appears somewhere in the latest user
message in the session transcript.

### Destructive verb list

Matched after `git` **and any global options it carries** — `git -C dir commit`,
`git --no-pager push` and `git -c k=v commit` all reach the verb, so the
options are not a bypass:
`commit`, `push`, `stash`, `revert`, `reset`, `checkout`, `switch`, `restore`,
`clean`, `rm`, `mv`, `pull`, `merge`, `rebase`, `cherry-pick`, `apply`, `am`.

Plus: `git branch -D`, `git branch -d`, `git branch --delete`.

Read-only verbs (status, log, diff, show, grep, blame, fetch, ls-*, rev-*,
remote without -add/-rm, branch listing) are unmatched and pass through.

### What is not a destructive op

- A verb is matched as a whole token: `git merge-base` is not `git merge`.
- Read-only forms of destructive verbs: `git stash list`, `git stash show`,
  `git clean -n` / `--dry-run` (any short-flag cluster containing `n`).
- Text the shell would not execute: quoted strings and heredoc bodies are
  blanked before matching (`hook_payload.visible_command`), so a commit
  message or an `echo` mentioning `git checkout` passes. What the shell WOULD
  run inside a string is kept and still matched: `$(git stash)`, backticks,
  and the argument of `bash -c` / `eval`.

### Consent mechanism

The hook reads `transcript_path` from its PreToolUse payload (Claude Code
populates this with the path to the session transcript JSONL). It scans the
**latest user message** for `\bgit\s+ok\b` (case-insensitive). Present →
permit. Absent → block.

A user message is a turn the user typed. Claude Code also writes `role=user`
lines the user never typed — the compaction summary, request copies, skill
bodies, hook and goal echoes, task notifications, subagent hand-backs, slash-
command output — and these often quote consent phrases verbatim, so they are
skipped (`hook_payload._user_turn_text`). A slash command counts as a turn,
so it ends an earlier message's grant, but its arguments grant nothing. The
soft hooks' pre-grants read the same turns.

`git ok` is a one-shot grant tied to that specific message — it does not
persist across subsequent user messages. If you say `git ok` and I push;
your next message without `git ok` does NOT consent to another push. This is
the HARD shape, shared only with H27's `wip ok`; the soft hooks (H28–H33)
pre-grant from any earlier message and pass on a deliberate retry instead
(see *Soft hooks*).

### Fail-open conditions

The hook permits the call (exits 0) if:
- `transcript_path` is missing from the payload, or
- The transcript file doesn't exist or can't be read, or
- The transcript has no user message identifiable in any of the supported
  schema variants.

This avoids the hook blocking legitimate work due to a hook bug or schema
change.

### Limitations

- **`git checkout` granularity**: this hook blocks ALL `git checkout`,
  including benign branch switches like `git checkout main`. CLAUDE.md
  distinguishes destructive `checkout <file>` from harmless branch switches,
  but reliably detecting that with regex is fragile. Type `git ok` to grant
  branch switches when needed.
- **Consent FN**: a user message containing the word "git" *and* the word
  "ok" in unrelated contexts could falsely consent — but the regex
  `\bgit\s+ok\b` requires them adjacent, so the false-consent risk is low.
- **Token shadowing**: if your latest user message asks me to write the
  literal phrase "git ok" to a file, the hook still reads it as consent.
  Acceptable risk.

## H16 — bundled-subgoal (`resconj`) detector

**File**: `h16_bundled_suspend_goals.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__hol_state_at|mcp__hol4__hol_send|mcp__hol4__hol_check_proof`
**Effect**: never blocks. When the tool output contains the goal-display
marker `⅋ᵣ` (U+214B + U+1D63) or the constant name `resconj`, injects an
advisory `additionalContext` reminder.

### What triggers it

The HOL4 `proofManagerLib`-based `suspend` framework uses a binary constant
`resconj` to MERGE the residual goals of multiple suspended subgoals under
the SAME label into one combined goal at Resume time. Display rendering of
`resconj x y` is `x ⅋ᵣ y`. Either token in a goal display means goals were
bundled.

This is symptomatic of:
- A dispatcher that routes the same `suspend "Label"` to multiple arms
  (`>~ [pat_a] >- suspend "X" >~ [pat_b] >- suspend "X"` …). Each arm's
  residual gets tagged identically, and Resume sees them merged. This covers
  the alike-patterns case too: a single `>~ [pat] >- tac` arm runs on the
  FIRST match only, so bundling means two arms reached one label, not one arm
  firing twice.
- A `>>` (THEN) distributing across multiple residual goals before
  `suspend "Label"`, bundling them.

Bundled goals cannot be decomposed cleanly with standard HOL tactics —
the user must split the dispatcher into per-arm labels (one label = one
goal) so each Resume body sees a single goal.

### What the reminder says

Lists the three causes above and the fix — give each suspended arm its OWN
label and write one Resume body per label — and warns against attacking the
merged `resconj` goal directly. Exact text lives in the hook.

### Limitations

- Triggers on any goal display containing the marker. A legitimate proof
  artifact that intentionally references `resconj` (e.g. a meta-discussion
  via `term_to_string`) would also fire — acceptable, since there's no
  legitimate reason to ship code containing the symbol.
- Depends on `hook_payload.output_text` keeping strings raw: JSON-escaping the
  payload would hide the U+214B marker and silently disable the hook.

## H17 — non-canonical `suspend` blocker

**File**: `h17_then_suspend.py`
**Event**: `PreToolUse`
**Matcher**: `Edit|Write|MultiEdit`
**Effect**: blocks (exit 2) when a `*Script.sml` edit newly introduces
`suspend "..."` non-canonically — either after a THEN-form combinator (`>>`,
`\\`, or the word `THEN`), or as a `by` justification
(`` `P` by (suspend "X") `` / `` `P` by suspend "X" ``). For `Edit` and
`MultiEdit`, matching occurrences already present in the replaced text are
subtracted, so inherited debt cannot block an unrelated change. A `Write`
checks the complete new file.

### Why

`suspend "L"` is a single-goal tactic; THEN distributes its right operand across
ALL residual goals, tagging each with the same label. At Resume time those goals
are merged via `resconj` into one unprovable bundled goal — the runtime failure
H16 detects. The canonical form is THEN1 (`>-`) immediately before every
`suspend`. H17 catches the mistake at edit time so it never reaches live state.

### What counts

Regex `(?:>>(?!~)|\\\\|\bTHEN(?![1L_]))\s*suspend\s*"..."`:
- `>>` — negative lookahead excludes `>>~` / `>>~-` (different combinators).
- `\\` — CakeML preamble synonym for THEN.
- the word `THEN` — word-boundary; `THEN1` / `THENL` / `THEN_LT` excluded.

Plus regex `\bby\s*\(?\s*suspend\s*"..."` for the `by`-justification form
(`` `P` by (suspend "X") `` / `` `P` by suspend "X" ``) — a single-goal tactic
parked off-pattern instead of dispatched with `>-`. No legitimate `by ... suspend`
exists, so no false positives; the THEN regex never sees these (`suspend` is
preceded by `by`/`(`, not a THEN-form).

Both detect newly introduced occurrences anywhere in the replacement text,
including inside parens (`>- (... >> suspend "L")`).

### Correct forms (not blocked)

`>- suspend "L"` · `>- suspend "L1" >- suspend "L2"` ·
`tac1 >> tac2 >- suspend "L"` (THEN for the transforms, THEN1 only at the
boundary) · `>~ [pat] >- suspend "L"`.

## H18 — suspension-lookup ban

**File**: `h18_ban_lookup_suspension.py`
**Event**: `PreToolUse`
**Matcher**: `mcp__hol4__hol_send|Edit|Write|MultiEdit`
**Effect**: blocks (exit 2) if a `hol_send` command (or an Edit/Write/MultiEdit
body) contains the banned `markerLib` suspension-lookup token (regex
`\blookup_` + `suspension\b`).

### Why

That query is the wrong tool for inspecting a suspended goal. Its type is
`(string * thm) option`, and in a bare MCP session it returns NONE — the
suspension store is populated by file replay, not by a lone `hol_send`. A NONE
return tempts guessing the suspended goal's assumptions instead of reading them,
a RULE F / RULE D violation that has cost real session time.

### What it points to

To READ a suspended goal, LOAD it and inspect normally:

    markerLib.set_suspended_goal {suspension_name = "<thm>", label_name = "<label>"};
    val (asl,w) = proofManagerLib.top_goal();
    List.app (fn t => print (term_to_string t ^ "\n")) asl;

The parent Theorem must be processed up to its QED first — navigate
`hol_state_at` to the dispatcher's QED so the suspension is in the store. In a
script, write the body inside `Resume thm[Label]: ... QED` and navigate with
`hol_state_at`.

### Limitation

Fires on any occurrence of the banned token, including in a memory note or
comment about the ban itself (this README phrases around it for that reason).
Acceptable — the token has no legitimate use in committed proof work.

## H27 — audit gates at commit time

**File**: `h27_commit_audit_gate.py`
**Event**: `PreToolUse`
**Matcher**: `Bash`
**Effect**: blocks (exit 2) a `git commit` that would record proof code failing
the audit gates. Override: `wip ok` in the latest user message (alongside
`git ok`).

### Why

The skill's audit gates fire "when you feel done" — self-reported, so nothing
fires when the feeling doesn't arrive. Scaffolded proofs pass `hol_check_proof`
AND `holmake`, so no other signal catches them either. H25 reports composition
defects but is a PostToolUse advisory and cannot stop anything. This makes the
gates mechanical at the one moment that is unambiguous: proof code leaving your
hands.

### Diff-scoped

Only what the commit introduces is judged against HEAD. Ordinary commits use
index blobs; `-a` includes tracked worktree edits; `--only` and implicit path
commits use only selected worktree paths; `--include` overlays selected paths
on the index. `--amend` is compared with the current HEAD. Inherited sweep
findings are matched by source-line mapping and finding text, including inside
edited theorems and on a retouched line whose HEAD counterpart carried the same
finding. Newly introduced findings still block. `cheat`, banned
tactics and `Resume` count on ADDED code lines; deletion or misplacement of a
required `Finalise` is also detected. Findings are grouped per theorem.

The audit is read-only: it never modifies the index or runs Git content
filters. In a repository that tracks `*Script.sml`, a commit it cannot model —
a compound command (`git add … && git commit`, `… && git push`), a command
substitution, a shell wrapper (`bash -c`, `env`), an unrecognised global or
commit option, interactive selection, content filters — is refused with the
reason rather than audited against the wrong snapshot: stage separately and
use a plain index commit. A message piped from a heredoc
(`-m "$(cat <<'EOF' … EOF)"`) is accepted. Outside such a repository the audit
is vacuous and every commit form passes. Quoted paths and commit-message option
text are parsed as arguments, not flags.

### What it checks, and what it deliberately does not

Blocks on Gates 1, 2, 3, 5 and the `proof_sweep` composition checks, except
two dispatcher prompts that stay H25's post-check advisories and never block:
the lone `>-` ("the only dispatcher at its level"), whose fix (`>>`) changes
no proof, and the short trailing `>-` run, which a count cannot tell from
genuine sibling arms — a two- or three-constructor case split with one
`>- suspend` per arm is the sanctioned form, not a deferred main line.

**Gate 6 (single-use `[local]` helpers) is deliberately excluded.** Its keeper
case — a small, intent-documenting named fact — is the common and correct idiom,
and no mechanical test separates it from a one-shot nav-helper. Calibrating
against a reviewed script, the check fired on `clean_prog_CONS`,
`in_cc_eq_state_cc` and five siblings, all of which should stay. It remains a
judgement prompt in the skill's audit, where a human does the judging.

Gate 1 is kept only because size discriminates it: keeper (a) is a per-case
`Resume` ladder, so a theorem with a *short* run of Resume blocks reads as the
deferred tail the gate calls junk, while a long ladder is the sanctioned form
and passes silently.

### Calibration

The bar was "refuse the commit that needed a cleanup, pass the cleaned result",
measured on a real before/after pair: the pre-cleanup revision of a proof script
is refused with ~190 findings, the reviewed version that shipped passes clean.
Anything that fired on the shipped version was treated as a false positive and
removed or narrowed, not tolerated.

### Limitations

- A prospective commit it cannot determine is refused with the specific
  limitation, never audited as a different snapshot (see *Diff-scoped*); a
  repository with no tracked `*Script.sml` is never gated.
- Runs alongside H14, which gates the same commits on `git ok`. Two hooks on one
  call is intentional here: they answer different questions (may you commit at
  all, and is this code fit to commit).

## H31 — `skip_prefix=True` is a soft block

**File**: `h31_skip_prefix_consent.py`
**Event**: `PreToolUse`
**Matcher**: `mcp__hol4__hol_state_at|mcp__hol4__hol_goals`
**Effect**: soft block (see *Soft hooks*) on a call with `skip_prefix: true`,
keyed per file: the first use is refused with the RULE K caveat, an identical
retry passes with an override note and is logged, and `skip prefix ok`
anywhere in the session's user turns pre-grants. `false` or absent never
fires. Fail-open when the transcript is unreadable.

## H32 — holmake preflight: name the target

**File**: `h32_holmake_preflight.py`
**Event**: `PreToolUse`
**Matcher**: `mcp__hol4__holmake`
**Effect**: soft block on a `holmake` with no `target` — an untargeted
Holmake builds every theory in the directory, not the one being worked on
(RULE A, build ownership). Keyed per workdir; pre-grant `build ok`. A
targeted build always passes: when its stale ancestors live in other
directories, rebuilding them is exactly what H30 demands, so refusing it
would leave no way forward.

For builds longer than the synchronous budget the answer is
`holmake(detach=True)` + `hol_build_status`, never a shell `nohup Holmake`
(H28).

## H33 — background waiters: read the log instead

**File**: `h33_background_waiter.py`
**Event**: `PreToolUse`
**Matcher**: `Bash`
**Effect**: soft block on three Bash shapes that cannot do what they
promise: `pgrep -f <pat>` with neither a bracket-escape nor `-x` (the
waiter's own command line contains `<pat>`, so the condition never turns
false), an `until`/`while … do … sleep` poll loop, and `sleep N` followed by
a log reader (a timer whose delay has nothing to do with the state it
reports). Matched on the raw command rather than `visible_command`, since
these loops usually sit inside `bash -c '…'`. Keyed per normalised command;
pre-grant `waiter ok`.

A detached job that writes a log needs no waiter: its state is one read of
that log, and a waiter's notification can only arrive between turns — when
the log would have been read anyway. A detached MCP build is waited on with
`hol_build_status(job, wait=100)`: one call blocks up to 100 s and shows the
building theory's log tail. To wait on anything else, background the
command itself (Bash `run_in_background`) so the harness reports its exit.
Rule source: global `~/.claude/CLAUDE.md` (every background job is
time-limited; one mechanism per question). This is general shell policy,
not HOL4 policy, so like H14 it is Claude-only and absent from the Codex
`hooks.json`.

## Soft hooks — block once, pass on a deliberate retry

H28, H29, H30, H31, H32 and H33 guard situations the hook cannot judge but the
agent must not miss. They share one protocol (`hook_payload.soft_block`):

1. The first occurrence of a situation (a per-hook fingerprint: the command,
   the directory, the file plus its stale set, …) is blocked with the full
   message, ending with: repeat the call unchanged if, having read this, you
   still judge it right.
2. An identical retry within 30 minutes passes, with a prominent
   `⚠ Hnn OVERRIDDEN by repeat: …` line in the model's context (and as a
   `systemMessage`), and the override is logged under
   `~/.claude/hook-state/<session_id>/soft_blocks.json`.
3. A changed situation (another file, a newly stale theory, a different
   command) is a new fingerprint and blocks once again.
4. A consent phrase (`shell holmake ok`, `restart ok`, `stale ok`,
   `skip prefix ok`, `build ok`, `waiter ok`) in ANY user turn of the session pre-grants;
   the call passes with a `pre-granted` note. No soft-block message tells the
   agent to ask the user for a phrase — they are the user's to volunteer.
5. The next `git commit` (H14) reports the session's overrides, so the
   decisions surface where the work is recorded.

The hard hooks are unchanged: H14 (`git ok`) and H27 (`wip ok`) read the
latest user message only and never pass on a retry; H1, H17, H20 and H23
block a wrong tactic form outright, with no override.

## Installing the full suite

The scripts in this directory are dormant until wired into Claude Code's
`~/.claude/settings.json`. Schema reference:
<https://docs.claude.com/en/docs/claude-code/settings#hooks>.

### Installing (one command)

```bash
~/hol4-mcp/hooks/install_hooks.py          # merge every hook into settings.json
~/hol4-mcp/hooks/install_hooks.py --check  # report drift, write nothing (exit 1 if any)
~/hol4-mcp/hooks/install_hooks.py --print  # emit the JSON block for a manual merge
```

`install_hooks.py` discovers every `h<N>_<name>.py` beside it and reads the
registration each hook declares at module level:

```python
HOOK_EVENT   = "PreToolUse"               # or PostToolUse, SessionStart, ...
HOOK_MATCHER = "Edit|Write|MultiEdit"     # or None = all calls for this event
```

**Adding a hook file is therefore the only step needed to install it** — there
is no list here to keep in sync, and a hook that omits `HOOK_EVENT` is an error
rather than a silent omission. Declarations are read statically (`ast`), never
imported, so a broken hook cannot execute during install.

Merging is idempotent and additive: entries already pointing at a hook are left
alone, entries for scripts outside this directory are never touched, and a
timestamped backup of `settings.json` is written before any change. Backups
accumulate one per change — sweep them occasionally with
`rm ~/.claude/settings.json.bak.*`. Merging by hand also works — JSON has no
multiple `hooks` keys, and a trailing comma makes the whole block vanish with
no warning.


### Manual / single-hook wiring

To install a subset, drop the desired script (`chmod +x` already if cloned),
and add only its entry under the matching event. Per-hook
matchers and event placement are in the Suite map table near the top of
this document.

### Hot-reload

`settings.json` reloads on the next tool call — no Claude Code restart
required. If a hook silently stops firing after an edit, the JSON is
malformed (typically a trailing comma); fix and retry.

### Quick sanity check

```bash
# Confirm each script is executable and parses
for f in ~/hol4-mcp/hooks/*.py; do
  python3 -c "import ast; ast.parse(open('$f').read())" && echo "ok: $f"
done

# Confirm settings.json is valid JSON
python3 -c "import json; json.load(open('$HOME/.claude/settings.json'))" \
  && echo "settings.json ok"

# Confirm every hook here is wired and no wired hook has vanished
~/hol4-mcp/hooks/install_hooks.py --check

# Confirm the guidance these hooks cite still resolves (links, §sections,
# paths, H-numbers) — a hook message naming a renamed section is a dead
# reference the model reads at the worst possible moment
~/hol4-mcp/skills/hol4-proving/corpus_check.py
```

### Disabling

Remove or rename the `hooks` key in `~/.claude/settings.json` (e.g.
`hooks` → `hooks_disabled`). To disable one hook, delete its entry.

## Stdin / stdout / exit-code contract

Reference: <https://docs.claude.com/en/docs/claude-code/hooks>.

- **stdin**: JSON payload. PreToolUse includes `tool_name`, `tool_input`,
  `session_id`, `cwd`, `hook_event_name`. PostToolUse additionally includes
  the tool result.
- **exit 0**: action proceeds.
- **exit 2 + stderr**: action is blocked; stderr surfaced to the model as
  tool error.
- **JSON on stdout** (exit 0) can inject `hookSpecificOutput.additionalContext`
  to add context visible to the model.
- Hook should be fast. A per-entry `timeout` may be set in settings.json;
  none of these hooks does, so all run under Claude Code's default. Every hook
  here returns in well under a second, so the default is not a constraint.

## Shared modules

Two files here are **not** hooks — `install_hooks.py` discovers only
`h<N>_<name>.py`, so a plain name is never wired by accident:

- `hook_payload.py` — `output_text(payload)` (a PostToolUse result flattened to
  searchable text, strings kept raw), `latest_user_message(payload)` (newest
  turn the user typed, for the consent-gated hooks) and `visible_command(command)`
  (a Bash command with quoted strings and heredoc bodies blanked, keeping the
  substitutions and `-c`/`eval` arguments the shell would still run — what
  H14 and H28 match against), plus the soft-hook protocol: `granted` /
  `pregranted` (a phrase in any user turn), `soft_block` (block once, pass an
  identical retry with a note, log it), `overrides_summary` (the tally H14
  prints at a commit). Every hook that reads a payload uses these;
  reimplementing one is how the copies drift apart.
- `proof_sweep.py` — the composition checks H25 runs, also usable standalone:
  `./proof_sweep.py FILE [FIRST_LINE LAST_LINE]`.

## Per-session state

H25 caches the last file any hol4 call named under
`~/.claude/hook-state/<session_id>/`, keyed by the `session_id` field on the
hook input — `hol_check_proof` is usually called without `file=`, so without
the cache the sweep has nothing to read. Every other hook is stateless.
Cleanup: weekly `find ~/.claude/hook-state -mtime +7 -delete`.

## See also

- `../skills/hol4-proving/SKILL.md` (+ its `notes/`) — the HOL4 proof-interaction rules these hooks enforce; exposed globally via the `~/.claude/skills/hol4-proving` symlink.
- `~/.claude/CLAUDE.md` — generic behavioural rules (editing/git — H14's source — memory-writing, working principles).
- `~/hol4-mcp/LOCAL_CHANGES.md` — local divergences of the running MCP server.
