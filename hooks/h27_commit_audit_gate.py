#!/usr/bin/env python3
"""
H27 -- PreToolUse gate that runs the post-discharge audit against a `git commit`
touching `*Script.sml`, and blocks on what it finds.

The skill's audit gates fire "when you feel done" -- self-reported, so nothing
fires when the feeling doesn't arrive. Scaffolded proofs pass `hol_check_proof`
AND `holmake`, so no other signal catches them either. This moves the gate to a
mechanical moment: when proof code leaves your hands.

DIFF-SCOPED. Only what this commit introduces is judged:
  - unchanged inherited composition findings are matched against HEAD;
  - banned tactics and `cheat` count only on ADDED lines.
The proposed bytes come from the index, or the selected tracked worktree files
for -a/--only/--include. This hook never changes the real index.

Checks (skill audit gates 1, 2, 3, 5 + the composition sweep; Gate 6 is not
enforced, see below):
  Gate 1  a Resume block added -- name the (a)/(b) justification or inline it
  Gate 2  a theorem left with Resume but no Finalise
  Gate 3  `cheat` added
  Gate 5  banned tactics added
  sweep   proof_sweep.py over each touched theorem

Override: put `wip ok` in the message alongside `git ok`. Deliberate WIP commits
are legitimate; silently unenforceable gates are not.

Outside a repository that tracks `*Script.sml` the audit is vacuous and nothing
is refused. Inside one, an ambiguous prospective commit (a compound command, a
substitution, a shell wrapper, an unknown option) is refused with the reason,
never audited against the wrong content: stage separately and commit the index.
A message piped from a heredoc whose body the shell would not execute is fine.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Bash"   # None = all calls for this event

import difflib
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proof_sweep  # noqa: E402
from hook_payload import latest_user_message, visible_command  # noqa: E402
from h14_git_destructive_consent import find_match  # noqa: E402
from git_commit_snapshot import (  # noqa: E402
    snapshot, repo_hint, tracks_scripts, AuditUnavailable,
)

OVERRIDE_RE = re.compile(r"\bwip\s+ok\b", re.IGNORECASE)
# A commit message piped from a heredoc: `hook_payload.visible_command` has
# blanked the body, so only empty lines may remain between the tag line and
# its terminator -- anything else is text the shell would execute.
HEREDOC_MESSAGE_RE = re.compile(
    r"\$\(\s*cat\s+<<-?\s*['\"]?(\w+)['\"]?[ \t]*\n(?:[ \t]*\n)*[ \t]*\1[ \t]*\n\s*\)")

BANNED = [(re.compile(r"\bTRY\b"), "TRY"), (re.compile(r"\bORELSE\b"), "ORELSE"),
          (re.compile(r"\bFIRST\b"), "FIRST"), (re.compile(r"\bTHENL\b"), "THENL"),
          (re.compile(r">\|", ), ">|")]
BLOCK_START = re.compile(r"^(Theorem|Definition|Triviality|Resume)\s+([A-Za-z0-9_']+)")
BLOCK_END = re.compile(r"^(QED|End)\b")
MAX_SHOWN = 12
# Calibrated so a reviewed, cleaned proof script reports NOTHING. Gate 1 keeps a
# per-case Resume ladder, so only a short one reads as the deferred tail it calls
# junk; below this it is flagged, at or above it is the sanctioned form.
LADDER_MIN = 2
# Sweep findings that stay H25's post-check advisory and never block a commit:
# a lone `>-` is a style prompt whose fix (`>>`) changes no proof, and a short
# trailing `>-` run cannot be told from genuine sibling arms by counting them.
ADVISORY_ONLY = ("`>-` is the only dispatcher", "trailing `>-`:")

# Gate 6 (single-use `[local]` helpers) is deliberately NOT enforced here. Its
# keeper case — a small, intent-documenting named fact — is the common, correct
# idiom, and no mechanical test separates it from a one-shot nav-helper: on a
# reviewed script this check fired on `clean_prog_CONS`, `in_cc_eq_state_cc` and
# five siblings, all of which should stay. It remains a judgement prompt in the
# skill's audit, where a human is doing the judging.


def changed_lines(before, after):
    """Added lines, and each new line's counterpart in HEAD: unchanged lines
    exactly, the lines of a replaced block positionally — so a finding that
    already stood on a line this commit merely retouches (a renamed theorem
    in a rewrite list) is matched against the same finding in HEAD."""
    old, new = before.splitlines(), after.splitlines()
    added, counterpart = {}, {}
    for tag, a, b, c, d in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag == "equal":
            counterpart.update({j + 1: a + j - c + 1 for j in range(c, d)})
        elif tag in ("insert", "replace"):
            added.update({j + 1: new[j] for j in range(c, d)})
            if tag == "replace":
                counterpart.update({j + 1: a + j - c + 1 for j in range(c, min(d, c + b - a))})
    return added, counterpart


def blocks(text):
    """[(name, kind, first, body, last)] for every Theorem/Definition/Resume
    block; `body` is the first line of proof text (the line after `Proof`, or
    after a `Resume` header), so statement-only edits are not proof edits."""
    out, cur = [], None
    for i, line in enumerate(text.split("\n"), 1):
        m = BLOCK_START.match(line)
        if m and cur is None:
            cur = [m.group(2), m.group(1), i, i + 1 if m.group(1) == "Resume" else None]
        elif cur and cur[3] is None and re.match(r"^Proof\b", line):
            cur[3] = i + 1
        elif cur and BLOCK_END.match(line):
            out.append((cur[0], cur[1], cur[2], cur[3] or i, i))
            cur = None
    return out


def block_of(blks, ln):
    for name, _, first, _, last in blks:
        if first <= ln <= last:
            return name
    return None


def audit(before, text):
    added, counterpart = changed_lines(before, text)
    # Strip comments for token checks; keep line structure so numbers stay real.
    clean_lines = proof_sweep.clean(text).splitlines()
    bare = {n: clean_lines[n - 1] for n in added}
    found, blks = [], blocks(text)
    ladders = {}
    for line in text.split("\n"):
        m = re.match(r"^Resume\s+([A-Za-z0-9_']+)", line)
        if m:
            ladders[m.group(1)] = ladders.get(m.group(1), 0) + 1

    for n, t in sorted(bare.items()):
        for rx, name in BANNED:
            if rx.search(t):
                found.append((n, f"Gate 5: banned tactic `{name}` on an added line"))
        if re.search(r"\bcheat\b", t):
            found.append((n, "Gate 3: `cheat` added — a committed cheat blocks the "
                             "pipeline theorem via check_thm"))
        m = re.match(r"^Resume\s+([A-Za-z0-9_']+)", t.strip())
        # Gate 1 keeper (a) is a multi-case induction "or a similarly large
        # multi-arm split" kept as one Resume per case, so a LADDER is the
        # sanctioned form and only a small number of Resumes reads as the
        # "single deferred tail" the gate calls junk.
        if m and ladders.get(m.group(1), 0) <= LADDER_MIN:
            found.append((n, f"Gate 1: `{m.group(1)}` has {ladders.get(m.group(1), 0)} "
                             f"Resume block(s) — too few to be the per-case ladder of an "
                             f"induction, so this reads as a deferred tail. Inline it, or "
                             f"say why it is a keeper"))

    # Gate 2 also catches deleting/moving a previously valid Finalise, even
    # when this diff adds no lines. An inherited defect is not a new one.
    def unfinished(source):
        ends = {name: last for name, kind, _, _, last in blocks(source) if kind == "Resume"}
        for n, line in enumerate(proof_sweep.clean(source).splitlines(), 1):
            m = re.match(r"^Finalise\s+([A-Za-z0-9_']+)\s*;", line)
            if m and n > ends.get(m[1], n):
                ends.pop(m[1], None)
        return set(ends)

    for name in unfinished(text) - unfinished(before):
        found.append((0, f"Gate 2: `Resume {name}` present with no `Finalise "
                         f"{name};` after its last body — the theorem stays cheated"))

    # Compare semantic findings at their HEAD counterparts, not just their
    # counts. Also catch new adjacency created solely by deleting a line.
    inherited = set(proof_sweep.sweep(before))
    for ln, msg in proof_sweep.sweep(text):
        if not any(kind != "Definition" and body <= ln < last
                   for _, kind, _, body, last in blks):
            continue
        if ((counterpart.get(ln), msg) not in inherited
                and not msg.startswith(ADVISORY_ONLY)):
            found.append((ln, msg))
    return found


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "Bash":
        return 0
    command = payload.get("tool_input", {}).get("command", "")
    if not re.search(r"\bgit\b", command) or not re.search(r"\bcommit\b", command):
        return 0

    latest = latest_user_message(payload)
    if latest and OVERRIDE_RE.search(latest):
        return 0

    cwd = payload.get("cwd") or os.getcwd()
    if not tracks_scripts(repo_hint(command, cwd)):
        return 0                                   # nothing to audit: pass every form

    try:
        visible = HEREDOC_MESSAGE_RE.sub("", visible_command(command))
        if ("$(" in visible or "`" in visible) and find_match(command) == "git commit":
            raise AuditUnavailable("command substitutions can change the index; use a literal commit call")
        proposed = snapshot(command, cwd)
        if proposed is None and find_match(command) == "git commit":
            raise AuditUnavailable("shell-wrapped commit cannot be audited; use a plain commit call")
    except (AuditUnavailable, ValueError) as error:
        print(f"hol4-hook H27: cannot determine the proposed commit: {error}", file=sys.stderr)
        return 2
    if proposed is None:
        return 0
    _root, files = proposed

    findings = []                                  # [(file, theorem, line, msg)]
    for f, (before, after) in files.items():
        blks = blocks(after)
        findings += [(f, block_of(blks, ln), ln, msg) for ln, msg in audit(before, after)]
    if not findings:
        return 0

    print(f"hol4-hook H27: refused the commit — the audit gates flag "
          f"{len(findings)} thing(s) in the proof code it would record.",
          file=sys.stderr)
    shown, group = 0, None
    for f, thm, ln, msg in sorted(findings, key=lambda x: (x[0], x[1] or "", x[2])):
        if shown == MAX_SHOWN:
            print(f"  ... and {len(findings) - MAX_SHOWN} more", file=sys.stderr)
            break
        if (f, thm) != group:
            group = (f, thm)
            print("", file=sys.stderr)
            print(f"  {f}" + (f" — {thm}" if thm else ""), file=sys.stderr)
        print(f"    {'line ' + str(ln) + ': ' if ln else ''}{msg}", file=sys.stderr)
        shown += 1
    print("", file=sys.stderr)
    print("Only newly introduced findings in the proposed commit were judged. Each sweep item is a "
          "PROMPT TO CHECK, not a proven defect — simplification is not "
          "confluent, so verify per theorem before collapsing anything.",
          file=sys.stderr)
    print("If this is a deliberate work-in-progress commit, say `wip ok` "
          "(alongside `git ok`).", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
