#!/usr/bin/env python3
"""
H14 -- PreToolUse hook blocking destructive git ops in Bash tool calls
without explicit `git ok` consent in the latest user message.

Reads PreToolUse JSON on stdin. If the tool is Bash and the command contains
a destructive git verb, the hook reads `transcript_path` from the payload
and inspects the latest user message for the literal phrase `git ok`
(case-insensitive). If absent -> exit 2; the tool call is blocked.

Destructive verbs, matched after `git` and any global options it carries
(`git -C dir commit`, `git --no-pager push`, `git -c k=v commit`):
  commit, push, stash, revert, reset, checkout, switch, restore, clean,
  rm, mv, pull, merge, rebase, cherry-pick, apply, am
Plus: branch -D / -d / --delete

Read-only verbs (status, log, diff, show, grep, blame, fetch, ls-*, rev-*,
config when reading, remote when listing) are unmatched and pass through.

Fails open if transcript_path is missing or unreadable -- never blocks
legitimately-needed work due to a hook bug.

CLAUDE.md source: '⛔ Editing and git' section.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Bash"   # None = all calls for this event

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import (  # noqa: E402
    emit_context, latest_user_message, overrides_summary, visible_command,
)

# `git` takes global options BEFORE the verb (`git -C dir commit`,
# `git --no-pager push`, `git -c k=v commit`), so the verb is not always the
# next token. Options carrying a separate argument must be consumed with it,
# hence the ordered alternation.
_OPT = (r"(?:(?:-C|-c|--git-dir|--work-tree|--namespace|--exec-path)"
        r"(?:=\S+|\s+\S+)|--?[A-Za-z][\w-]*)\s+")
_VERBS = (r"commit|push|stash|revert|reset|checkout|switch|restore|clean"
          r"|rm|mv|pull|merge|rebase|cherry-pick|apply|am")

# `(?![\w-])`: `merge-base` is not `merge`. The rest of the simple command is
# captured so read-only subcommands of a destructive verb can be exempted.
DESTRUCTIVE_GIT_RE = re.compile(r"\bgit\s+(?:" + _OPT + r")*(" + _VERBS
                                + r")(?![\w-])([^|&;\n]*)")
BRANCH_DELETE_RE = re.compile(r"\bgit\s+(?:" + _OPT + r")*branch\s+(-D|-d|--delete)\b")

# Read-only forms of otherwise destructive verbs.
READ_ONLY = {
    "stash": lambda rest: re.match(r"\s+(list|show)(?![\w-])", rest) is not None,
    "clean": lambda rest: any(t == "--dry-run" or (t.startswith("-") and not
                              t.startswith("--") and "n" in t)
                              for t in rest.split()),
}

CONSENT_RE = re.compile(r"\bgit\s+ok\b", re.IGNORECASE)

def find_match(command):
    text = visible_command(command)
    for m in DESTRUCTIVE_GIT_RE.finditer(text):
        verb, rest = m.group(1), m.group(2)
        if verb in READ_ONLY and READ_ONLY[verb](rest):
            continue
        return f"git {verb}"
    m = BRANCH_DELETE_RE.search(text)
    if m:
        return f"git branch {m.group(1)}"
    return None

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "Bash":
        return 0
    cmd = payload.get("tool_input", {}).get("command", "")
    matched = find_match(cmd)
    if not matched:
        return 0
    latest = latest_user_message(payload)
    if latest is None:
        return 0  # fail-open
    tally = overrides_summary(payload) if matched == "git commit" else ""
    if CONSENT_RE.search(latest):
        if tally:
            # The soft hooks' overrides surface where the work gets recorded.
            emit_context(f"[H14: this session overrode soft hooks -- {tally}]")
        return 0
    # Block
    print(f"hol4-hook H14: refused destructive git op: {matched!r}", file=sys.stderr)
    if tally:
        print(f"(this session overrode soft hooks -- {tally})", file=sys.stderr)
    print("", file=sys.stderr)
    print("CLAUDE.md '⛔ Editing and git':", file=sys.stderr)
    print("  No git command that modifies working-tree or repo state runs", file=sys.stderr)
    print("  without an explicit, in-context user request for THAT command.", file=sys.stderr)
    print("", file=sys.stderr)
    print("Latest user message does not contain consent token `git ok`.", file=sys.stderr)
    print("To grant consent, include the literal phrase `git ok` somewhere in", file=sys.stderr)
    print("your next message.", file=sys.stderr)
    return 2

if __name__ == "__main__":
    sys.exit(main())
