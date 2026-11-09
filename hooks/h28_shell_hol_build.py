#!/usr/bin/env python3
"""
H28 -- PreToolUse hook blocking shell invocations of the HOL4 build/REPL
binaries, redirecting to the MCP tools that own those interactions.

Reads PreToolUse JSON on stdin. If the tool is Bash and the command invokes
`Holmake` (or a raw `poly`/`hol` REPL) in a command position, the call is
blocked with a pointer to the owning MCP tool.

Rationale: the MCP tool reports its own completion and returns the failing
log excerpt. A shell build needs a hand-rolled completion sentinel, and
Holmake's real failure lines (`Proof of ... failed`, `error in quse`) do not
match the obvious guesses -- so the poller hangs while the build is dead.

Matched in a command position only (start, or after | & ; ( && || newline),
so prose mentions and paths like .hol/logs/... pass through. Quoted strings
and heredoc bodies are blanked first (hook_payload.visible_command), so a
grep pattern or a Python line inside a heredoc is not a command either;
`name=...` is an assignment, and a lone `-v`/`--help` query is not a build
or a REPL.

Soft hook: the same command is blocked once, then an identical retry passes
with an override note and is logged (hook_payload.soft_block). The literal
phrase `shell holmake ok` anywhere in the session's user turns pre-grants.
Fails open if the transcript is missing or unreadable.

Rule source: hol4-proving skill '⛔ RULE A' (holmake is the file-build gate)
and the corpus layer table (MCP tools are the point of contact).
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Bash"   # None = all calls for this event

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import granted, pregranted, soft_block, visible_command  # noqa: E402

# A command position: string start, or after a shell separator. Prevents
# matching `grep Holmake log`, `--- holmake procs ---`, paths, and comments.
_CMD_POS = r"(?:^|[|&;(\n]|&&|\|\|)\s*"

# Optional env-var assignments and `nohup`/`time`/`env` wrappers.
_PREFIX = r"(?:(?:[A-Za-z_]\w*=\S*|nohup|time|env|command|exec)\s+)*"

# `(?![\w=])`: `hol=$(...)` assigns a variable, it does not run `hol`.
BUILD_RE = re.compile(_CMD_POS + _PREFIX + r"(Holmake)(?![\w=])")
REPL_RE = re.compile(_CMD_POS + _PREFIX + r"(poly|hol)(?![\w=])")

# `Holmake --help`, `poly -v`: the binary answers and exits, no build, no REPL.
QUERY_ONLY_RE = re.compile(r"\s+(?:-v|--version|-h|-help|--help)\s*(?:$|[|&;)\n])")

CONSENT_RE = re.compile(r"\bshell\s+holmake\s+ok\b", re.IGNORECASE)

REPLACEMENT = {
    "Holmake": "mcp__hol4__holmake (params: workdir, target, jobs, timeout)",
    "poly": "mcp__hol4__hol_start / hol_send",
    "hol": "mcp__hol4__hol_start / hol_send",
}


def find_match(command):
    text = visible_command(command)
    for rx in (BUILD_RE, REPL_RE):
        for m in rx.finditer(text):
            if not QUERY_ONLY_RE.match(text, m.end()):
                return m.group(1)
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
    consent = granted(payload, CONSENT_RE)
    if consent is None:
        return 0  # fail-open
    if pregranted(payload, "H28", CONSENT_RE, "shell holmake ok",
                  f"shell invocation of {matched!r}"):
        return 0
    return soft_block(payload, "H28", " ".join(cmd.split()), [
        f"hol4-hook H28: refused shell invocation of {matched!r}.",
        "",
        f"Use {REPLACEMENT[matched]} instead; a build longer than the synchronous",
        "budget is holmake(detach=True) + hol_build_status.",
        "",
        "The MCP tool reports its own completion and returns the failing log",
        "excerpt; a shell build needs a hand-rolled sentinel, and Holmake's",
        "failure lines do not match the obvious guesses -- the poller hangs",
        "while the build is already dead.",
    ], f"shell {matched} run outside the MCP tools; nothing reports on it")


if __name__ == "__main__":
    sys.exit(main())
