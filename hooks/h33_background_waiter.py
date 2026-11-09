#!/usr/bin/env python3
"""
H33 -- PreToolUse hook blocking self-defeating background-waiter idioms in
Bash commands.

Reads PreToolUse JSON on stdin. Blocks three shapes:

  1. `pgrep -f <pat>` with no bracket-escape and no `-x`. The shell running
     the loop carries <pat> in its own command line, so pgrep matches itself
     and the condition never becomes false -- infinite from its first second.
  2. An `until`/`while` ... `do` ... loop containing `sleep`: a poll loop.
  3. `sleep N` followed by a log reader: a timer poll, whose delay is
     unrelated to the state it reports.

Matched against the RAW command, not `visible_command`: these loops are
normally written inside `bash -c '...'`, whose body quoting would otherwise
blank the whole construct.

Rationale: a detached job that writes a log needs no waiter. Its state is one
read of that log, and a waiter's completion notification can only arrive
between turns -- exactly when the log would have been read anyway. The waiter
adds a process to abandon and a second mechanism for one question. A detached
MCP build already has its blocking wait: `hol_build_status(job, wait=...)`.

Soft hook: the same command is blocked once, then an identical retry passes
with an override note and is logged (hook_payload.soft_block). The literal
phrase `waiter ok` anywhere in the session's user turns pre-grants. Fails
open if the transcript is missing or unreadable.

Rule source: `~/.claude/CLAUDE.md` (every background job must be
time-limited; one mechanism per question) and the mechanics in
`~/.claude/memory/feedback_background_shells.md`.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Bash"   # None = all calls for this event

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import granted, pregranted, soft_block  # noqa: E402

SLEEP_RE = re.compile(r"\bsleep\s+\d")
LOOP_RE = re.compile(r"\b(?:until|while)\b.*?\bdo\b", re.S)
PGREP_RE = re.compile(r"\bpgrep\b([^\n;|&)]*)")
READER_RE = re.compile(r"\b(?:grep|egrep|rg|tail|head|cat|awk|sed)\b")

CONSENT_RE = re.compile(r"\bwaiter\s+ok\b", re.IGNORECASE)


def pgrep_selfmatch(cmd):
    """`pgrep -f` whose pattern can match the waiter's own command line."""
    for m in PGREP_RE.finditer(cmd):
        args = m.group(1)
        if "-f" not in args:
            continue            # -f is what widens the match to the cmdline
        if "-x" in args:
            continue            # -x matches the executable, not the cmdline
        if "[" in args:
            continue            # bracket-escape breaks the self-match
        return True
    return False


def find_shape(cmd):
    if pgrep_selfmatch(cmd):
        return ("pgrep", "`pgrep -f` with no bracket-escape: it matches the "
                         "waiter's own command line, so it never exits")
    sleep = SLEEP_RE.search(cmd)
    if not sleep:
        return None
    if LOOP_RE.search(cmd):
        return ("loop", "an `until`/`while` ... `do` ... `sleep` poll loop")
    if READER_RE.search(cmd, sleep.end()):
        return ("timer", "`sleep N` then a log read: a timer poll, whose "
                         "delay is unrelated to the state it reports")
    return None


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "Bash":
        return 0
    cmd = payload.get("tool_input", {}).get("command", "")
    shape = find_shape(cmd)
    if not shape:
        return 0
    kind, why = shape
    consent = granted(payload, CONSENT_RE)
    if consent is None:
        return 0  # fail-open
    if pregranted(payload, "H33", CONSENT_RE, "waiter ok",
                  f"background waiter ({kind})"):
        return 0
    return soft_block(payload, "H33", " ".join(cmd.split()), [
        f"hol4-hook H33: refused a background waiter -- {why}.",
        "",
        "A detached job that writes a log needs no waiter: its state is one",
        "read of that log, and a waiter's notification can only arrive between",
        "turns -- exactly when the log would have been read anyway. Read the",
        "log when there is a reason to.",
        "",
        "A detached MCP build is waited on with hol_build_status(job, wait=100):",
        "one call blocks up to 100 s and shows the building theory's log tail.",
        "",
        "If the job is the thing you want to wait for, background the command",
        "ITSELF (Bash run_in_background) so the harness tracks it and reports",
        "its exit code; do not wrap a poller around a job already running.",
        "",
        "Mechanics: ~/.claude/memory/feedback_background_shells.md",
    ], f"background waiter ({kind}) launched despite the one-mechanism rule")


if __name__ == "__main__":
    sys.exit(main())
