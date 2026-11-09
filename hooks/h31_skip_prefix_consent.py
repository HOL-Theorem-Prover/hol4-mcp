#!/usr/bin/env python3
"""
H31 -- PreToolUse soft hook on `skip_prefix: true` for hol_state_at /
hol_goals.

RULE K: prefix-skip binds every theorem before the target by `cheat`, so the
goal shown rests on unverified statements. Soft hook: the first use on a
file is blocked with the caveat, an identical retry passes with an override
note and is logged (hook_payload.soft_block), and the literal phrase `skip
prefix ok` anywhere in the session's user turns pre-grants.

Fails open if the transcript is missing or unreadable. `skip_prefix: false`
or absent never fires.

Rule source: hol4-proving skill '⛔ RULE K'.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_state_at|mcp__hol4__hol_goals"

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import granted, pregranted, session_state_dir, soft_block  # noqa: E402

CONSENT_RE = re.compile(r"\bskip\s+prefix\s+ok\b", re.IGNORECASE)
TOOLS = ("mcp__hol4__hol_state_at", "mcp__hol4__hol_goals")


def working_file(payload):
    ti = payload.get("tool_input", {})
    if ti.get("file"):
        return str(ti["file"])
    try:
        with open(os.path.join(session_state_dir(payload), "hol4_file"),
                  encoding="utf-8") as fh:
            return fh.read().strip() or "<unknown file>"
    except OSError:
        return "<unknown file>"


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    if tool not in TOOLS:
        return 0
    if payload.get("tool_input", {}).get("skip_prefix") is not True:
        return 0
    consent = granted(payload, CONSENT_RE)
    if consent is None:
        return 0  # fail-open
    path = working_file(payload)
    if pregranted(payload, "H31", CONSENT_RE, "skip prefix ok",
                  f"prefix-skip on {os.path.basename(path)}; the goal rests on "
                  f"unverified prefix statements"):
        return 0
    short = tool.rsplit("__", 1)[-1]
    return soft_block(payload, "H31", path, [
        f"hol4-hook H31: refused {short}(skip_prefix=True) -- RULE K.",
        "",
        "skip_prefix binds every theorem BEFORE the target by `cheat`; the goal",
        "it shows rests on unverified statements and proves nothing on its own,",
        "and a green result under it must be re-confirmed without it. Navigate",
        "the real way: full replay, a sub-suspended arm, or the built ancestors",
        "(holmake).",
    ], f"prefix-skip on {os.path.basename(path)}; every goal shown rests on "
       f"unverified prefix statements and proves nothing until re-confirmed")


if __name__ == "__main__":
    sys.exit(main())
