#!/usr/bin/env python3
"""
H18 -- PreToolUse hook on mcp__hol4__hol_send (and Edit/Write/MultiEdit) that
bans `markerLib.lookup_suspension`.

Rationale: `lookup_suspension` is the WRONG tool for inspecting a suspended
goal. Its type is `(string * thm) option`; in a bare MCP session it returns
NONE (the suspension store is populated by file replay, not by a lone
`hol_send`), which tempts you to GUESS the suspended goal's assumptions
instead of reading them -- a RULE F / RULE D violation that has cost real
session time.

To READ a suspended goal, PREFER `hol_state_at`: navigate to a line inside the
`Resume thm[Label]: ... QED` body (or to the dispatcher's QED first). That
replays the FULL prefix in file order, so the goal shown is exactly the one
Holmake sees -- an accurate, file-faithful state. Only if you must inspect
interactively (e.g. a quick assumption read) fall back to loading it:

    markerLib.set_suspended_goal {suspension_name = "<thm>", label_name = "<label>"};
    val (asl,w) = proofManagerLib.top_goal();
    List.app (fn t => print (term_to_string t ^ "\\n")) asl;   (* the real assumptions *)

(The parent Theorem must be processed up to its QED so the suspension is in
the store -- `hol_state_at` to the dispatcher's QED first.)

Block fires on any occurrence of `lookup_suspension` in the hol_send command
(or in Edit/Write/MultiEdit new content). Stateless.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_send|Edit|Write|MultiEdit"   # None = all calls for this event

import json
import re
import sys

BAD_RE = re.compile(r'\blookup_suspension\b')

REMINDER = """\
hol4-hook H18: refused -- `lookup_suspension` is BANNED.

It is the WRONG tool for reading a suspended goal: type
`(string * thm) option`, and in a bare session it returns NONE (the
suspension store is filled by file replay, not a lone hol_send). Using it
tempts you to GUESS the suspended goal's assumptions instead of reading
them -- a RULE F / RULE D violation.

To READ a suspended goal, PREFER `hol_state_at`: navigate to a line inside
the `Resume thm[Label]: ... QED` body (it replays the full prefix in file
order, so the goal is exactly what Holmake sees). Only if you must inspect
interactively fall back to loading it:

  markerLib.set_suspended_goal {suspension_name = "<thm>", label_name = "<label>"};
  val (asl,w) = proofManagerLib.top_goal();
  List.app (fn t => print (term_to_string t ^ "\\n")) asl;

(The parent Theorem must be processed up to its QED first: `hol_state_at`
to the dispatcher's QED so the suspension is in the store.)"""


def extract_texts(payload):
    ti = payload.get("tool_input", {}) or {}
    tool = payload.get("tool_name", "")
    out = []
    if tool == "mcp__hol4__hol_send":
        out.append(ti.get("command", ""))
    elif tool == "Edit":
        out.append(ti.get("new_string", ""))
    elif tool == "Write":
        out.append(ti.get("content", ""))
    elif tool == "MultiEdit":
        for e in ti.get("edits", []) or []:
            out.append(e.get("new_string", ""))
    return out


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") not in {
        "mcp__hol4__hol_send", "Edit", "Write", "MultiEdit"
    }:
        return 0
    for text in extract_texts(payload):
        if text and BAD_RE.search(text):
            print(REMINDER, file=sys.stderr)
            return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
