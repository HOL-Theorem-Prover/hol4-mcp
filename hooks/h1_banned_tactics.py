#!/usr/bin/env python3
"""
H1 -- PreToolUse hook blocking newly-authored banned HOL4 tactics in
*Script.sml edits.

Reads PreToolUse JSON on stdin. For Edit/Write/MultiEdit on a file whose path
ends in `Script.sml` (HOL4 proof-script convention; library files like
*Lib.sml / *Syntax.sml / Tactical.sml are exempt), compares old vs new
content. Flags any banned tactic (TRY, ORELSE, FIRST, THENL, `>|`) whose
post-edit count exceeds its pre-edit count -- i.e. newly introduced or
copied during a discharge edit. Strips (* ... *) comments and "..." strings
before scan to avoid false positives.

Exit 2 + stderr -> tool call is blocked; the model sees the explanation and
must restructure.

Rule source: hol4-proving skill 'HOL4 - banned tactics' section,
Post-discharge Gate 5.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Edit|Write|MultiEdit"   # None = all calls for this event

import json
import re
import sys

BANNED = [
    (re.compile(r"\bTRY\b"),    "TRY"),
    (re.compile(r"\bORELSE\b"), "ORELSE"),
    (re.compile(r"\bFIRST\b"),  "FIRST"),
    (re.compile(r"\bTHENL\b"),  "THENL"),
    (re.compile(r">\|"),        ">|"),
]
COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.DOTALL)
STRING_RE  = re.compile(r'"(?:\\.|[^"\\])*"')

def strip(text):
    return STRING_RE.sub('""', COMMENT_RE.sub("", text))

def count_hits(text):
    cleaned = strip(text)
    return {name: len(rx.findall(cleaned)) for rx, name in BANNED}

def get_old_new(tool_name, tool_input):
    if tool_name == "Edit":
        return tool_input.get("old_string", ""), tool_input.get("new_string", "")
    if tool_name == "Write":
        path = tool_input.get("file_path", "")
        try:
            with open(path, "r", encoding="utf-8") as f:
                return f.read(), tool_input.get("content", "")
        except (FileNotFoundError, OSError):
            return "", tool_input.get("content", "")
    if tool_name == "MultiEdit":
        edits = tool_input.get("edits", [])
        return ("\n".join(e.get("old_string", "") for e in edits),
                "\n".join(e.get("new_string", "") for e in edits))
    return "", ""

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        # Fail-open on malformed input; never block legitimate work due to a hook bug.
        return 0
    tool_name = payload.get("tool_name", "")
    if tool_name not in {"Edit", "Write", "MultiEdit"}:
        return 0
    tool_input = payload.get("tool_input", {})
    if not tool_input.get("file_path", "").endswith("Script.sml"):
        return 0
    old, new = get_old_new(tool_name, tool_input)
    old_h = count_hits(old)
    new_h = count_hits(new)
    introduced = {n: new_h[n] - old_h[n] for n in new_h if new_h[n] > old_h[n]}
    if not introduced:
        return 0
    fp = tool_input.get("file_path", "")
    print(f"hol4-hook H1: refused {tool_name} on {fp}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Newly-introduced banned HOL4 tactic(s):", file=sys.stderr)
    for name, count in introduced.items():
        print(f"  - {name} (+{count} new occurrence(s))", file=sys.stderr)
    print("", file=sys.stderr)
    print("hol4-proving skill 'HOL4 - banned tactics':", file=sys.stderr)
    print("  TRY/ORELSE/FIRST hide failure -> restructure as `>~ [pat] >- suspend \"X\"`.", file=sys.stderr)
    print("  >| (THENL) is position-keyed -> split per subgoal via suspend/Resume.", file=sys.stderr)
    print("", file=sys.stderr)
    print("Restructure the edit before retrying. Pre-existing occurrences in a", file=sys.stderr)
    print("theorem you are restructuring: ask the user how to proceed.", file=sys.stderr)
    return 2

if __name__ == "__main__":
    sys.exit(main())
