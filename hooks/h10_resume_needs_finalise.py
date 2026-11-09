#!/usr/bin/env python3
"""
H10 -- PreToolUse hook injecting a Finalise reminder when a Resume block is
added without a matching `Finalise <thm>;` line in the post-edit content.

Stateless. Never blocks. Reads PreToolUse JSON on stdin. For Edit/Write/
MultiEdit on a Script.sml file, computes pre-edit and post-edit content,
finds newly-introduced Resume theorems (post - pre), and checks each for
a `Finalise <thm>;` line in the post-edit content. Fires a brief reminder
listing any theorem still missing Finalise.

Diff-aware on theorem NAMES (not labels): adding a sub-Resume like
`Resume foo[A_subarm]:` to a file that already has `Resume foo[A]:` and
`Finalise foo;` is silent -- no new theorem name introduced.

Rule source: hol4-proving skill '⛔ Post-discharge audit Gate 2' /
'HOL4 - suspend/Resume/Finalise'.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Edit|Write|MultiEdit"   # None = all calls for this event

import json
import re
import sys

RESUME_RE = re.compile(r"^Resume\s+(\w+)\[", re.MULTILINE)
COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.DOTALL)
STRING_RE  = re.compile(r'"(?:\\.|[^"\\])*"')

def strip(text):
    return STRING_RE.sub('""', COMMENT_RE.sub("", text))

def resume_thms(text):
    return set(RESUME_RE.findall(strip(text)))

def finalise_present(text, name):
    return bool(re.search(rf"^Finalise\s+{re.escape(name)}\s*;", strip(text), re.MULTILINE))

def pre_edit_content(tool_input):
    path = tool_input.get("file_path", "")
    try:
        with open(path, "r", encoding="utf-8") as f:
            return f.read()
    except (FileNotFoundError, OSError):
        return ""

def apply_edits(pre, tool_name, tool_input):
    if tool_name == "Write":
        return tool_input.get("content", "")
    if tool_name == "Edit":
        old = tool_input.get("old_string", "")
        new = tool_input.get("new_string", "")
        if tool_input.get("replace_all", False):
            return pre.replace(old, new)
        return pre.replace(old, new, 1)
    if tool_name == "MultiEdit":
        result = pre
        for edit in tool_input.get("edits", []):
            old = edit.get("old_string", "")
            new = edit.get("new_string", "")
            if edit.get("replace_all", False):
                result = result.replace(old, new)
            else:
                result = result.replace(old, new, 1)
        return result
    return pre

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool_name = payload.get("tool_name", "")
    if tool_name not in {"Edit", "Write", "MultiEdit"}:
        return 0
    tool_input = payload.get("tool_input", {})
    if not tool_input.get("file_path", "").endswith("Script.sml"):
        return 0
    pre = pre_edit_content(tool_input)
    post = apply_edits(pre, tool_name, tool_input)
    added = resume_thms(post) - resume_thms(pre)
    missing = sorted(n for n in added if not finalise_present(post, n))
    if not missing:
        return 0
    if len(missing) == 1:
        n = missing[0]
        msg = (
            f"hol4-hook H10: Resume {n} added; insert `Finalise {n};` "
            f"after the last Resume block now (hol4-proving skill Gate 2)."
        )
    else:
        names = ", ".join(missing)
        msg = (
            f"hol4-hook H10: Resume blocks for {names} added without Finalise. "
            f"Insert `Finalise <thm>;` placeholders now (hol4-proving skill Gate 2)."
        )
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "additionalContext": msg,
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
