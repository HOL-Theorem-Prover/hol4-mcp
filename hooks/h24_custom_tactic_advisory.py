#!/usr/bin/env python3
"""
H24 -- PreToolUse hook advising on newly-defined tactic abbreviations in
*Script.sml edits.

Never blocks. Reads PreToolUse JSON on stdin. For Edit/Write/MultiEdit on a
file whose path ends in `Script.sml`, compares pre- vs post-edit content and
reports `val`/`fun` bindings whose value is a tactic and which this edit
introduces. Lifting a tactic must be a conscious, justified decision; the
default outcomes are to lift a LEMMA or to leave the duplication.

A binding counts as a tactic when its name ends in `_tac`/`_TAC`, or its
right-hand side opens with a tactic combinator (`>>`, `\\\\`, `>-`, `THEN`,
`THEN1`). Bindings named `_` are ignored. Comments and strings are stripped
first. Diff-aware on binding NAMES, so editing a file that already defines
one is silent.

Library files (*Lib.sml, *Syntax.sml) are out of scope by the path test:
tactic abbreviations are legitimate there.

Rule source: hol4-proving skill 'HOL4 - banned tactics'.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Edit|Write|MultiEdit"   # None = all calls for this event

import json
import re
import sys

BIND_RE = re.compile(
    r"^[ \t]*(?:val|fun)\s+([A-Za-z_][A-Za-z0-9_']*)\b([^\n=]*)=(.*)$",
    re.MULTILINE,
)
COMBINATOR_RE = re.compile(r"(>>|\\\\|>-|\bTHEN1\b|\bTHEN\b)")
NAME_RE = re.compile(r".*_(tac|TAC)$")
COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.DOTALL)
STRING_RE = re.compile(r'"(?:\\.|[^"\\])*"')


def strip(text):
    return STRING_RE.sub('""', COMMENT_RE.sub("", text))


def _continuation(text, start):
    """The indented lines following the position ``start`` — an SML
    binding's right-hand side continues only onto indented lines; the first
    column-0 line opens the next declaration or block."""
    out = []
    for line in text[start:].split("\n")[1:]:
        if line and not line[0].isspace():
            break
        out.append(line)
    return "\n".join(out)


def tactic_bindings(text):
    """Names bound by this text whose value looks like a tactic."""
    cleaned = strip(text)
    found = set()
    for m in BIND_RE.finditer(cleaned):
        name, _args, rhs_head = m.group(1), m.group(2), m.group(3)
        if name == "_":
            continue
        rhs = rhs_head + _continuation(cleaned, m.end(3))
        if NAME_RE.match(name) or COMBINATOR_RE.search(rhs):
            found.add(name)
    return found


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
        # Fail-open on malformed input; never disturb legitimate work.
        return 0
    tool_name = payload.get("tool_name", "")
    if tool_name not in {"Edit", "Write", "MultiEdit"}:
        return 0
    tool_input = payload.get("tool_input", {})
    if not tool_input.get("file_path", "").endswith("Script.sml"):
        return 0
    old, new = get_old_new(tool_name, tool_input)
    added = sorted(tactic_bindings(new) - tactic_bindings(old))
    if not added:
        return 0
    names = ", ".join(added)
    msg = (
        f"hol4-hook H24: this edit defines tactic abbreviation(s): {names}. "
        "A named tactic hides WHAT is proved behind HOW, so no call site can be "
        "checked in isolation -- lifting one needs a STRONG, stated justification. "
        "Default outcomes, in order: (1) lift a LEMMA -- state the fact the ritual "
        "establishes and prove it once, so each repeat becomes a one-line "
        "application; (2) leave the duplication -- the reader still sees the whole "
        "argument at every site. Sibling files that define tactic abbreviations are "
        "precedent to weigh, not to follow. Proceed only if you can state the "
        "justification; otherwise restructure the edit."
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
