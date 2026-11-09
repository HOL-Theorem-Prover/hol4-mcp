#!/usr/bin/env python3
"""
H16 -- PostToolUse hook that fires when a goal display shows multiple
subgoals bundled into one Resume body via the `resconj` operator.

Trigger: tool output contains the U+214B + U+1D63 sequence (printed as
`⅋ᵣ`) OR the bare constant name `resconj`. Either symptom means the
proof state at a Resume body holds a `resconj`-merged goal -- the canonical
indicator that the parent dispatcher used ONE suspend label across MULTIPLE
arms (or bundled goals via `>>`), violating the hol4-proving skill rule
"one label = one goal".

Stateless, advisory only. Never blocks. Matches:
  - mcp__hol4__hol_state_at
  - mcp__hol4__hol_send
  - mcp__hol4__hol_check_proof

Rule source: hol4-proving skill 'HOL4 - suspend/Resume/Finalise' / 'One label = one goal'.
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = "mcp__hol4__hol_state_at|mcp__hol4__hol_send|mcp__hol4__hol_check_proof"   # None = all calls for this event

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import output_text  # noqa: E402

# Display marker: U+214B (TURNED AMPERSAND) followed by U+1D63 (SUBSCRIPT R).
DISPLAY_MARKER = "⅋ᵣ"
# Constant name -- match as a word boundary so substrings ("resconjugation")
# don't false-positive (no such identifier exists in HOL4, but cheap defence).
CONST_RE = re.compile(r"\bresconj\b")

REMINDER = """\
hol4-hook H16: goal display contains `⅋ᵣ` / `resconj` -- multiple
subgoals are bundled into one Resume body.

Cause is one of:
  - The SAME `suspend "Label"` reached MULTIPLE arms -- literally repeated
    across dispatcher arms, or two `>~ [pat]` arms whose patterns are shaped
    alike so both route to the same label. Each arm's residual goal got
    tagged identically, and Resume now sees them merged via `resconj`.
    Canonical: ONE label = ONE goal. (One `>~ [pat] >- tac` arm cannot fire
    twice -- it runs on the FIRST match only.)
  - A `>>` (THEN) distributed over residual goals before `suspend "Label"`,
    bundling them.

Fix (hol4-proving skill 'HOL4 - suspend/Resume/Finalise'):
  - Split the suspended arms by giving each its OWN label
    (`suspend "Label_NONE"`, `suspend "Label_Break"`, ...), and write a
    Resume body per label. The bundled `resconj` goal then decomposes
    into per-arm subgoals you can discharge independently.
  - If two `>~ [pat]` arms are shaped alike, refine one pattern with a
    discriminating sub-term so the arms separate (or `Cases_on` upstream
    to drive the goals into distinct shapes).
  - Do NOT try to attack the merged `resconj` goal directly; the structure
    is not user-facing and standard tactics don't decompose it cleanly."""

TARGET_TOOLS = {
    "mcp__hol4__hol_state_at",
    "mcp__hol4__hol_send",
    "mcp__hol4__hol_check_proof",
}

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") not in TARGET_TOOLS:
        return 0
    text = output_text(payload)
    if DISPLAY_MARKER not in text and not CONST_RE.search(text):
        return 0
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": REMINDER,
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
