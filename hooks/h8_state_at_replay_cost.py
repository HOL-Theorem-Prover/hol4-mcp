#!/usr/bin/env python3
"""
H8 -- PostToolUse hook injecting a cost-discipline reminder after a
hol_state_at call whose tactic-replay time crosses the threshold.

Stateless: each call judged on its own. Reads PostToolUse JSON on stdin,
extracts `replay=(\\d+)ms` from the tool output. If replay >= 30s, emits a
`hookSpecificOutput.additionalContext` reminder framed for the repeated-use
anti-pattern (hol4-proving skill cost-discipline trigger). Never blocks.

Skips:
  - Cache hits (`replayed=0/N`) -- replay didn't actually run.
  - Missing `[Timing:` line -- error-path return, no replay happened.

Rule source: hol4-proving skill 'HOL4 - iteration loop' / Cost-discipline trigger.
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = "mcp__hol4__hol_state_at"   # None = all calls for this event

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import output_text  # noqa: E402

THRESHOLD_MS = 30_000

TIMING_REPLAY_RE = re.compile(r"replay=(\d+)ms")
TIMING_LINE_RE = re.compile(r"\[Timing:")
CACHE_HIT_RE = re.compile(r"replayed=0/\d+")

REMINDER_TEMPLATE = """\
hol4-hook H8: hol_state_at replay took {replay_s:.1f}s on {file}.

A single slow replay can be legitimate (cold cache, first call on a large
file, no incremental reuse available). The anti-pattern flagged by the hol4-proving skill
cost-discipline trigger is REPEATEDLY running expensive hol_state_at calls
on the same body -- that's "burning replay time".

If you find yourself re-running hol_state_at on this body:
  - Sub-suspend the frontier (primary fix): `>- suspend "Label"` +
    `Resume thm[Label]: cheat QED` after the parent QED. Replay scope shrinks
    to the body only, and the file owns the prefix.
  - For a quick check, `hol_send` SMALL probes (a single `e` tactic) at the
    already-parked frontier -- NOT `eall`/`ef`/`expandf` (all-goals drivers
    misfire on a goalfrag), NOT a re-sent chain (RULE I/G)."""

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__hol_state_at":
        return 0
    text = output_text(payload)
    if not TIMING_LINE_RE.search(text):
        return 0  # error path: no replay happened
    if CACHE_HIT_RE.search(text):
        return 0  # cache hit: replayed=0/N
    m = TIMING_REPLAY_RE.search(text)
    if not m:
        return 0  # no replay timing found
    replay_ms = int(m.group(1))
    if replay_ms < THRESHOLD_MS:
        return 0
    file_path = payload.get("tool_input", {}).get("file", "<unknown file>")
    reminder = REMINDER_TEMPLATE.format(
        replay_s=replay_ms / 1000.0,
        file=file_path,
    )
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": reminder,
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
