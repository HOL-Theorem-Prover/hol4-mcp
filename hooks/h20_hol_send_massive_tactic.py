#!/usr/bin/env python3
"""
H20 -- PreToolUse hook on mcp__hol4__hol_send that BLOCKS sending a massive
tactic chain, and points to file persistence instead.

Rationale (hol4-proving skill RULE I + the cost-discipline trigger at the end
of 'HOL4 -- iteration loop'): the
interactive proofManagerLib session is SCRATCH, not storage. A large tactic
chain (a `proofManagerLib.e(...)` / `e(...)` / `expand` / replay of a whole
proof body) does NOT belong in hol_send:

  - It is NOT file-validated -- an interactive close says nothing about whether
    the file form replays (RULE G); the two diverge silently (prover-gen names,
    `>>` vs `\\`, parens, goalfrag alpha-renaming).
  - It is lost on compaction and re-sent verbatim on every tweak -- the top
    token-waste failure mode.
  - It re-prints multi-KB goals each call.

The correct loop: flush the verified chain INTO the `*Script.sml` body ending
in a fresh `cheat` / `>- suspend "Frontier"`, then JUMP to the frontier with
`hol_state_at` (full file-order replay -> accurate state) and probe with SHORT
`hol_send` calls (one tactic, minimal goal slice). A multi-line tactic chain
belongs in the FILE, not in repeated hol_send calls.

Heuristic: count THEN-combinators (`\\`, `>>`) and non-blank lines in the
hol_send command. Block when the command is a genuinely massive tactic:
  - >= COMBINATOR_LIMIT THEN-combinators, OR
  - >= LINE_LIMIT non-blank lines AND at least a few combinators (so it is a
    tactic chain, not a long definition/query/goal-set).

Small interactive probes (a handful of tactics) pass untouched. Stateless;
fails open on malformed input.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_send"   # None = all calls for this event

import json
import re
import sys

COMBINATOR_LIMIT = 6    # >= this many `\\`/`>>` THEN-combinators -> massive
LINE_LIMIT = 8          # >= this many non-blank lines (with some combinators)
MIN_COMBINATORS_FOR_LINES = 2

REMINDER = """\
hol4-hook H20: REFUSED -- this hol_send is a MASSIVE tactic chain. This is a
HIGH-SEVERITY violation of hol4-proving skill RULE I, not a style nit.

WHY THIS IS SERIOUS (it has burned entire sessions):
  - It PROVES NOTHING. An interactive close says NOTHING about whether the file
    form replays (RULE G). The two diverge SILENTLY on prover-gen names
    (`w'`/`v15`), goalfrag alpha-renaming, `>>` vs `\\`, parens, simp-set order.
    Driving a big chain to "read a goal" gives you a goal from a DIFFERENT
    context than the file -- you then fix a phantom.
  - It is LOST on compaction and RE-SENT verbatim on every tweak -- the single
    largest token-waste failure mode, re-printing multi-KB goals each call.
  - The proofManagerLib session is SCRATCH, never storage. Treat every hol_send
    as a ONE-tactic probe on an already-parked frontier.

DO THIS INSTEAD:
  1. Flush the verified chain INTO the *Script.sml body, ending in a fresh
     `cheat` or `>- suspend "Frontier"`.
  2. JUMP to the frontier with `hol_state_at` (replays the full prefix in file
     order -> the goal is EXACTLY what Holmake sees; no divergence).
  3. Probe with SHORT `hol_send` only: ONE tactic, a MINIMAL goal slice
     (`String.substring (term_to_string g) 0 300`), never a full-body replay.

A chain past a few lines belongs in the FILE. If `hol_state_at` cannot reach a
goal inside a `\\`-chain, SUB-SUSPEND the frontier (`>- suspend "X"` + Resume)
so the FILE owns the prefix -- NEVER replay the body through hol_send.
"""


def count_combinators(text):
    # `\\` (THEN) appears as two literal backslashes; `>>` (THEN) likewise.
    # Count occurrences of each operator token.
    n = len(re.findall(r'\\\\', text))      # \\  (HOL/CakeML THEN)
    n += len(re.findall(r'>>', text))       # >>  (THEN)
    return n


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__hol_send":
        return 0
    cmd = (payload.get("tool_input", {}) or {}).get("command", "") or ""
    if not cmd:
        return 0

    combos = count_combinators(cmd)
    nonblank_lines = sum(1 for ln in cmd.splitlines() if ln.strip())

    massive = (combos >= COMBINATOR_LIMIT) or (
        nonblank_lines >= LINE_LIMIT and combos >= MIN_COMBINATORS_FOR_LINES
    )
    if massive:
        print(REMINDER, file=sys.stderr)
        print(
            f"\n(measured: {combos} THEN-combinators, {nonblank_lines} "
            f"non-blank lines)",
            file=sys.stderr,
        )
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
