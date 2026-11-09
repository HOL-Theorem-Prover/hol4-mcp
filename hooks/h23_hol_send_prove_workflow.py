#!/usr/bin/env python3
"""
H23 -- PreToolUse hook on mcp__hol4__hol_send that BLOCKS the standalone-`prove`
workflow (constructing a complete proof in the scratch session via `prove`,
`store_thm`, `TAC_PROOF`, ...), and points to the file-owned workflow instead.

Rationale (hol4-proving skill RULE I + RULE G): the interactive proofManagerLib
session is SCRATCH, not storage. Building a finished proof there with a goal
you TYPED -- `val x = prove(``...``, tac)` / `store_thm(...)` / `TAC_PROOF(...)`
-- proves NOTHING about whether the theorem replays in the *Script.sml file:

  - The goal you typed is NOT the goal the file presents. After the file's
    prefix runs (`rpt conj_tac` nesting, the real assumption set, abbrevs like
    `sort_width (LENGTH Ys)` vs `LENGTH Xs`, lambda type-annotations), the arm
    goal diverges silently from the one you hand-wrote. A standalone `prove`
    that closes can sit atop an arm that breaks in the file -- you then debug a
    phantom (this exact trap has burned sessions).
  - It is lost on compaction and re-sent verbatim on every tweak.

The correct loop:
  - Whole lemma  -> write it as `Theorem foo[local]: ... Proof ... QED` in the
    *Script.sml and confirm with `hol_check_proof foo`.
  - One arm of a bigger theorem -> sub-suspend it: `>- suspend "arm"` in the
    Proof body + a `Resume thm[arm]:` block after QED (+ `Finalise thm;`).
    `hol_state_at` to the suspend replays the full prefix in file order, so the
    arm goal is EXACTLY what Holmake sees -- no divergence.

`hol_send` is for SHORT probes (one tactic on an already-parked frontier, a
`DB.find`, a term inspection), never for a finished proof. Stateless; fails
open on malformed input.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_send"   # None = all calls for this event

import json
import re
import sys

# `prove(`, `Q.prove(`, `Tactical.prove(`, `boolLib.prove(`, `bossLib.prove(`
# (\bprove also matches the `prove` in `Q.prove` since `.` is a word boundary;
#  `disprove`/`improve`/`approve` are NOT matched -- no boundary before `prove`).
PROVE_RE = re.compile(r'\bprove\s*\(')
# store_thm / Q.store_thm / save_thm / Q.save_thm
STORE_RE = re.compile(r'\b(?:store|save)_thm\s*\(')
# TAC_PROOF((asl,g), tac)
TACPROOF_RE = re.compile(r'\bTAC_PROOF\s*\(')

REMINDER = """\
hol4-hook H23: REFUSED -- this hol_send engages the standalone-`prove` workflow
(`prove` / `store_thm` / `TAC_PROOF`). This is a RULE I + RULE G violation: the
proofManagerLib session is SCRATCH, and a proof you close there with a goal you
TYPED proves NOTHING about whether the theorem replays in the *Script.sml file.

WHY IT BURNS SESSIONS:
  - The goal you hand-wrote is NOT the goal the file presents. After the file's
    prefix runs (`rpt conj_tac` nesting, the real assumptions, abbreviations,
    lambda type-annotations), the arm goal diverges SILENTLY. A standalone
    `prove` that closes can sit atop an arm that breaks in the file -- you then
    debug a phantom.
  - It is lost on compaction and re-sent verbatim on every tweak.

DO THIS INSTEAD:
  - Whole lemma  -> write `Theorem foo[local]: ... Proof <tac> QED` in the
    *Script.sml, then confirm with `hol_check_proof foo`.
  - One arm of a bigger theorem -> SUB-SUSPEND it: `>- suspend "arm"` in the
    Proof body + a `Resume thm[arm]:` block after QED (+ `Finalise thm;`).
    `hol_state_at` to the suspend replays the prefix in file order -> the arm
    goal is EXACTLY what Holmake sees, no divergence.

`hol_send` is for SHORT probes only (one tactic on a parked frontier, a
`DB.find`, a term inspection) -- never a finished proof.
"""


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

    hits = []
    if PROVE_RE.search(cmd):
        hits.append("prove(")
    if STORE_RE.search(cmd):
        hits.append("store_thm(/save_thm(")
    if TACPROOF_RE.search(cmd):
        hits.append("TAC_PROOF(")

    if hits:
        print(REMINDER, file=sys.stderr)
        print(f"\n(matched: {', '.join(hits)})", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
