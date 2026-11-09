#!/usr/bin/env python3
"""
H7 -- PostToolUse hook injecting a RULE A reminder after a holmake call that
fits the edit-then-rebuild loop.

Advisory only, never blocks. Keyed on repeats per session (state under
~/.claude/hook-state/<session_id>/h7_builds.json): the first build of a
(workdir, target) is silent, and so is a rebuild with unchanged authored proof
text. A rebuild within 30 minutes AFTER a target proof edit gets the reminder.
Executable assertions, top-level translations and unrelated scripts do not.
A changed block already validated at its current revision by hol_state_at at QED
or hol_check_proof also does not trigger the reminder.

Rule source: hol4-proving skill '⛔ RULE A' / 'HOL4 - iteration loop'.
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = "mcp__hol4__holmake"   # None = all calls for this event

import glob
import json
import os
import re
import sys
import time

from proof_sweep import block_fingerprints

STATE = os.path.expanduser("~/.claude/hook-state")
WINDOW_S = 30 * 60

REMINDER_TEMPLATE = """\
hol4-hook H7: Holmake ran again on {target}, {mins} min after the previous
build, with proof text edited in between -- the edit-then-rebuild loop.

Per hol4-proving skill RULE A: holmake is the FILE-BUILD GATE, not the way to
check an edit. Read the edit with hol_state_at (it auto-detects the change)
and confirm the theorem with hol_check_proof; rebuild ONCE when the file is
done. A theorem with surviving Resume blocks also needs its `Finalise <thm>;`
(skill Gate 2) -- without it the theorem stays cheated even when every
Resume body is OK."""


def describe_target(tool_input):
    workdir = tool_input.get("workdir", "")
    target = tool_input.get("target", "")
    if workdir and target:
        return f"{workdir} (target={target})"
    return workdir or target or "<unknown target>"


def state_file(payload):
    return os.path.join(STATE, payload.get("session_id") or "nosession",
                        "h7_builds.json")


def load_state(path):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return {}


def save_state(path, state):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(state, fh)
    except OSError:
        pass


def proof_fingerprints(workdir, target):
    """Only the named target's authored proof blocks, not executable assertions
    or top-level translation. Unknown/directory targets cover local scripts."""
    match = re.fullmatch(r"(.+)Theory(?:\.(?:dat|uo|ui|sml|sig))?", target or "")
    paths = ([os.path.join(workdir, match[1] + "Script.sml")] if match else
             glob.glob(os.path.join(workdir, "*Script.sml")))
    result = {}
    for p in paths:
        try:
            with open(p, encoding="utf-8") as source:
                fingerprints = block_fingerprints(source.read())
        except OSError:
            continue
        if fingerprints:
            result[p] = fingerprints
    return result


def validated_since_edit(payload, previous, current):
    """True iff every changed current proof block was explicitly validated."""
    try:
        with open(os.path.join(STATE, payload.get("session_id") or "nosession",
                               "h7_validations.json"), encoding="utf-8") as stream:
            validations = json.load(stream)
    except Exception:
        return False
    changed = []
    for path, blocks in current.items():
        old_blocks = previous.get(path)
        if not isinstance(blocks, dict) or not isinstance(old_blocks, dict):
            return False  # legacy state: retain the conservative reminder once
        for block, digest in blocks.items():
            if old_blocks.get(block) != digest:
                changed.append((os.path.abspath(path), block, digest))
    return bool(changed) and all(
        validations.get(path, {}).get(block) == digest
        for path, block, digest in changed
    )


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__holmake":
        return 0
    ti = payload.get("tool_input", {})
    workdir = os.path.abspath(ti.get("workdir") or payload.get("cwd") or ".")
    key = f"{workdir}::{ti.get('target') or ''}"
    path = state_file(payload)
    state = load_state(path)
    prev = state.get(key)
    now = time.time()
    proofs = proof_fingerprints(workdir, ti.get("target"))
    state[key] = {"ts": now, "proofs": proofs}
    save_state(path, state)
    if not prev:
        return 0
    age = now - float(prev.get("ts", 0))
    if not (0 <= age < WINDOW_S):
        return 0
    if "proofs" not in prev or not any(prev["proofs"].get(p) != h
                                        for p, h in proofs.items()):
        return 0
    if validated_since_edit(payload, prev["proofs"], proofs):
        return 0
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": REMINDER_TEMPLATE.format(
                target=describe_target(ti), mins=int(age // 60)),
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
