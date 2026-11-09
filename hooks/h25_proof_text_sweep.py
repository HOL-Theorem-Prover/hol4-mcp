#!/usr/bin/env python3
"""
H25 -- PostToolUse hook sweeping finished HOL4 proof text for composition
defects. Advisory only; PostToolUse runs after the call, so it cannot block.

Primary trigger: `hol_check_proof` returning `Status: OK`. The result carries
`Theorem: X` / `Lines: a-b`, so the sweep scans exactly the theorem just
confirmed -- the done-claim for that theorem, made mechanical instead of
depending on the agent remembering to run an audit.

Successful `hol_check_proof` and QED-position `hol_state_at` calls also record
the exact validated proof revision for H7's edit-then-rebuild advisory.

Backstop: `holmake` on success, reporting COUNTS ONLY for the built theory's
Script.sml, and only when that file is git-modified -- otherwise every build
would report on code the session never touched.

Silent when the proof failed: a broken proof already has its own advisory
(H6), and stacking style notes on it is the noise that gets suites disabled.

`hol_check_proof` is usually called without `file=` (the session cursor
supplies it), so the last file seen on any hol4 tool call is cached under
~/.claude/hook-state/<session_id>/.

Checks and their calibration live in proof_sweep.py.
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = "mcp__hol4__hol_check_proof|mcp__hol4__hol_state_at|mcp__hol4__holmake"

import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proof_sweep  # noqa: E402
from hook_payload import output_text  # noqa: E402

STATE = os.path.expanduser("~/.claude/hook-state")
MAX_SHOWN = 8


def cached_file(session, tool_input):
    """Remember the last file any hol4 call named; fall back to it."""
    path = tool_input.get("file") or tool_input.get("file_path")
    d = os.path.join(STATE, session or "nosession")
    f = os.path.join(d, "hol4_file")
    if path:
        try:
            os.makedirs(d, exist_ok=True)
            with open(f, "w", encoding="utf-8") as fh:
                fh.write(path)
        except OSError:
            pass
        return path
    try:
        with open(f, encoding="utf-8") as fh:
            return fh.read().strip()
    except OSError:
        return None


def emit(msg):
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PostToolUse", "additionalContext": msg}}))
    return 0


def record_validation(session, path, theorem):
    """Record the exact proof revision a successful theorem check validated."""
    if not (path and theorem and os.path.exists(path)):
        return
    try:
        with open(path, encoding="utf-8", errors="replace") as stream:
            text = stream.read()
        fingerprint = proof_sweep.theorem_fingerprint(text, theorem)
        if fingerprint is None:
            return
        key, digest = fingerprint
        directory = os.path.join(STATE, session or "nosession")
        state_path = os.path.join(directory, "h7_validations.json")
        try:
            with open(state_path, encoding="utf-8") as stream:
                state = json.load(stream)
        except Exception:
            state = {}
        state.setdefault(os.path.abspath(path), {})[key] = digest
        os.makedirs(directory, exist_ok=True)
        with open(state_path, "w", encoding="utf-8") as stream:
            json.dump(state, stream)
    except OSError:
        pass


def successful_theorem(text):
    """The theorem name iff this output is a trustworthy completed check."""
    if any(marker in text for marker in (
        "PROOF BROKEN", "ERROR:", "depends on cheat",
        "context has admission history", "prefix-skip mode ON",
    )):
        return None
    if "Status: OK" not in text and "No goals (proof complete)" not in text:
        return None
    match = re.search(r"^Theorem:\s*(\S+)", text, re.M)
    return match.group(1) if match else None


def git_modified(path):
    try:
        out = subprocess.run(["git", "status", "--porcelain", "--", path],
                             cwd=os.path.dirname(path) or ".",
                             capture_output=True, text=True, timeout=5)
        return bool(out.stdout.strip())
    except Exception:
        return False


def do_check_proof(text, path):
    if "Status: OK" not in text:
        return 0
    m = re.search(r"^Theorem:\s*(\S+)", text, re.M)
    r = re.search(r"^Lines:\s*(\d+)\s*-\s*(\d+)", text, re.M)
    if not (m and r and path and os.path.exists(path)):
        return 0
    thm, first, last = m.group(1), int(r.group(1)), int(r.group(2))
    src = open(path, encoding="utf-8", errors="replace").read()
    hits = proof_sweep.sweep(src, first, last)
    if not hits:
        return 0
    shown = hits[:MAX_SHOWN]
    lines = [f"hol4-hook H25: {thm} closes -- {len(hits)} thing(s) to look at in its text:"]
    lines += [f"  L{ln}: {msg}" for ln, msg in shown]
    if len(hits) > MAX_SHOWN:
        lines.append(f"  ... and {len(hits) - MAX_SHOWN} more")
    lines.append("Each is a PROMPT TO CHECK, not a proven defect -- simplification is "
                 "not confluent, so verify any collapse per theorem before keeping it.")
    return emit("\n".join(lines))


def do_holmake(text, tool_input):
    if not re.search(r"\bOK\b", text):
        return 0
    workdir = tool_input.get("workdir", "")
    thys = set(re.findall(r"\b(\w+)Theory\b", text))
    reports = []
    for t in thys:
        path = os.path.join(workdir, f"{t}Script.sml")
        if not os.path.exists(path) or not git_modified(path):
            continue
        n = len(proof_sweep.sweep(open(path, encoding="utf-8", errors="replace").read()))
        if n:
            reports.append(f"{os.path.basename(path)}: {n}")
    if not reports:
        return 0
    return emit("hol4-hook H25: sweep of modified script(s) -- "
                + "; ".join(reports)
                + " item(s) to look at. Run hooks/proof_sweep.py <file> for detail.")


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    tool_input = payload.get("tool_input", {})
    path = cached_file(payload.get("session_id"), tool_input)
    text = output_text(payload)
    try:
        record_validation(payload.get("session_id"), path, successful_theorem(text))
        if tool.endswith("hol_check_proof"):
            return do_check_proof(text, path)
        if tool.endswith("holmake"):
            return do_holmake(text, tool_input)
    except Exception:
        return 0  # never disturb work because of a sweep bug
    return 0


if __name__ == "__main__":
    sys.exit(main())
