#!/usr/bin/env python3
"""
H32 -- PreToolUse hook on mcp__hol4__holmake: a build must name its target.

An UNTARGETED build (no `target`) makes Holmake build every theory in the
directory, including ones nobody is working on (hol4-proving RULE A, build
ownership). Soft hook: the first untargeted build of a workdir is blocked
once, an identical retry passes with an override note and is logged
(hook_payload.soft_block), and the literal phrase `build ok` anywhere in the
session's user turns pre-grants. A targeted build always passes -- when its
stale ancestors live in other directories, rebuilding them is exactly what
H30 asks for.

Fails open on an unreadable transcript.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__holmake"

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import granted, pregranted, soft_block  # noqa: E402

CONSENT_RE = re.compile(r"\bbuild\s+ok\b", re.IGNORECASE)


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__holmake":
        return 0
    ti = payload.get("tool_input", {})
    if ti.get("target"):
        return 0
    workdir = ti.get("workdir") or payload.get("cwd") or "."
    if not os.path.isabs(workdir):
        workdir = os.path.abspath(os.path.join(payload.get("cwd", "."), workdir))

    consent = granted(payload, CONSENT_RE)
    if consent is None:
        return 0  # fail-open
    if pregranted(payload, "H32", CONSENT_RE, "build ok",
                  f"untargeted build of {workdir}"):
        return 0
    return soft_block(payload, "H32", workdir, [
        f"hol4-hook H32: refused holmake with no target in {workdir}.",
        "",
        "An untargeted Holmake builds EVERY theory in the directory, not the",
        "one you are working on. Name it: holmake(workdir=..., target=<thy>Theory).",
    ], f"untargeted (whole-directory) build of {workdir}")


if __name__ == "__main__":
    sys.exit(main())
