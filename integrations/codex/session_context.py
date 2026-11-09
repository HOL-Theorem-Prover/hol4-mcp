#!/usr/bin/env python3
"""Codex-native SessionStart guidance for HOL4 project directories."""

from __future__ import annotations

import glob
import json
import os
import sys


MARKERS = ("Holmakefile", ".holpath")
ANCESTOR_LEVELS = 3
DIRECTIVE = """\
hol4-mcp: HOL4 project detected (Holmakefile/.holpath/*Script.sml).
Before any proof work this session—including writing a tactic, editing a
*Script.sml file, or calling a hol_*/holmake MCP tool—load and follow the
bundled hol4-proving skill. Its rules apply on the first attempt."""


def is_hol4_dir(cwd: str) -> bool:
    directory = os.path.abspath(cwd)
    for _ in range(ANCESTOR_LEVELS + 1):
        if any(os.path.exists(os.path.join(directory, marker)) for marker in MARKERS):
            return True
        parent = os.path.dirname(directory)
        if parent == directory:
            break
        directory = parent
    return bool(glob.glob(os.path.join(os.path.abspath(cwd), "*Script.sml")))


def main() -> int:
    try:
        payload = json.load(sys.stdin)
        if not is_hol4_dir(payload.get("cwd") or os.getcwd()):
            return 0
        print(json.dumps({
            "hookSpecificOutput": {
                "hookEventName": "SessionStart",
                "additionalContext": DIRECTIVE,
            }
        }))
    except Exception:
        return 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
