#!/usr/bin/env python3
"""
H22 -- SessionStart hook injecting a directive to load the hol4-proving skill
when the session starts in a HOL4 project directory.

Detection: cwd (or up to 3 ancestors) contains a Holmakefile or .holpath, or
cwd itself contains *Script.sml files. Stateless, advisory only, never blocks;
silent (exit 0, no output) outside HOL4 directories and on any error.

Also reports hook-wiring drift (install_hooks.drift): a hook script in this
directory that ~/.claude/settings.json does not wire, or a wired script that
no longer exists, is named at session start -- in any directory, since an
unwired hook enforces nothing wherever the session runs.

The HOL4 ruleset lives in ~/hol4-mcp/skills/hol4-proving/SKILL.md; the global
CLAUDE.md only carries a pointer. This hook is the mechanical safety net that
makes the skill load on the FIRST attempt rather than after a violation.
"""

HOOK_EVENT = "SessionStart"
HOOK_MATCHER = None   # None = all calls for this event

import glob
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

DIRECTIVE = """\
hol4-hook H22: HOL4 project detected (Holmakefile/.holpath/*Script.sml).
Before ANY proof work this session -- writing a tactic, editing a *Script.sml,
calling a hol_*/holmake MCP tool, or writing a HOL proof plan -- load the HOL4
ruleset: invoke the hol4-proving skill (Skill tool), or Read
~/hol4-mcp/skills/hol4-proving/SKILL.md. The rules apply on the FIRST attempt."""

MARKERS = ("Holmakefile", ".holpath")
ANCESTOR_LEVELS = 3

def is_hol4_dir(cwd):
    d = cwd
    for _ in range(ANCESTOR_LEVELS + 1):
        for m in MARKERS:
            if os.path.exists(os.path.join(d, m)):
                return True
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return bool(glob.glob(os.path.join(cwd, "*Script.sml")))

def wiring_drift():
    """Lines naming unwired or stale hook scripts; empty when settings.json
    matches this directory. Any failure reads as 'no drift' -- advisory only."""
    try:
        import install_hooks
        missing, stale = install_hooks.drift(install_hooks.load_settings())
    except Exception:
        return []
    lines = [f"NOT WIRED: {os.path.basename(p)}" for p in missing]
    lines += [f"WIRED BUT ABSENT: {os.path.basename(p)}" for p in stale]
    if lines:
        lines.insert(0, "hol4-hook H22: hook wiring drift -- these hooks enforce "
                        "nothing this session. Run ~/hol4-mcp/hooks/install_hooks.py:")
    return lines


def main():
    try:
        payload = json.load(sys.stdin)
        cwd = payload.get("cwd") or os.getcwd()
        parts = [DIRECTIVE] if is_hol4_dir(cwd) else []
        drift = wiring_drift()
        if drift:
            parts.append("\n".join(drift))
        if not parts:
            return 0
        print(json.dumps({
            "hookSpecificOutput": {
                "hookEventName": "SessionStart",
                "additionalContext": "\n\n".join(parts),
            }
        }))
    except Exception:
        return 0
    return 0

if __name__ == "__main__":
    sys.exit(main())
