#!/usr/bin/env python3
"""
H29 -- PreToolUse hook blocking REPEAT mcp__hol4__hol_stop / hol_restart on
the same theory directory (the ritual-stop pattern). Supersedes the retired
advisory-only restart hook (restart only; hol_stop had no coverage): the repeat-key auto-allows the
legitimate cases instead of gating everything behind consent.

A first stop/restart always passes (finished a theory, switching theory
directories, fresh start) with a one-line reminder, and so does any stop once
the cached working file (H25's hol4_file) sits in a different directory --
another theory. Blocked: a second stop/restart within 30 minutes while still
working in the same directory, whichever file inside it is current -- the
signature of using stop/restart inside the edit-check loop. That loop never
needs one: hol_state_at auto-detects file edits and rebuilt ancestors and
moves the session across workdirs itself (MCP server), and every stop costs
a HOL restart and a prefix reload (from the last saved state at best) on the
next navigation.

Soft hook: the repeat is blocked once, then an identical retry passes with an
override note and is logged (hook_payload.soft_block). A stop within ten
minutes of a budget TIMEOUT recorded by H6 passes outright (a wedged session
is a real possibility there), and so does one within ten minutes of an H30
stale-ancestor refusal covering the working directory (the stop frees the
session's memory for the rebuild H30 asks for). The literal phrase `restart ok` anywhere in
the session's user turns pre-grants. Fail-open: unknown working file,
unreadable state, or unreadable transcript never blocks.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_stop|mcp__hol4__hol_restart"

import json
import os
import re
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import emit_context, granted, pregranted, soft_block  # noqa: E402

STATE = os.path.expanduser("~/.claude/hook-state")
COOLDOWN_S = 30 * 60
TIMEOUT_GRACE_S = 10 * 60


def recent_timeout_age(payload):
    """Seconds since H6 recorded a budget TIMEOUT on a navigation this
    session, if within the grace window; else None."""
    try:
        with open(os.path.join(session_dir(payload), "last_timeout"),
                  encoding="utf-8") as fh:
            age = time.time() - float(fh.read().strip())
    except Exception:
        return None
    return age if 0 <= age < TIMEOUT_GRACE_S else None


def recent_stale_block(payload, directory):
    """(age in seconds, stale directories) of an H30 refusal within the grace
    window whose target or stale theories sit in `directory`; else None."""
    try:
        with open(os.path.join(session_dir(payload), "last_stale_block"),
                  encoding="utf-8") as fh:
            block = json.load(fh)
        age = time.time() - float(block["ts"])
        dirs = set(block.get("stale_dirs") or [])
        covered = dirs | {os.path.dirname(block["target"])}
    except Exception:
        return None
    if 0 <= age < TIMEOUT_GRACE_S and directory in covered:
        return age, sorted(dirs)
    return None


CONSENT_RE = re.compile(r"\brestart\s+ok\b", re.IGNORECASE)
TOOLS = ("mcp__hol4__hol_stop", "mcp__hol4__hol_restart")


def session_dir(payload):
    return os.path.join(STATE, payload.get("session_id") or "nosession")


def working_file(payload):
    try:
        with open(os.path.join(session_dir(payload), "hol4_file"),
                  encoding="utf-8") as fh:
            return fh.read().strip() or None
    except OSError:
        return None


def last_stop(payload):
    try:
        with open(os.path.join(session_dir(payload), "h29_last_stop"),
                  encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return None


def record_stop(payload, tool, path):
    d = session_dir(payload)
    try:
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "h29_last_stop"), "w",
                  encoding="utf-8") as fh:
            json.dump({"ts": time.time(), "tool": tool, "file": path}, fh)
    except OSError:
        pass


def advise(tool):
    msg = (
        f"hol4-hook H29: {tool} allowed -- first stop/restart in this window. "
        "Justify it: right when a theory is FINISHED, or when leaving its "
        "directory. It is never part of the edit-check loop -- hol_state_at "
        "auto-detects file edits, reloads after an ancestor rebuild and moves "
        "the session to a new workdir itself; every stop costs a HOL restart "
        "and a prefix reload on the next navigation. A repeat in the same directory within "
        "30 min is blocked (override: `restart ok`)."
    )
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse", "additionalContext": msg}}))
    return 0


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    if tool not in TOOLS:
        return 0
    consent = granted(payload, CONSENT_RE)
    if consent is None:
        return 0  # fail-open
    path = working_file(payload)
    if pregranted(payload, "H29", CONSENT_RE, "restart ok", f"{tool}"):
        record_stop(payload, tool, path)
        return 0
    prev = last_stop(payload)
    prev_file = prev.get("file") if prev else None
    if (path and prev_file
            and os.path.dirname(prev_file) == os.path.dirname(path)):
        age = time.time() - float(prev.get("ts", 0))
        if 0 <= age < COOLDOWN_S:
            since_timeout = recent_timeout_age(payload)
            if since_timeout is not None:
                record_stop(payload, tool, path)
                emit_context(
                    f"[H29: {tool} allowed -- a navigation hit its budget "
                    f"(TIMEOUT) {int(since_timeout // 60)} min ago, so a wedged "
                    f"session is a real possibility. Otherwise a repeat stop in "
                    f"the same directory is the ritual-stop pattern.]")
                return 0
            stale = recent_stale_block(payload, os.path.dirname(path))
            if stale is not None:
                record_stop(payload, tool, path)
                emit_context(
                    f"[H29: {tool} allowed -- H30 refused navigation "
                    f"{int(stale[0] // 60)} min ago over stale ancestors "
                    f"({', '.join(stale[1]) or 'built before their own ancestors'}); "
                    f"stopping the session frees its memory for that rebuild. Confirm "
                    f"the stop returned BEFORE you start the build, and navigate again "
                    f"only after the build finished.]")
                return 0
            mins = int(age // 60)
            code = soft_block(payload, "H29", os.path.dirname(path), [
                f"hol4-hook H29: refused {tool} -- repeat stop/restart {mins} min "
                f"after the last one, still working in the same directory:",
                f"  {os.path.dirname(path)}",
                "",
                "A stop/restart is NEVER part of the edit-check loop:",
                "hol_state_at auto-detects file edits, reloads the session after an ancestor",
                "rebuild and moves it to a new workdir itself (MCP server contract), and every",
                "stop costs a HOL restart and a prefix reload on the next navigation.",
                "A weird replay or a goal that looks wrong is a proof or navigation error to",
                "diagnose (RULE D), which the restart would erase.",
                "",
                "Auto-allowed: the first stop/restart, any stop once the working file is in",
                "another directory, a stop shortly after a budget TIMEOUT, and a stop shortly",
                "after H30 refused navigation here over stale ancestor theories (to free",
                "memory for the rebuild).",
            ], f"repeat stop/restart in {os.path.dirname(path)} within 30 min")
            if code == 0:
                record_stop(payload, tool, path)
            return code
    record_stop(payload, tool, path)
    return advise(tool)


if __name__ == "__main__":
    sys.exit(main())
