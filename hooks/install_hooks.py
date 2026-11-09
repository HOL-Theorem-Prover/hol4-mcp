#!/usr/bin/env python3
"""
Wire every hook in this directory into Claude Code's settings.json.

Each hook declares its own registration at module level:

    HOOK_EVENT   = "PreToolUse"                 # or PostToolUse, SessionStart, ...
    HOOK_MATCHER = "Edit|Write|MultiEdit"       # or None = all calls for this event

so adding a hook file is the only step needed to install it -- there is no
separate list to keep in sync. Declarations are read statically (ast), never
imported, so a broken hook cannot execute during install.

Usage:
    ./install_hooks.py            merge all declared hooks into settings.json
    ./install_hooks.py --check    report drift, exit 1 if any (no writes)
    ./install_hooks.py --print    print the hooks block to stdout, merge nothing

Merging is idempotent and additive: an entry already pointing at a hook's path
is left alone, and hook entries for scripts outside this directory are never
touched. A timestamped backup is written before any change.
"""
import argparse
import ast
import json
import os
import re
import sys
import time

HOOK_RE = re.compile(r"h\d+_[A-Za-z0-9_]+\.py")
HERE = os.path.dirname(os.path.abspath(__file__))
SETTINGS = os.path.expanduser("~/.claude/settings.json")


def declared(path):
    """(event, matcher) declared by a hook file, or None if it declares neither."""
    tree = ast.parse(open(path, encoding="utf-8").read())
    got = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in ("HOOK_EVENT", "HOOK_MATCHER"):
                try:
                    got[name] = ast.literal_eval(node.value)
                except ValueError:
                    return None
    if "HOOK_EVENT" not in got:
        return None
    return got["HOOK_EVENT"], got.get("HOOK_MATCHER")


def discover():
    """{path: (event, matcher)} for every hook here; raises on an undeclared one."""
    out, undeclared = {}, []
    for fn in sorted(os.listdir(HERE), key=lambda f: (len(f), f)):
        if not HOOK_RE.fullmatch(fn):
            continue
        path = os.path.join(HERE, fn)
        spec = declared(path)
        if spec is None:
            undeclared.append(fn)
        else:
            out[path] = spec
    if undeclared:
        raise SystemExit(
            "hook(s) with no HOOK_EVENT declaration: " + ", ".join(undeclared) +
            "\nAdd HOOK_EVENT / HOOK_MATCHER at module level so they self-register."
        )
    return out


def build_block(specs):
    block = {}
    for path, (event, matcher) in sorted(specs.items()):
        entry = {"hooks": [{"type": "command", "command": path}]}
        if matcher:
            entry["matcher"] = matcher
        block.setdefault(event, []).append(entry)
    return block


def wired_paths(settings):
    return set(re.findall(r'"command":\s*"([^"]+)"', json.dumps(settings.get("hooks", {}))))


def load_settings(path=SETTINGS):
    if os.path.exists(path):
        return json.load(open(path, encoding="utf-8"))
    return {}


def drift(settings, specs=None):
    """(missing, stale): hook scripts here that settings.json does not wire,
    and wired paths under this directory whose script no longer exists."""
    specs = discover() if specs is None else specs
    live = wired_paths(settings)
    missing = [p for p in specs if p not in live]
    stale = [p for p in live
             if os.path.dirname(p) == HERE and not os.path.exists(p)]
    return missing, stale


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="report drift, write nothing")
    ap.add_argument("--print", dest="dump", action="store_true", help="print the block")
    args = ap.parse_args()

    specs = discover()
    if args.dump:
        print(json.dumps({"hooks": build_block(specs)}, indent=2))
        return 0

    settings = load_settings()
    missing, stale = drift(settings, specs)

    if args.check:
        for p in missing:
            print(f"NOT WIRED: {os.path.basename(p)}")
        for p in stale:
            print(f"WIRED BUT ABSENT: {os.path.basename(p)}")
        if not missing and not stale:
            print(f"ok: all {len(specs)} hook(s) wired, none stale")
            return 0
        return 1

    if not missing and not stale:
        print(f"ok: all {len(specs)} hook(s) already wired; nothing to do")
        return 0

    backup = f"{SETTINGS}.bak.{time.strftime('%Y%m%d-%H%M%S')}"
    if os.path.exists(SETTINGS):
        with open(backup, "w", encoding="utf-8") as f:
            json.dump(settings, f, indent=2)
        print(f"backup: {backup}")

    hooks = settings.setdefault("hooks", {})
    for event, entries in build_block({p: specs[p] for p in missing}).items():
        hooks.setdefault(event, []).extend(entries)
    for event in list(hooks):
        hooks[event] = [e for e in hooks[event]
                        if not any(h.get("command") in stale for h in e.get("hooks", []))]
        if not hooks[event]:
            del hooks[event]

    with open(SETTINGS, "w", encoding="utf-8") as f:
        json.dump(settings, f, indent=2)
    for p in missing:
        print(f"wired:   {os.path.basename(p)}")
    for p in stale:
        print(f"removed: {os.path.basename(p)} (script no longer present)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
