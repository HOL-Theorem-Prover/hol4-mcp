#!/usr/bin/env python3
"""
H30 -- PreToolUse hook blocking HOL navigation of a file whose ancestor
theories are stale (edited upstream not rebuilt, artifacts missing/mid-write,
or built before their own ancestors).

The fault class this forecloses: edit an upstream *Script.sml, keep working
downstream. Nothing else ever reports it -- downstream sessions and fresh
loads read the BUILT .dat (HOL `load` inspects no script content and no
mtime), so every downstream check silently runs against the PRE-EDIT
upstream. The only native symptom is the late, mislocated `Missing
dependency: <thy>` when artifacts are absent mid-rebuild.

Make-style staleness over the target's ancestor closure, headers parsed from
the scripts themselves (`Theory`/`Ancestors` blocks with SML comments
stripped, plus old-style `open ... fooTheory` prefixes), memoized by script
mtime under ~/.claude/hook-state/h30/. Duplicate theory names (e.g. candle
standard vs overloading) resolve to the candidate nearest the target file. A
theory T (script in dir D, artifacts D/.hol/objs/TTheory.dat or
D/TTheory.dat) is stale iff its artifact is missing, older than its script,
or older than a direct ancestor's artifact. The target file itself is exempt
(it is the one being developed). Theories whose script is not in the
target's repo (HOL stdlib) are skipped.

Self-clearing: rebuilding (mcp__hol4__holmake) makes artifacts newer than
sources and the block disappears. Soft hook: a given (file, stale set) is
blocked once, then an identical retry passes with an override note and is
logged (hook_payload.soft_block); a newly stale theory blocks again. The
literal phrase `stale ok` anywhere in the session's user turns pre-grants
the deferral. Fail-open on any internal error, unknown target file,
unreadable transcript, or closure larger than the cap. A refusal is recorded
(`last_stale_block` in the session's hook state) for H29, which lets the stop
that frees memory for the rebuild through.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = ("mcp__hol4__hol_state_at|mcp__hol4__hol_goals|"
                "mcp__hol4__hol_check_proof|mcp__hol4__hol_send|"
                "mcp__hol4__hol_start")

import json
import os
import re
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import granted, pregranted, soft_block  # noqa: E402

STATE = os.path.expanduser("~/.claude/hook-state")
H30_DIR = os.path.join(STATE, "h30")
GRAPH_CACHE = os.path.join(H30_DIR, "graph_cache.json")
INDEX_CACHE = os.path.join(H30_DIR, "index_cache.json")
CONSENT_RE = re.compile(r"\bstale\s+ok\b", re.IGNORECASE)
CLOSURE_CAP = 2000
INDEX_TTL_S = 600
MAX_ROOTS_SHOWN = 4
SKIP_DIRS = {".git", ".hol", ".HOLMK", "node_modules", "__pycache__"}


def load_json(path):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return {}


def save_json(path, obj):
    try:
        os.makedirs(H30_DIR, exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(obj, fh)
        os.replace(tmp, path)
    except OSError:
        pass


def repo_root(path):
    d = os.path.dirname(os.path.abspath(path))
    for _ in range(12):
        if os.path.isdir(os.path.join(d, ".git")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            return None
        d = parent
    return None


def build_index(root):
    """theory name -> [Script.sml paths], for every script under root."""
    idx = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            if fn.endswith("Script.sml"):
                idx.setdefault(fn[:-len("Script.sml")], []).append(
                    os.path.join(dirpath, fn))
    return idx


def get_index(root):
    cache = load_json(INDEX_CACHE)
    ent = cache.get(root)
    if ent and time.time() - ent.get("ts", 0) < INDEX_TTL_S:
        idx = ent["idx"]
        if all(isinstance(v, list) for v in idx.values()):
            return idx
    idx = build_index(root)
    cache[root] = {"ts": time.time(), "idx": idx}
    save_json(INDEX_CACHE, cache)
    return idx


def resolve(idx, name, near):
    """Pick the Script.sml for `name`; on duplicates, nearest to `near`."""
    ps = idx.get(name)
    if not ps:
        return None
    if len(ps) == 1:
        return ps[0]
    near_dir = os.path.dirname(near) + os.sep
    return max(ps, key=lambda p: (
        len(os.path.commonprefix([os.path.dirname(p) + os.sep, near_dir])),
        -len(p)))


def strip_comments(text):
    """Remove (possibly nested) SML comments."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


ANC_NAME_RE = re.compile(r"([A-Za-z0-9_']+)(?:\[[^\]]*\])?")
OPEN_THY_RE = re.compile(r"\b([A-Za-z0-9_']+)Theory\b")


def parse_deps(path):
    """Direct ancestor theory names declared by a Script.sml."""
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            head = strip_comments(fh.read(16384))
    except OSError:
        return []
    lines = head.splitlines()
    deps = set()
    in_anc = False
    saw_header = False
    for ln in lines[:160]:
        if re.match(r"^Theory\s+\S+", ln):
            saw_header = True
            continue
        if saw_header:
            m = re.match(r"^Ancestors\b\s*(.*)$", ln)
            if m:
                in_anc = True
                for tok in m.group(1).split():
                    t = ANC_NAME_RE.fullmatch(tok)
                    if t:
                        deps.add(t.group(1))
                continue
            if in_anc:
                if ln.strip() == "" or re.match(r"^\S", ln):
                    in_anc = False
                else:
                    for tok in ln.split():
                        t = ANC_NAME_RE.fullmatch(tok)
                        if t:
                            deps.add(t.group(1))
    if not saw_header:
        in_open = False
        for ln in lines[:120]:
            if re.match(r"^\s*(local\s+)?open\b", ln):
                in_open = True
            elif in_open and not re.match(r"^\s*[A-Za-z0-9_'. ]+\s*;?\s*$", ln):
                in_open = False
            if in_open:
                deps.update(OPEN_THY_RE.findall(ln))
                if ";" in ln:
                    in_open = False
    return sorted(deps)


def get_deps(path, graph):
    try:
        mtime = os.path.getmtime(path)
    except OSError:
        return []
    ent = graph.get(path)
    if ent and ent.get("mtime") == mtime:
        return ent["deps"]
    deps = parse_deps(path)
    graph[path] = {"mtime": mtime, "deps": deps}
    return deps


def artifact_mtime(script_path):
    """Newest built artifact for the theory of script_path, or None."""
    d = os.path.dirname(script_path)
    t = os.path.basename(script_path)[:-len("Script.sml")]
    best = None
    for cand in (os.path.join(d, ".hol", "objs", t + "Theory.dat"),
                 os.path.join(d, t + "Theory.dat")):
        try:
            m = os.path.getmtime(cand)
            best = m if best is None or m > best else best
        except OSError:
            pass
    return best


def check_closure(target, root):
    """Return (roots, n_downstream, direct_stale_names) of stale ancestors.

    roots: [(script_path, why)] theories stale because of their OWN
    script/artifacts; n_downstream: count stale only via an ancestor.
    direct_stale_names: target's direct deps that are transitively stale
    (suggested holmake targets)."""
    idx = get_index(root)
    graph = load_json(GRAPH_CACHE)
    target_theory = os.path.basename(target)[:-len("Script.sml")]

    art = {}       # theory -> artifact mtime (or None)
    smtime = {}    # theory -> script mtime
    dep_map = {}   # theory -> [repo-internal dep names]
    spaths = {}    # theory -> resolved script path
    seen = set()
    stack = list(get_deps(target, graph))
    direct = set(stack)
    while stack:
        name = stack.pop()
        if name in seen or name == target_theory:
            continue
        seen.add(name)
        if len(seen) > CLOSURE_CAP:
            return None  # too big -- fail open
        spath = resolve(idx, name, target)
        if not spath:
            continue  # external theory (HOL stdlib etc.)
        try:
            smtime[name] = os.path.getmtime(spath)
        except OSError:
            continue
        spaths[name] = spath
        art[name] = artifact_mtime(spath)
        ds = [d for d in get_deps(spath, graph) if d in idx]
        dep_map[name] = ds
        stack.extend(ds)
    save_json(GRAPH_CACHE, graph)

    stale = {}  # name -> "root" | "downstream"
    changed = True
    while changed:
        changed = False
        for name in dep_map:
            if name in stale:
                continue
            a = art.get(name)
            if a is None:
                stale[name] = "root"; changed = True; continue
            if a < smtime.get(name, 0):
                stale[name] = "root"; changed = True; continue
            for d in dep_map[name]:
                if d in stale or (art.get(d) is not None and art[d] > a):
                    stale[name] = "downstream"; changed = True; break
    roots = []
    for name, kind in stale.items():
        if kind != "root":
            continue
        spath = spaths[name]
        if art.get(name) is None:
            why = "artifacts missing (never built, or a rebuild is mid-write)"
        else:
            why = ("script edited %s > artifacts built %s"
                   % (time.strftime("%m-%d %H:%M", time.localtime(smtime[name])),
                      time.strftime("%m-%d %H:%M", time.localtime(art[name]))))
        roots.append((spath, why))
    n_down = sum(1 for k in stale.values() if k == "downstream")
    direct_stale = sorted(n for n in direct if n in stale)
    return roots, n_down, direct_stale


def cache_working_file(payload, path):
    """Keep H25's per-session working-file cache current (H30 sees hol_goals
    and hol_start, which H25's matcher does not)."""
    d = os.path.join(STATE, payload.get("session_id") or "nosession")
    try:
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "hol4_file"), "w", encoding="utf-8") as fh:
            fh.write(path)
    except OSError:
        pass


def target_file(payload):
    ti = payload.get("tool_input", {})
    path = ti.get("file") or ti.get("file_path")
    if path:
        path = os.path.abspath(os.path.join(payload.get("cwd", "."), path)) \
            if not os.path.isabs(path) else path
        cache_working_file(payload, path)
        return path
    try:
        d = os.path.join(STATE, payload.get("session_id") or "nosession")
        with open(os.path.join(d, "hol4_file"), encoding="utf-8") as fh:
            return fh.read().strip() or None
    except OSError:
        return None


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    # Enforce our own declared scope even when a client dispatcher is broad.
    # In particular, recovery builds and polling must not consume an override.
    if not re.fullmatch(HOOK_MATCHER, tool):
        return 0
    try:
        target = target_file(payload)
        if not target or not target.endswith("Script.sml") \
                or not os.path.exists(target):
            return 0
        root = repo_root(target)
        if not root:
            return 0
        res = check_closure(target, root)
        if not res:
            return 0
        roots, n_down, direct_stale = res
        if not roots and not n_down:
            return 0
    except Exception:
        return 0  # never disturb work because of a checker bug
    consent = granted(payload, CONSENT_RE)
    if consent is None:
        return 0  # fail-open
    stale_names = sorted(os.path.basename(p) for p, _ in roots)
    if pregranted(payload, "H30", CONSENT_RE, "stale ok",
                  f"stale ancestors {', '.join(stale_names)} of "
                  f"{os.path.basename(target)}; results here are not trustworthy "
                  f"until they are rebuilt"):
        return 0
    lines = [f"hol4-hook H30: refused {tool} on {os.path.basename(target)} -- "
             f"stale ancestor theories."]
    for spath, why in roots[:MAX_ROOTS_SHOWN]:
        lines += [f"  {spath}", f"    {why}"]
    if len(roots) > MAX_ROOTS_SHOWN:
        lines.append(f"  ... and {len(roots) - MAX_ROOTS_SHOWN} more edited-unbuilt "
                     f"ancestors")
    if n_down:
        lines.append(f"  (+ {n_down} theories built before their own ancestors)")
    lines += [
        "",
        "Downstream sessions and fresh loads read the BUILT .dat, so every check",
        "on this file would silently run against the PRE-EDIT upstream; no tool",
        "reports that. Rebuild each stale theory from its own directory, then",
        "the target's direct dependencies:",
    ]
    for spath, _ in roots[:MAX_ROOTS_SHOWN]:
        thy = os.path.basename(spath)[:-len("Script.sml")]
        lines.append(f"  mcp__hol4__holmake workdir={os.path.dirname(spath)} "
                     f"target={thy}Theory")
    for name in direct_stale[:3]:
        if name + "Script.sml" not in stale_names:
            lines.append(f"  mcp__hol4__holmake workdir=<{name}'s directory> "
                         f"target={name}Theory")
    lines += ["(Long builds: detach=True + hol_build_status. The block clears itself",
              "once artifacts are newer than their sources.)"]
    fingerprint = target + "|" + "|".join(sorted(p for p, _ in roots))
    code = soft_block(payload, "H30", fingerprint, lines,
                      f"navigating {os.path.basename(target)} against STALE ancestors "
                      f"{', '.join(stale_names)}; nothing checked here is trustworthy "
                      f"until they are rebuilt")
    if code == 2:
        record_block(payload, target, roots)
    return code


def record_block(payload, target, roots):
    """Note the refusal for H29: a stop right after it frees the session's
    memory for the rebuild it asks for."""
    d = os.path.join(STATE, payload.get("session_id") or "nosession")
    try:
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "last_stale_block"), "w", encoding="utf-8") as fh:
            json.dump({"ts": time.time(), "target": target,
                       "stale_dirs": sorted({os.path.dirname(p) for p, _ in roots})}, fh)
    except OSError:
        pass


if __name__ == "__main__":
    sys.exit(main())
