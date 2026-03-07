#!/usr/bin/env python3
"""Find dead (unreferenced) definitions and theorems in a HOL4 project.

Parses *Theory.sig files (build artifacts) to discover what each theory exports,
then scans *Script.sml source files to find what's actually used. Reports
definitions and theorems that are never referenced outside their own theory,
with transitive propagation (if B uses A, but B is dead, A is also dead).

Usage:
    python find_dead_hol.py <project_root> [--include-auto] [--json] [--by-theory]

    --include-auto    Include auto-generated names (datatype boilerplate, etc.)
    --external-only   Only show names unused anywhere (skip internal-only)
    --json            Output as JSON
    --by-theory       Group output by theory
"""

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path


# ---------------------------------------------------------------------------
# Auto-generated name filters
# ---------------------------------------------------------------------------

AUTO_SUFFIXES = {
    # Datatype boilerplate
    "_TY_DEF", "_case_def", "_case_cong", "_case_eq",
    "_Axiom", "_induction", "_nchotomy",
    "_11", "_distinct",
    "_BIJ", "_CASE",
    "_size_def",
    # ind principles from Define
    "_ind",
    # Record type boilerplate
    "_accessors", "_accfupds",
    "_component_equality",
    "_fn_updates", "_fupdcanon", "_fupdcanon_comp",
    "_fupdfupds", "_fupdfupds_comp",
    "_updates_eq_literal",
    "_literal_nchotomy",
}

AUTO_PATTERNS = [
    re.compile(r"^num2\w+_\w+$"),
    re.compile(r"^\w+2num_\w+$"),
    re.compile(r"^datatype_\w+$"),
    re.compile(r"^FORALL_\w+$"),
    re.compile(r"^EXISTS_\w+$"),
    re.compile(r"^recordtype_\w+_seldef_"),
    re.compile(r"^\w+_primitive$"),
    re.compile(r"^\w+_primitive_def$"),
    re.compile(r"^\w+_extract\d+$"),
    re.compile(r"^\w+_extract\d+_def$"),
    re.compile(r"^\w+_AUX$"),
    re.compile(r"^\w+_AUX_def$"),
    re.compile(r"^\w+_UNION_AUX$"),
    re.compile(r"^\w+_UNION_extract\d+$"),
    re.compile(r"^\w+_pre_cases$"),
    re.compile(r"^\w+_pre_rules$"),
    re.compile(r"^\w+_pre_strongind$"),
    re.compile(r"^\w+_pre_ind$"),
    re.compile(r"^cv_\w+_def$"),
    re.compile(r"^cv_\w+_thm$"),
    re.compile(r"^\w+_ho$"),
    re.compile(r"^\w+_EQ_\w+$"),
    re.compile(r"^MAP_\w+_def$"),
    re.compile(r"^MAP_\w+_ho$"),
    re.compile(r"^FILTER_\w+_def$"),
    re.compile(r"^FILTER_\w+_ho$"),
    re.compile(r"^\w+_lam_\w+$"),
]


def is_auto_generated(name: str) -> bool:
    for suffix in AUTO_SUFFIXES:
        if name.endswith(suffix):
            return True
    for pattern in AUTO_PATTERNS:
        if pattern.match(name):
            return True
    return False


# ---------------------------------------------------------------------------
# File discovery
# ---------------------------------------------------------------------------

EXCLUDE_DIRS = {"worktrees", ".hol", ".git", "node_modules"}


def _should_exclude(p: Path) -> bool:
    return bool(EXCLUDE_DIRS & set(p.parts))


def find_sig_files(root: Path) -> list[Path]:
    """Find all *Theory.sig files under .hol/objs directories."""
    return sorted(
        p for p in root.rglob("*.hol/objs/*Theory.sig")
        if "worktrees" not in p.parts
    )


def find_script_files(root: Path) -> list[Path]:
    return sorted(
        p for p in root.rglob("*Script.sml")
        if not _should_exclude(p)
    )


def find_sml_files(root: Path) -> list[Path]:
    """Non-Script .sml files (libraries, test runners, etc.)."""
    return sorted(
        p for p in root.rglob("*.sml")
        if not _should_exclude(p) and not p.name.endswith("Script.sml")
    )


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def parse_sig_file(sig_path: Path) -> tuple[str, list[str], list[str], list[str]]:
    """Parse a *Theory.sig -> (theory_name, parents, definitions, theorems)."""
    text = sig_path.read_text()

    m = re.match(r"signature\s+(\w+)Theory\s*=", text)
    if not m:
        return None, [], [], []
    theory_name = m.group(1)

    parents = re.findall(r'\[(\w+)\]\s+Parent theory of', text)

    # Only parse val declarations before the docs block
    doc_start = text.find("\n(*\n")
    header = text[:doc_start] if doc_start > 0 else text

    defs, thms = [], []
    section = None
    for line in header.splitlines():
        stripped = line.strip()
        if stripped == "(*  Definitions  *)":
            section = "def"
        elif stripped == "(*  Theorems  *)":
            section = "thm"
        m = re.match(r"val\s+(\w+)\s*:\s*thm", stripped)
        if m:
            name = m.group(1)
            if section == "def":
                defs.append(name)
            else:
                thms.append(name)

    return theory_name, parents, defs, thms


def extract_theory_from_script(script_path: Path) -> str | None:
    try:
        text = script_path.read_text()
    except Exception:
        return None
    m = re.search(r"^Theory\s+(\w+)", text, re.MULTILINE)
    if m:
        return m.group(1)
    name = script_path.stem
    return name[:-6] if name.endswith("Script") else None


def scan_references(file_path: Path, all_names: set[str]) -> set[str]:
    """Scan a file for references to known names (strips SML nested comments)."""
    try:
        text = file_path.read_text()
    except Exception:
        return set()

    # Strip nested (* ... *) comments
    cleaned = []
    i, depth = 0, 0
    while i < len(text):
        if text[i:i+2] == "(*":
            depth += 1; i += 2
        elif text[i:i+2] == "*)" and depth > 0:
            depth -= 1; i += 2
        elif depth == 0:
            cleaned.append(text[i]); i += 1
        else:
            i += 1
    text = "".join(cleaned)

    tokens = set(re.findall(r'\b(\w+)\b', text))
    # Also handle qualified: fooTheory.bar_def
    tokens.update(re.findall(r'\b\w+Theory\.(\w+)\b', text))
    return tokens & all_names


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Find dead (unreferenced) HOL4 definitions and theorems"
    )
    parser.add_argument("root", type=Path, help="Project root directory")
    parser.add_argument("--include-auto", action="store_true",
                        help="Include auto-generated boilerplate")
    parser.add_argument("--external-only", action="store_true",
                        help="Only show names unused anywhere (skip internal-only)")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--by-theory", action="store_true", help="Group by theory")
    parser.add_argument("--verbose", "-v", action="store_true")
    parser.add_argument("--ignore-stale", action="store_true",
                        help="Don't skip stale/orphan .sig files")
    args = parser.parse_args()

    root = args.root.resolve()
    if not root.is_dir():
        print(f"Error: {root} is not a directory", file=sys.stderr)
        sys.exit(1)

    # --- 1. Parse .sig files ---
    sig_files = find_sig_files(root)
    if not sig_files:
        print(f"No *Theory.sig files found under {root}", file=sys.stderr)
        print("Has the project been built? (run Holmake first)", file=sys.stderr)
        sys.exit(1)

    # theory_name -> {name: "def"|"thm"}
    theories: dict[str, dict[str, str]] = {}
    theory_parents: dict[str, list[str]] = {}
    theory_sig_path: dict[str, Path] = {}  # track sig path for staleness check

    for sig_path in sig_files:
        theory_name, parents, defs, thms = parse_sig_file(sig_path)
        if theory_name is None:
            continue
        exports = {}
        for d in defs:
            exports[d] = "def"
        for t in thms:
            exports[t] = "thm"
        theories[theory_name] = exports
        theory_parents[theory_name] = parents
        theory_sig_path[theory_name] = sig_path

    # --- Staleness check ---
    # Cross-reference sigs against Script files to detect stale builds.
    if not args.ignore_stale:
        script_files_early = find_script_files(root)
        script_map: dict[str, Path] = {}
        for sp in script_files_early:
            t = extract_theory_from_script(sp)
            if t:
                script_map[t] = sp

        stale = []
        for theory_name in list(theories.keys()):
            script = script_map.get(theory_name)
            if script is None:
                stale.append((theory_name, "orphan"))
                continue
            sig_path = theory_sig_path.get(theory_name)
            if sig_path and script.stat().st_mtime > sig_path.stat().st_mtime:
                stale.append((theory_name, "stale"))

        if stale:
            for t, reason in stale:
                tag = "no Script (orphan build artifact)" if reason == "orphan" \
                    else "Script newer than sig (needs rebuild)"
                print(f"  SKIP {t}Theory: {tag}", file=sys.stderr)
                del theories[t]
                if t in theory_parents:
                    del theory_parents[t]
            print(f"Skipped {len(stale)} stale/orphan theories "
                  f"(use --ignore-stale to include)", file=sys.stderr)

    if args.verbose:
        total = sum(len(v) for v in theories.values())
        print(f"Found {len(sig_files)} sigs, {total} exports, "
              f"{len(theories)} theories", file=sys.stderr)

    # --- 2. Build name universe (after auto-filtering) ---
    all_exported: dict[str, tuple[str, str]] = {}  # name -> (theory, kind)
    for theory_name, exports in theories.items():
        for name, kind in exports.items():
            if not args.include_auto and is_auto_generated(name):
                continue
            all_exported[name] = (theory_name, kind)

    all_names = set(all_exported.keys())

    # --- 3. Scan files for references ---
    script_files = find_script_files(root)
    sml_files = find_sml_files(root)

    if args.verbose:
        print(f"Scanning {len(script_files)} Scripts + {len(sml_files)} SML files",
              file=sys.stderr)

    # name_refs[name] = set of theory names (or __sml__*) that reference it
    name_refs: dict[str, set[str]] = defaultdict(set)

    for script_path in script_files:
        theory = extract_theory_from_script(script_path)
        for name in scan_references(script_path, all_names):
            if theory:
                name_refs[name].add(theory)

    for sml_path in sml_files:
        for name in scan_references(sml_path, all_names):
            name_refs[name].add(f"__sml__{sml_path.name}")

    # --- 4. Transitive dead code analysis ---
    #
    # We build a name-level dependency graph (approximate):
    #   depends_on[N] = set of names that N's theory script references externally
    # Then propagate aliveness from roots (leaf theory exports + SML refs).
    #
    # Approximation: all exports of theory T depend on all external names
    # mentioned in T's Script file. This is coarse (a dead theorem in T
    # keeps alive all of T's external deps) but conservative — it won't
    # produce false positives (won't call alive code dead).

    # For each theory, cache its script's external references
    theory_ext_refs: dict[str, set[str]] = {}
    for script_path in script_files:
        theory = extract_theory_from_script(script_path)
        if not theory or theory not in theories:
            continue
        refs = scan_references(script_path, all_names)
        own = set(theories[theory].keys())
        theory_ext_refs[theory] = (refs & all_names) - own

    # depends_on[name] = external names that name's theory references
    depends_on: dict[str, set[str]] = {}
    for name, (theory, _) in all_exported.items():
        depends_on[name] = theory_ext_refs.get(theory, set())

    # Determine alive theories via ancestor graph.
    # A theory is alive if it's a leaf (top-level goal) or an ancestor of one.
    has_children: set[str] = set()
    for t, parents in theory_parents.items():
        if t in theories:
            for p in parents:
                has_children.add(p)
    leaf_theories = set(theories.keys()) - has_children

    # BFS from leaves backwards through ancestor graph to find all alive theories
    alive_theories: set[str] = set()
    theory_children: dict[str, set[str]] = defaultdict(set)
    for t, parents in theory_parents.items():
        if t in theories:
            for p in parents:
                if p in theories:
                    theory_children[p].add(t)

    # All theories reachable from a leaf (upward through ancestors) are alive
    worklist = list(leaf_theories)
    while worklist:
        t = worklist.pop()
        if t in alive_theories:
            continue
        alive_theories.add(t)
        for p in theory_parents.get(t, []):
            if p in theories and p not in alive_theories:
                worklist.append(p)

    alive: set[str] = set()

    # Leaf theory exports are roots (top-level goals of the project)
    for t in leaf_theories:
        for name in theories[t]:
            if name in all_exported:
                alive.add(name)

    # SML-referenced names are roots
    for name in all_exported:
        for ref_src in name_refs.get(name, set()):
            if ref_src.startswith("__sml__") or ref_src not in theories:
                alive.add(name)
                break

    # Names referenced by alive theories (from their Script files) are alive
    for name in all_exported:
        theory = all_exported[name][0]
        refs = name_refs.get(name, set())
        # Alive if referenced by any alive theory other than self
        for ref_src in refs:
            if ref_src != theory and ref_src in alive_theories:
                alive.add(name)
                break

    if args.verbose:
        print(f"Roots: {len(leaf_theories)} leaf theories, "
              f"{len(alive_theories)} alive theories, "
              f"{len(alive)} seed alive names", file=sys.stderr)

    # Propagate: alive names keep their dependencies alive
    worklist = list(alive)
    while worklist:
        name = worklist.pop()
        for dep in depends_on.get(name, set()):
            if dep not in alive:
                alive.add(dep)
                worklist.append(dep)

    if args.verbose:
        print(f"After propagation: {len(alive)} alive, "
              f"{len(all_exported) - len(alive)} dead", file=sys.stderr)

    # --- 5. Classify dead names ---
    dead: dict[str, list[tuple[str, str, str]]] = defaultdict(list)

    for name, (theory_name, kind) in all_exported.items():
        if name in alive:
            continue

        referencing = name_refs.get(name, set())
        self_refs = theory_name in referencing

        if args.external_only and self_refs:
            continue

        status = "self-only" if self_refs else "nowhere"
        dead[theory_name].append((name, kind, status))

    for t in dead:
        dead[t].sort(key=lambda x: x[0])

    # --- 6. Output ---
    total_dead = sum(len(v) for v in dead.values())
    n_nowhere = sum(1 for items in dead.values() for _, _, s in items if s == "nowhere")
    n_selfonly = total_dead - n_nowhere

    if args.json:
        import json
        output = {
            "total_dead": total_dead,
            "nowhere": n_nowhere,
            "self_only": n_selfonly,
            "by_theory": {
                t: [{"name": n, "kind": k, "status": s} for n, k, s in items]
                for t, items in sorted(dead.items())
            }
        }
        print(json.dumps(output, indent=2))
        return

    if total_dead == 0:
        print("No dead code found!")
        return

    print(f"Found {total_dead} potentially dead names "
          f"({n_nowhere} unused anywhere, {n_selfonly} internal-only):\n")

    if args.by_theory:
        for theory_name, items in sorted(dead.items()):
            if not items:
                continue
            print(f"  {theory_name}Theory:")
            for name, kind, status in items:
                tag = "DEF" if kind == "def" else "THM"
                marker = " ◌" if status == "self-only" else " ✗"
                print(f"   {marker} [{tag}] {name}")
            print()
    else:
        flat = []
        for theory_name, items in dead.items():
            for name, kind, status in items:
                flat.append((theory_name, name, kind, status))
        flat.sort(key=lambda x: (x[3] != "nowhere", x[1]))

        for theory_name, name, kind, status in flat:
            tag = "DEF" if kind == "def" else "THM"
            marker = "◌" if status == "self-only" else "✗"
            print(f"  {marker} [{tag}] {theory_name}Theory.{name}")

    n_defs = sum(1 for items in dead.values() for _, k, _ in items if k == "def")
    n_thms = sum(1 for items in dead.values() for _, k, _ in items if k == "thm")
    print(f"\nSummary: {n_defs} definitions, {n_thms} theorems")
    print(f"Legend: ✗ = unused anywhere, ◌ = internal-only (not referenced externally)")
    if not args.include_auto:
        print(f"(Use --include-auto to also show auto-generated boilerplate)")


if __name__ == "__main__":
    main()
