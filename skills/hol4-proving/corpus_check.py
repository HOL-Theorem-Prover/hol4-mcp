#!/usr/bin/env python3
"""
Mechanical check for the HOL4 guidance corpus — the "verify mechanically" step
of notes/reference_hol4_docs.md, made runnable.

Checks, across SKILL.md, notes/*.md, the hooks and their README:
  links     every [[name]] resolves to notes/<name>.md
  sections  every §Section citation resolves to a heading in the file it names
            (unqualified § means a section of feedback_hol4_mcp_proving)
  paths     every concrete ~/ or /home path that is cited exists
  hooks     every H<N> cited outside hooks/README.md is a hook that exists
  dup       no long verbatim run shared by two files (one home + a pointer)

Renaming a section is the failure this exists to catch: pointers elsewhere in
the corpus keep the old name and nothing complains.

Usage:  ./corpus_check.py [--dup-threshold N]
Exit 1 if anything is unresolved.
"""
import argparse
import itertools
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NOTES = os.path.join(HERE, "notes")
HOOKS = os.path.normpath(os.path.join(HERE, "..", "..", "hooks"))
DEFAULT_NOTE = "feedback_hol4_mcp_proving"   # what an unqualified § refers to

# A § citation ends at the first delimiter that cannot be part of a heading.
# The em-dash and the parenthesis start a continuation, not more section name.
SECTION_RE = re.compile(r"§([^,.;:()|\n·\"—]+)")
LINK_RE = re.compile(r"\[\[(\w+)\]\]")
PATH_RE = re.compile(r"`(~/[\w./-]+|/home/[\w./-]+)`")
HOOK_RE = re.compile(r"\bH(\d+)\b")
# Literal placeholders in prose ABOUT the link syntax, not real links.
PLACEHOLDERS = {"name", "link", "links"}


def norm(s):
    s = re.sub(r"[`*⛔✅⚠️⚠]", "", s)
    return " ".join(re.sub(r"[^\w>~\-/']+", " ", s).split()).lower()


def corpus_files():
    out = [os.path.join(HERE, "SKILL.md")]
    out += sorted(os.path.join(NOTES, f) for f in os.listdir(NOTES) if f.endswith(".md"))
    if os.path.isdir(HOOKS):
        out += sorted(os.path.join(HOOKS, f) for f in os.listdir(HOOKS)
                      if f.endswith((".py", ".md")))
    return out


def headings(path):
    return {norm(m.group(1)) for line in open(path, encoding="utf-8")
            for m in [re.match(r"#+\s+(.*)", line)] if m}


def in_code_span(text, pos):
    """True if `pos` sits inside a `...` span — prose ABOUT the § convention
    rather than a citation."""
    start = text.rfind("\n", 0, pos) + 1
    return text.count("`", start, pos) % 2 == 1


def owner_of(text, pos, notes):
    """Which note a § at `pos` refers to: the [[link]] earlier on its line, if
    that line has exactly one; otherwise the corpus default."""
    start = text.rfind("\n", 0, pos) + 1
    found = [n for n in LINK_RE.findall(text[start:pos]) if n in notes]
    return found[-1] if len(set(found)) == 1 else DEFAULT_NOTE


def report(kind, path, pos, text, msg):
    line = text[:pos].count("\n") + 1
    print(f"{kind:9s} {os.path.relpath(path, HERE)}:{line}  {msg}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dup-threshold", type=int, default=15,
                    help="flag a verbatim run of N+ words shared by two files")
    args = ap.parse_args()

    files = corpus_files()
    notes = {os.path.splitext(os.path.basename(p))[0]
             for p in files if os.path.dirname(p) == NOTES}
    heads = {os.path.splitext(os.path.basename(p))[0]: headings(p)
             for p in files if p.endswith(".md")}
    hooks = {m.group(1) for f in os.listdir(HOOKS)
             for m in [re.match(r"h(\d+)_.*\.py$", f)] if m} if os.path.isdir(HOOKS) else set()
    bad = 0

    for path in files:
        text = open(path, encoding="utf-8", errors="replace").read()

        for m in LINK_RE.finditer(text):
            if m.group(1) not in notes and m.group(1) not in PLACEHOLDERS:
                report("links", path, m.start(), text, f"[[{m.group(1)}]]"); bad += 1

        for m in SECTION_RE.finditer(text):
            sec = norm(m.group(1))
            if not sec or in_code_span(text, m.start()):
                continue
            own = owner_of(text, m.start(), notes)
            here = os.path.splitext(os.path.basename(path))[0]
            # a citation resolves against the named note, this file itself, or
            # the skill (sections of SKILL.md are cited from the notes too)
            pool = (heads.get(own, set()) | heads.get(here, set())
                    | heads.get("SKILL", set()))
            if not any(sec in h or h in sec for h in pool):
                report("sections", path, m.start(), text,
                       f"§{m.group(1).strip()[:50]}  (looked in {own}, {here}, SKILL)")
                bad += 1

        for m in PATH_RE.finditer(text):
            p = os.path.expanduser(m.group(1))
            if "*" in p or "<" in p or os.path.exists(p):
                continue
            report("paths", path, m.start(), text, m.group(1)); bad += 1

        # Only when the hook suite was actually found — otherwise every cited
        # H-number would be reported, which is a checker fault, not a corpus one.
        if hooks and os.path.basename(path) != "README.md":
            for m in HOOK_RE.finditer(text):
                if m.group(1) not in hooks:
                    report("hooks", path, m.start(), text, f"H{m.group(1)}"); bad += 1

    # Duplication: a long verbatim run present in two files has two homes.
    def runs(path, n):
        w = re.findall(r"[a-z_]+", re.sub(r"[`*#\-—–]", " ", open(path).read().lower()))
        return {" ".join(w[i:i + n]) for i in range(len(w) - n)}

    md = [p for p in files if p.endswith(".md") and os.path.dirname(p) != HOOKS]
    G = {p: runs(p, args.dup_threshold) for p in md}
    for a, b in itertools.combinations(md, 2):
        for s in sorted(G[a] & G[b])[:2]:
            print(f"dup       {os.path.relpath(a, HERE)} <-> {os.path.relpath(b, HERE)}"
                  f"\n            \"{s[:90]}…\"")
            bad += 1

    print(f"-- {bad} issue(s) across {len(files)} file(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
