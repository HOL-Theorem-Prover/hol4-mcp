"""Read-only reconstruction of the proof files a simple Git commit records.

Never stage, write objects, run filters, or execute the supplied shell command.
Ambiguous shell/interactive forms require separate staging and commit calls.
"""
from pathlib import Path
import re
import shlex
import subprocess


class AuditUnavailable(ValueError):
    pass


def git(args, cwd, *, optional=False):
    proc = subprocess.run(["git", *args], cwd=cwd, capture_output=True, timeout=10)
    if proc.returncode:
        if optional:
            return b""
        raise AuditUnavailable(proc.stderr.decode(errors="replace").strip())
    return proc.stdout


def _parts(command):
    """The simple commands of a shell command line, split at control operators."""
    lexer = shlex.shlex(command, posix=True, punctuation_chars=";&|\n")
    lexer.whitespace = " \t\r"
    lexer.whitespace_split = True
    parts, part = [], []
    for token in lexer:
        if token in (";", "&&", "||", "|", "&", "\n"):
            if part:
                parts.append(part)
            part = []
        else:
            part.append(token)
    if part:
        parts.append(part)
    return parts


def repo_hint(command, cwd):
    """Best-effort directory the commit addresses: a `cd`, a `git -C`, else
    `cwd`. Never raises; it only decides whether the audit applies at all."""
    try:
        parts = _parts(command)
    except ValueError:
        return cwd
    for words in parts:
        if words[0] == "cd" and len(words) == 2:
            cwd = str(Path(cwd, words[1]).resolve())
        elif words[0] == "git":
            where, i = cwd, 1
            while i < len(words) and words[i].startswith("-"):
                if words[i] == "-C" and i + 1 < len(words):
                    where = str(Path(where, words[i + 1]).resolve())
                    i += 2
                else:
                    i += 1
            if "commit" in words[i:]:
                return where
    return cwd


def tracks_scripts(cwd):
    """True if the repository at `cwd` tracks any `*Script.sml`."""
    try:
        proc = subprocess.run(["git", "ls-files", "-z", "--",
                               ":(top,glob)**/*Script.sml"],
                              cwd=cwd, capture_output=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return False
    return proc.returncode == 0 and bool(proc.stdout.strip(b"\0"))


def commit_args(command, cwd):
    """Return (Git cwd, commit argv), or None for a non-commit command."""
    parts = _parts(command)
    found = []
    preceding = False
    for words in parts:
        if words[0] == "cd" and len(words) == 2 and not preceding:
            cwd = str(Path(cwd, words[1]).resolve())
            continue
        if words[0] != "git":
            preceding = True
            continue
        where, i = cwd, 1
        while i < len(words) and words[i].startswith("-"):
            flag = words[i]
            if flag == "-C" and i + 1 < len(words):
                where = str(Path(where, words[i + 1]).resolve())
                i += 2
            elif flag in ("--no-pager", "--no-optional-locks"):
                i += 1
            else:
                if "commit" in words[i:]:
                    raise AuditUnavailable("unsupported Git global options; use a plain commit call")
                break
        if i < len(words) and words[i] == "commit":
            if preceding or found or len(parts) > parts.index(words) + 1:
                raise AuditUnavailable("run staging/other commands and git commit in separate tool calls")
            if any("$" in w or "`" in w for w in words[:i]):
                raise AuditUnavailable("use literal repository paths for the commit audit")
            found.append((where, words[i + 1:]))
        else:
            preceding = True
    return found[0] if found else None


def selection(args):
    """Git commit defaults to --only when paths are supplied."""
    mode, paths, i = "index", [], 0
    value_options = {"-m", "--message", "-F", "--file", "-C", "--reuse-message",
                     "-c", "--reedit-message", "--author", "--date", "--cleanup",
                     "--fixup", "--squash", "--trailer", "-t", "--template"}
    plain_options = {"--amend", "--no-edit", "--allow-empty", "--allow-empty-message",
                     "--no-verify", "--no-gpg-sign", "--signoff", "--quiet", "--verbose",
                     "--no-status", "--status", "--reset-author"}
    while i < len(args):
        arg = args[i]
        if arg == "--":
            paths.extend(args[i + 1:])
            break
        cluster = re.fullmatch(r"-([aoiqvsn]+)([mFcCt])(.*)", arg)
        if cluster:
            for flag in cluster[1]:
                if flag in "aoi":
                    mode = {"a": "all", "o": "only", "i": "include"}[flag]
            if not cluster[3]:
                if i + 1 == len(args):
                    raise AuditUnavailable(f"missing argument to -{cluster[2]}")
                i += 1
            i += 1
            continue
        if arg in value_options:
            if i + 1 == len(args):
                raise AuditUnavailable(f"missing argument to {arg}")
            i += 2
            continue
        if any(arg.startswith(option + "=") for option in value_options if option.startswith("--")):
            pass
        elif arg in ("--all", "--only", "--include"):
            mode = {"--all": "all", "--only": "only", "--include": "include"}[arg]
        elif arg in plain_options or arg.startswith("--gpg-sign="):
            pass
        elif re.fullmatch(r"-[aoiqvsn]+", arg):
            for flag in arg[1:]:
                if flag in "aoi":
                    mode = {"a": "all", "o": "only", "i": "include"}[flag]
        elif arg.startswith(("-m", "-F", "-S")) and len(arg) > 2:
            pass
        elif arg.startswith("-"):
            raise AuditUnavailable(f"unsupported commit option {arg}; stage separately and commit the index")
        else:
            paths.append(arg)
        i += 1
    if paths and mode == "index":
        mode = "only"
    if any("$" in p or "`" in p for p in paths):
        raise AuditUnavailable("use literal pathspecs for the commit audit")
    return mode, paths


def snapshot(command, cwd):
    parsed = commit_args(command, cwd)
    if parsed is None:
        return None
    cwd, args = parsed
    root = git(["rev-parse", "--show-toplevel"], cwd).decode().strip()
    mode, paths = selection(args)
    head = {}
    for entry in git(["ls-tree", "-rz", "HEAD"], root, optional=True).split(b"\0"):
        if entry:
            meta, name = entry.split(b"\t", 1)
            head[name.decode()] = meta.split()[2].decode()
    index = {}
    for entry in git(["ls-files", "--stage", "-z"], root).split(b"\0"):
        if entry:
            meta, name = entry.split(b"\t", 1)
            _mode, oid, stage = meta.split()
            if stage != b"0":
                raise AuditUnavailable("the index has unresolved merge entries")
            index[name.decode()] = oid.decode()
    selected = set()
    if paths:
        selected = {p.decode() for p in git(
            ["ls-files", "--full-name", "-z", "--", *paths], cwd).split(b"\0") if p}
    overlay = set(index) if mode == "all" else selected if mode in ("only", "include") else set()
    prospective = dict(head if mode == "only" else index)
    changed = {p.decode() for p in git(
        ["diff", "--cached", "--name-only", "--no-renames", "-z"], root).split(b"\0") if p}
    if mode == "all":
        changed.update(p.decode() for p in git(
            ["diff", "--name-only", "--no-renames", "-z"], root).split(b"\0") if p)
    candidates = selected if mode == "only" else changed | selected
    files = {}
    for path in sorted(candidates):
        if not path.endswith("Script.sml"):
            continue
        before = (git(["cat-file", "blob", head[path]], root).decode("utf-8", errors="replace")
                  if path in head else "")
        if path in overlay:
            # Git clean filters and encodings may produce different bytes.
            # Do not run contributor-controlled filters during a read-only audit.
            attrs = git(["check-attr", "filter", "working-tree-encoding", "--", path], root).decode()
            if any(not line.endswith((": unspecified", ": unset")) for line in attrs.splitlines()):
                raise AuditUnavailable(f"{path} has Git content filters; stage it and commit the index")
            try:
                after = Path(root, path).read_text(encoding="utf-8", errors="replace")
            except FileNotFoundError:
                after = ""
        else:
            after = (git(["cat-file", "blob", prospective[path]], root).decode("utf-8", errors="replace")
                     if path in prospective else "")
        if before != after:
            files[path] = (before, after)
    return root, files
