"""Coordinate MCP builds' artifacts across server lifetimes.

Holmake locks competing writers, but can skip an existing partial dependency.
Builds are compared per artifact unit — the files one Holmake job writes for a
target (fooTheory.sml/.sig/.dat/.ui/.uo) — so independent theories in one
directory build concurrently. Read/read overlap is safe; a write/read or
write/write overlap on a unit is refused. Locks cover cooperating servers on
the same host/user; undeclared outputs and plain external Holmake processes
remain outside this protocol.

Everything the coordination keeps lives under one per-user host directory
(`storage_root`), never in a project tree: lock files, output records,
detached-job records with their logs, discovery traces.

When a build ends, each of its outputs is judged on its own: a job Holmake's
monitor reported as finished wrote complete files even if a later job failed.
A detached job also leaves a record of itself and, through its wrapper, the
exit status Holmake ends with, so a server started after the one that
launched it can report it, cancel it, and apply its outcome.
"""

from dataclasses import dataclass, field
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import stat
import sys
import tempfile
import time
import uuid

from .hol_session import HOLDIR


def _stamp(path):
    try:
        stat = path.stat()
        return stat.st_mtime_ns, stat.st_ctime_ns, stat.st_size, stat.st_ino
    except FileNotFoundError:
        return None


def _artifact_paths(path):
    """Graph names are logical; Poly/ML HOL stores generated files in objs.

    Keep both layouts for older HOL versions and ordinary shell recipes.
    sigobj files already have their physical names.
    """
    yield path.resolve()
    generated = path.suffix in {".uo", ".ui"} or (
        path.stem.endswith("Theory") and len(path.stem) > len("Theory")
        and path.suffix in {".sml", ".sig", ".dat"})
    already_physical = path.parent.name == "objs" and path.parent.parent.name == ".hol"
    if generated and path.parent.name != "sigobj" and not already_physical:
        yield (path.parent / ".hol" / "objs" / path.name).resolve()


@dataclass
class BuildClaim:
    workdir: Path
    reads: set[Path]
    outputs: set[Path]
    token: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    proc: object = None
    detached: bool = False
    before: dict = field(default_factory=dict)
    preflight_output: str = ""
    lock_fds: list[int] = field(default_factory=list)
    state_error: str = ""
    clean: bool = False
    # Outputs by the name Holmake's monitor prints for the job writing them,
    # the outputs Holmake compiles in its own process (no job line), and each
    # job's first command line as a sequential build echoes it.
    tags: dict = field(default_factory=dict)
    in_process: set = field(default_factory=set)
    commands: dict = field(default_factory=dict)
    read_units: set = field(default_factory=set)
    write_units: set = field(default_factory=set)
    created: float = field(default_factory=time.time)
    log: Path | None = None

    @property
    def label(self):
        return f"{'job' if self.detached else 'build'}={self.token} workdir={self.workdir}"

    def release_locks(self):
        # Closing our copy preserves flock protection in an orphaned Holmake
        # process that inherited the same open file description via pass_fds.
        for fd in self.lock_fds:
            os.close(fd)
        self.lock_fds.clear()


def claim_from_graph(output: str, workdir: Path, target: str | None) -> BuildClaim:
    # Pre-exec commands may print before the graph. JSON itself starts in
    # column zero; dependency lists inside it never do.
    start = output.rfind("\n[") + 1
    nodes = json.loads(output[start:])
    if not isinstance(nodes, list) or any(
        not isinstance(node, dict) or not {"node_id", "target", "dependencies",
                                           "needs_rebuild", "command"} <= node.keys()
        for node in nodes
    ):
        raise ValueError("Holmake returned an unsupported dependency graph")
    graph = {node["node_id"]: node for node in nodes}
    nominal = {key: workdir / node["target"] for key, node in graph.items()}
    paths = {key: path.resolve() for key, path in nominal.items()}
    clean = target in {"clean", "cleanDeps", "cleanAll"}
    if target and not clean:
        requested = (workdir / target).resolve()
        roots = [key for key, path in paths.items() if path == requested]
        if not roots:
            roots = [key for key, path in paths.items() if path == Path(str(requested) + ".uo")]
        if not roots:
            raise ValueError(f"target {target!r} is absent from the dependency graph")
    else:
        roots = list(graph)
    selected = set()
    pending = roots[:]
    while pending:
        key = pending.pop()
        if key in selected:
            continue
        selected.add(key)
        pending.extend(graph[key]["dependencies"])
    reads = {path for key in selected for path in _artifact_paths(nominal[key])}
    outputs = {path for key in selected
               if graph[key]["command"] and graph[key]["needs_rebuild"]
               for path in _artifact_paths(nominal[key])}
    if clean:
        # Holmakefile CLINE_OPTIONS may make cleaning recursive. Reserve the
        # whole discovered closure so it cannot delete a peer's interfaces.
        outputs = {path for key in selected if graph[key]["command"]
                   for path in _artifact_paths(nominal[key])}
    claim = BuildClaim(workdir, reads, outputs)
    claim.clean = clean
    claim.preflight_output = output[:start]
    tag_dirs = {}
    for key in selected:
        node = graph[key]
        if not (node["command"] and node["needs_rebuild"]):
            continue
        command = str(node["command"])
        tag = job_tag(nominal[key], command)
        paths = set(_artifact_paths(nominal[key]))
        if tag is None:
            claim.in_process |= paths
        else:
            claim.tags.setdefault(tag, set()).update(paths)
            tag_dirs.setdefault(tag, set()).add(paths_dir(nominal[key]))
            if not command.startswith("BIC_"):
                first = command.split("\n", 1)[0].strip()
                claim.commands[tag] = None if first.startswith("@") else first
    for tag, dirs in tag_dirs.items():
        if len(dirs) > 1:
            del claim.tags[tag]   # the printed name alone cannot tell them apart
            claim.commands.pop(tag, None)
    return claim


def paths_dir(path):
    return path.resolve().parent


def artifact_unit(path):
    """(directory, stem): the files one Holmake job writes for a target —
    fooTheory.sml/.sig/.dat/.ui/.uo in the theory's directory or its
    .hol/objs — which is the granularity at which builds can conflict."""
    directory = path.parent
    if directory.name == "objs" and directory.parent.name == ".hol":
        directory = directory.parent.parent
    return (directory, path.name.split(".")[0])


def job_tag(target: Path, command: str) -> str | None:
    """The name Holmake's monitor prints for the job that writes ``target``,
    or None when Holmake compiles it in its own process and prints nothing.
    One BIC_Build job writes a theory's .sml, .sig and .dat under the stem."""
    if command == "BIC_Compile":
        return None
    if command.startswith("BIC_Build"):
        return target.stem
    name = target.name
    return name[:-4] if name.endswith(".sml") else name


# Holmake's monitor, when stdout is not a terminal, prints one line as a job
# starts and one as it ends: `<tag> [dir] (<time>) [k/n] <verdict>`. The
# columns are space-padded; the padding can be absent (a long dir abuts the
# time, the counter abuts the verdict), and the dir may itself contain
# parentheses, as in `$(CAKEMLDIR)/...`.
_JOB_START_RE = re.compile(r"^Starting work on (\S+)\s*$")
_JOB_RESULT_RE = re.compile(
    r"^(?P<tag>\S+)(?:\s+\S*?)?\s*\([^)]*\)\s*(?:\[[^\]]*\])?\s*"
    r"(?P<verdict>OK|CHEATED|F-CHEAT|CACHED|RETRY|FAIL<[^>]*>)\s*$")
_SUCCESS_VERDICTS = {"OK", "CHEATED", "F-CHEAT", "CACHED"}
# A sequential build (-j1) has no monitor. After each theory script it ran
# successfully it prints `Holmake: [k/n] <thy>` (or `[↓m] <thy>` past 99
# theories), naming the job its monitor would print as `<thy>Theory`; shell
# command targets get no such line.
_J1_THEORY_DONE_RE = re.compile(r"^(?:Holmake: )?\[(?:\d+/\d+|↓\d+)\] (\S+)\s*$")


def job_verdicts(output, commands=None):
    """Each job's final state from a build's output: a verdict word, or
    "started" for a job the monitor opened and never closed.

    A sequential build (-j1) has no monitor. Its theories get progress lines;
    its shell command targets only echo their command, so one of those is
    taken as succeeded once a later target demonstrably began — with `--qof`
    Holmake moves on only after success. A quiet (`@`) recipe echoes nothing
    and is never certified this way.
    """
    state = {}
    lines = output.splitlines()
    for line in lines:
        start = _JOB_START_RE.match(line)
        if start:
            state[start.group(1)] = "started"
            continue
        result = _JOB_RESULT_RE.match(line)
        if result:
            state[result.group("tag")] = result.group("verdict")
            continue
        theory = _J1_THEORY_DONE_RE.match(line)
        if theory:
            state[theory.group(1) + "Theory"] = "OK"
    if commands and not any(_JOB_START_RE.match(line) for line in lines):
        wanted = {command: tag for tag, command in commands.items() if command}
        events = []
        for line in lines:
            stripped = line.strip()
            if stripped in wanted:
                events.append(wanted[stripped])
            elif (_J1_THEORY_DONE_RE.match(stripped)
                  or stripped.startswith(("Holmake: Linking", "Holmake: Failed script build"))):
                events.append(None)
        for index, tag in enumerate(events[:-1]):
            if tag is not None and tag not in state:
                state[tag] = "OK"
    return state


def _sequential_script_was_running(output):
    """True when a sequential build's last event is a theory script starting
    (`Holmake: Linking …`) with no completion line after it. Holmake runs one
    graph node at a time and prints that line inside the script's own node,
    so no in-process compile was running when the build stopped."""
    lines = output.splitlines()
    if any(_JOB_START_RE.match(line) for line in lines):
        return False
    last = None
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("Holmake: Linking "):
            last = "script"
        elif (_J1_THEORY_DONE_RE.match(stripped)
              or stripped.startswith("Holmake: Failed script build")):
            last = "done"
    return last == "script"


def completed_outputs(tags, in_process, output, returncode, commands=None):
    """Outputs a build that did not succeed as a whole nevertheless finished.

    A monitored job's outputs are complete when its last line is a success
    verdict and no later start line reopened it; in a sequential build, a
    theory's are complete once its progress line follows and a shell target's
    once a later target began. Holmake's in-process compiles are complete
    when Holmake exited of its own accord (a small positive status): it
    writes them one at a time and nothing interrupted it. They are also
    complete when a sequential build stopped while a theory script ran. A
    signal — cancellation, a timeout kill, a vanished controller — otherwise
    certifies nothing beyond the verdict lines.
    """
    state = job_verdicts(output, commands)
    done = set()
    for tag, paths in tags.items():
        if state.get(tag) in _SUCCESS_VERDICTS:
            done.update(paths)
    if ((returncode is not None and 0 < returncode < 128)
            or _sequential_script_was_running(output)):
        done.update(in_process)
    return done


def storage_root():
    """The per-user home of everything the coordination keeps: /var/tmp
    survives reboots, and the identity depends on neither a client's private
    TMPDIR nor its HOME, so every server of one user meets the same files."""
    root = Path("/var/tmp") / f"hol4-mcp-{os.getuid()}"
    root.mkdir(mode=0o700, exist_ok=True)
    info = root.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
        raise ValueError(f"Coordination directory is not private and owned by this user: {root}")
    return root


def _storage(kind):
    directory = storage_root() / kind
    directory.mkdir(mode=0o700, exist_ok=True)
    return directory


def builds_directory():
    """Detached jobs' logs and exit-status files."""
    return _storage("builds")


def discovery_directory():
    """Opt-in discovery traces and their context files."""
    return _storage("discovery")


def _unit_directory(path):
    directory = path.parent
    if directory.name == "objs" and directory.parent.name == ".hol":
        directory = directory.parent.parent
    return directory


def _state_directory(path):
    return _storage("state") / hashlib.sha256(str(_unit_directory(path)).encode()).hexdigest()


def _legacy_state_directory(path):
    """Where records lived inside the project tree; read, never written."""
    return _unit_directory(path) / ".hol4-mcp" / "build-state"


def _state_file(path, phase):
    digest = hashlib.sha256(str(path).encode()).hexdigest()
    return _state_directory(path) / f"{digest}.{phase}.json"


def _legacy_state_file(path, phase):
    digest = hashlib.sha256(str(path).encode()).hexdigest()
    return _legacy_state_directory(path) / f"{digest}.{phase}.json"


def _unlink_state(path, phase):
    _state_file(path, phase).unlink(missing_ok=True)
    _legacy_state_file(path, phase).unlink(missing_ok=True)


def _read_state(path, phase):
    for location in (_state_file(path, phase), _legacy_state_file(path, phase)):
        try:
            data = json.loads(location.read_text())
            break
        except FileNotFoundError:
            continue
    else:
        return None
    if not isinstance(data, dict) or not {"path", "stamp", "label", "token"} <= data.keys():
        raise ValueError(f"Invalid build coordination record for {path}")
    if data["path"] != str(path):
        raise ValueError(f"Mismatched build coordination record for {path}")
    return data


def _record_stamp(record):
    return tuple(record["stamp"]) if record["stamp"] is not None else None


def _write_state(path, phase, stamp, claim, returncode=None):
    """``returncode`` is the exit status this server observed for the build
    that left a failed output; absent when no exit status was seen."""
    destination = _state_file(path, phase)
    destination.parent.mkdir(parents=True, mode=0o700, exist_ok=True)
    record = {"path": str(path), "stamp": stamp, "label": claim.label, "token": claim.token}
    if returncode is not None:
        record["returncode"] = returncode
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8",
                                         dir=destination.parent, delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(record, stream)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def _suspect(path, adopt=True):
    stamp = _stamp(path)
    if stamp is None:
        return None
    failed = _read_state(path, "failed")
    if failed is not None and stamp == _record_stamp(failed):
        return failed
    running = _read_state(path, "running")
    if running is not None and stamp != _record_stamp(running):
        # The lock is free, but the controller never certified completion.
        # Its job may have left an exit status behind for us to apply.
        if adopt and adopt_finished_job(running["token"]):
            return _suspect(path, adopt=False)
        return running
    return None


# --- detached job records: survive the server that started the job ---------

_TOKEN_RE = re.compile(r"^[0-9a-f]{12}$")


def jobs_directory():
    return _storage("jobs")


BUILD_LOGS_KEPT = 20


def prune_builds(keep=BUILD_LOGS_KEPT):
    """Keep the logs and exit files of the newest ``keep`` finalized jobs; a
    job still running, or finished but never reported, keeps its files."""
    finalized = []
    for record_path in jobs_directory().glob("*.json"):
        try:
            record = json.loads(record_path.read_text())
            if record.get("finalized"):
                finalized.append((record["finalized"]["at"], record))
        except (OSError, ValueError, KeyError, TypeError):
            continue
    finalized.sort(key=lambda item: item[0], reverse=True)
    for _, record in finalized[keep:]:
        for key in ("log", "exit_file"):
            try:
                Path(record[key]).unlink(missing_ok=True)
            except (OSError, KeyError, TypeError):
                pass


def _process_start(pid):
    """The kernel's start time of ``pid``, so a reused pid is not mistaken
    for the job; None where /proc is unavailable."""
    try:
        with open(f"/proc/{pid}/stat", encoding="utf-8", errors="replace") as stream:
            return stream.read().rsplit(")", 1)[1].split()[19]
    except (OSError, IndexError):
        return None


def job_record(claim, *, pid, target, log, exit_file, trace_note, started):
    return {
        "token": claim.token, "label": claim.label, "pid": pid,
        "process_start": _process_start(pid), "workdir": str(claim.workdir),
        "target": target, "log": str(log), "exit_file": str(exit_file),
        "trace_note": trace_note, "started": started,
        "outputs": [str(p) for p in claim.outputs],
        "before": {str(p): s for p, s in claim.before.items()},
        "tags": {t: sorted(str(p) for p in ps) for t, ps in claim.tags.items()},
        "in_process": sorted(str(p) for p in claim.in_process),
        "commands": dict(claim.commands),
    }


def write_job(record):
    directory = jobs_directory()
    destination = directory / f"{record['token']}.json"
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=directory,
                                     delete=False) as stream:
        json.dump(record, stream)
        temporary = Path(stream.name)
    os.replace(temporary, destination)
    cutoff = time.time() - 7 * 24 * 3600
    for stale in directory.glob("*.json"):
        if stale != destination:
            try:
                data = json.loads(stale.read_text())
                if data.get("finalized") and data["finalized"]["at"] < cutoff:
                    stale.unlink()
            except (OSError, ValueError, KeyError, TypeError):
                pass


def read_job(token):
    if not _TOKEN_RE.match(token or ""):
        return None
    try:
        record = json.loads((jobs_directory() / f"{token}.json").read_text())
    except (OSError, ValueError):
        return None
    return record if isinstance(record, dict) and record.get("token") == token else None


def job_exit_status(record):
    """Holmake's exit status written by the job's wrapper, or None while it
    runs or if the wrapper itself was killed."""
    try:
        return int(Path(record["exit_file"]).read_text().strip())
    except (OSError, ValueError, KeyError):
        return None


def process_alive(record):
    pid = record.get("pid")
    if not pid:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        pass
    start = _process_start(pid)
    return start is None or record.get("process_start") in (None, start)


def finalize_job(record, returncode, output):
    """Apply a finished (or cancelled: ``returncode`` None) job's outcome to
    its outputs' coordination records, as its own server would have."""
    owner = _RecordOwner(record["token"], record["label"])
    outputs = [Path(p) for p in record["outputs"]]
    before = {Path(p): (tuple(s) if s is not None else None)
              for p, s in record["before"].items()}
    tags = {t: {Path(p) for p in ps} for t, ps in record["tags"].items()}
    in_process = {Path(p) for p in record["in_process"]}
    completed = completed_outputs(tags, in_process, output, returncode,
                                  record.get("commands"))
    finalize(outputs, before, returncode, owner, completed)
    record["finalized"] = {"returncode": returncode, "at": time.time()}
    write_job(record)


def adopt_finished_job(token):
    """Finalize a job whose controller is gone but whose wrapper recorded
    Holmake's exit status. True when something was applied."""
    record = read_job(token)
    if record is None or record.get("finalized"):
        return False
    returncode = job_exit_status(record)
    if returncode is None:
        return False
    try:
        output = Path(record["log"]).read_text(encoding="utf-8", errors="replace")
    except (OSError, KeyError):
        output = ""
    try:
        finalize_job(record, returncode, output)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"Build coordination state could not be finalized for job "
              f"{token}: {exc}", file=sys.stderr)
        return False
    return True


def record_finalized(token, returncode):
    """Note that the job's own server finalized it, so no adoption repeats it."""
    record = read_job(token)
    if record is not None and not record.get("finalized"):
        record["finalized"] = {"returncode": returncode, "at": time.time()}
        try:
            write_job(record)
        except OSError:
            pass


def _lock_storage():
    return _storage("locks")


def _unit_lock(unit):
    directory, stem = unit
    digest = hashlib.sha256(f"{directory}\0{stem}".encode()).hexdigest()
    return _lock_storage() / f"{digest}.lock"


# Holmake and its children inherit the lock descriptors (pass_fds). Numbered
# at or above FD_SETSIZE they leave the low numbers free for the children's
# own descriptors: glibc aborts select() on a descriptor of FD_SETSIZE or more,
# and a large closure holds thousands of locks.
_LOCK_FD_BASE = 1024


def _open_lock(path):
    low = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        return fcntl.fcntl(low, fcntl.F_DUPFD_CLOEXEC, _LOCK_FD_BASE)
    finally:
        os.close(low)


def _note_holder(unit, mode, claim):
    """Best-effort record of who holds a unit's lock, for the message the
    next server shows when it is refused; the lock itself is the evidence."""
    try:
        _unit_lock(unit).with_suffix(".holder.json").write_text(json.dumps({
            "unit": f"{unit[0]}/{unit[1]}", "mode": mode, "label": claim.label,
            "pid": os.getpid(), "since": time.time()}))
    except OSError:
        pass


def _foreign_label(unit):
    # Holder notes and intent records are evidence for names, never evidence
    # that a process is still alive. Only failure to acquire flock proves overlap.
    try:
        holder = json.loads(_unit_lock(unit).with_suffix(".holder.json").read_text())
        return f"{holder['label']} (server pid {holder['pid']}, {holder['mode']})"
    except (OSError, ValueError, KeyError):
        pass
    try:
        records = _state_directory(unit[0] / "placeholder").glob("*.running.json")
        labels = {json.loads(path.read_text())["label"] for path in records}
        return "; ".join(sorted(labels)) or "another MCP server's build"
    except (OSError, ValueError, KeyError):
        return "another MCP server's build"


def _ensure_fd_budget(needed):
    """Raise the soft open-file limit when a closure needs more lock files
    than it allows; False when even the hard limit cannot hold them."""
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    wanted = _LOCK_FD_BASE + needed + 256
    if wanted <= soft:
        return True
    if hard != resource.RLIM_INFINITY and wanted > hard:
        return False
    try:
        resource.setrlimit(resource.RLIMIT_NOFILE, (max(wanted, soft), hard))
    except (ValueError, OSError):
        return False
    return True


def finalize(outputs, before, returncode, owner, completed=frozenset()):
    """Record each output's fate once its build has ended.

    ``returncode`` None means cancelled or lost. An output the build did not
    finish is marked failed if it changed; one it did finish — the whole set
    on success, ``completed`` otherwise — sheds any stale failure record.
    """
    for path in outputs:
        stamp = _stamp(path)
        failed = _read_state(path, "failed")
        if returncode != 0 and path not in completed:
            if stamp is not None and stamp != before.get(path):
                _write_state(path, "failed", stamp, owner, returncode)
        elif failed is not None and stamp != _record_stamp(failed):
            _unlink_state(path, "failed")
        running = _read_state(path, "running")
        if running is not None and running["token"] == owner.token:
            _unlink_state(path, "running")


class BuildClaims:
    def __init__(self):
        self.active: dict[str, BuildClaim] = {}

    def finish(self, claim, output=""):
        """``output`` is the build's own stdout (the log, for a detached
        job): the verdict lines in it decide what a failed build finished."""
        if claim.token not in self.active:
            return
        if claim.proc is not None and claim.proc.returncode is None:
            return  # Keep protection if killing/reaping the process failed.
        try:
            returncode = claim.proc.returncode if claim.proc is not None else None
            completed = completed_outputs(claim.tags, claim.in_process, output, returncode,
                                          claim.commands)
            finalize(claim.outputs, claim.before, returncode, claim, completed)
        except (OSError, ValueError) as exc:
            # Keep any unfinalized intent conservative, and always release
            # locks. State I/O failure must not strand a resource forever.
            claim.state_error = f"Build coordination state could not be finalized: {exc}"
            print(claim.state_error, file=sys.stderr)
        finally:
            self.active.pop(claim.token, None)
            claim.release_locks()

    def reap_stale(self):
        """Finish claims whose build is over but whose finishing never ran —
        a process that exited without its controller noticing, or a claim
        that never spawned one — so they cannot block this server forever."""
        for previous in list(self.active.values()):
            if previous.proc is not None:
                stale = previous.proc.returncode is not None
            else:
                stale = time.time() - previous.created > 120
            if not stale:
                continue
            output = ""
            if previous.log is not None:
                try:
                    output = previous.log.read_text(encoding="utf-8", errors="replace")
                except OSError:
                    output = ""
            self.finish(previous, output)

    def register(self, claim):
        claim.read_units = {artifact_unit(path) for path in claim.reads}
        claim.write_units = {artifact_unit(path) for path in claim.outputs}
        if claim.clean:
            claim.write_units |= claim.read_units
        self.reap_stale()
        for previous in self.active.values():
            overlap = ((claim.write_units & (previous.read_units | previous.write_units))
                       | (claim.read_units & previous.write_units))
            if overlap:
                shown = sorted(f"{d}/{s}" for d, s in overlap)
                return (f"ERROR: dependency overlap with {previous.label}: "
                        f"{', '.join(shown[:8])}{' …' if len(shown) > 8 else ''}. "
                        "No build was started. Wait for the running build to finish, "
                        "then retry; hol_build_status reports detached jobs.")
        units = claim.read_units | claim.write_units
        if not _ensure_fd_budget(len(units)):
            return (f"ERROR: this build touches {len(units)} artifact units, more lock "
                    "files than the process may open (RLIMIT_NOFILE); raise the hard "
                    "limit or build a smaller target. No build was started.")
        accepted = False
        try:
            for unit in sorted(units, key=lambda u: (str(u[0]), u[1])):
                fd = _open_lock(_unit_lock(unit))
                claim.lock_fds.append(fd)
                writing = unit in claim.write_units
                try:
                    fcntl.flock(fd, (fcntl.LOCK_EX if writing else fcntl.LOCK_SH) | fcntl.LOCK_NB)
                except BlockingIOError:
                    return (f"ERROR: dependency overlap with {_foreign_label(unit)}: "
                            f"{unit[0]}/{unit[1]}. No build was started. Wait for the "
                            "blocking build to finish and retry; foreign job IDs belong "
                            "to their originating MCP server.")
                _note_holder(unit, "writing" if writing else "reading", claim)
            suspects = [(path, record) for path in sorted(claim.reads)
                        if path not in claim.outputs
                        and (record := _suspect(path)) is not None]
            if suspects:
                return _suspect_refusal(suspects)
            claim.before = {path: _stamp(path) for path in claim.outputs}
            for path in sorted(claim.outputs):
                previous = _suspect(path)
                if previous is not None:
                    # Preserve old suspicion before replacing an orphan's
                    # intent. A failed/no-op repair must not erase it.
                    _write_state(path, "failed", claim.before[path],
                                 _RecordOwner(previous["token"], previous["label"]))
                _write_state(path, "running", claim.before[path], claim)
            self.active[claim.token] = claim
            accepted = True
            return None
        finally:
            if not accepted:
                # No recipes have started. Remove only this proposal's intent;
                # retain preexisting failed/orphan evidence.
                try:
                    for path in claim.outputs:
                        running = _read_state(path, "running")
                        if running is not None and running["token"] == claim.token:
                            _unlink_state(path, "running")
                finally:
                    claim.release_locks()


def _left_by_observed_failure(path, record):
    """True when this file is, provably, what an MCP build left unfinished:
    a failed record with the build's observed nonzero exit status, and the
    file unchanged since (mtime, ctime, size and inode)."""
    return (isinstance(record.get("returncode"), int) and record["returncode"] != 0
            and _stamp(path) == _record_stamp(record))


def _suspect_refusal(suspects):
    """The refusal for reads that a build left possibly unfinished. Holmake
    takes an existing file for up to date, so no build is accepted while one
    exists; removing it lets the retried build rebuild it."""
    lines = [f"ERROR: {record['label']} left a possibly partial or unverified "
             f"artifact: {path}" for path, record in suspects[:8]]
    if len(suspects) > 8:
        lines.append(f"… and {len(suspects) - 8} more")
    lines.append("No build was started. Holmake treats an existing file as up to date, "
                 "so no build is accepted while these exist: inspect/remove them, then "
                 "retry this build, which rebuilds them.")
    holdir = HOLDIR.resolve()
    for path, record in suspects[:8]:
        if not path.resolve().is_relative_to(holdir):
            continue
        if _left_by_observed_failure(path, record):
            lines.append(f"{path} is under $HOLDIR. It may be removed: {record['label']} "
                         f"ended with exit status {record['returncode']} and the file is "
                         "unchanged since.")
        else:
            lines.append(f"{path} is under $HOLDIR and is not provably a leftover of an "
                         "MCP build: ask the user to remove it.")
    return "\n".join(lines)


@dataclass
class _RecordOwner:
    token: str
    label: str


build_claims = BuildClaims()
