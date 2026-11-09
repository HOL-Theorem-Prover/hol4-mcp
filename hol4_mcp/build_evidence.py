"""Opt-in build-discovery tracing. Ordinary builds do not invoke a tracer."""
import functools
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

from . import build_coordination as coordination

TRACES_KEPT = 5


@functools.lru_cache(maxsize=None)
def _tracer_options(tracer: str) -> tuple[str, ...]:
    """The optional strace flags this tracer accepts (`--kill-on-exit` needs strace >= 5.17)."""
    try:
        usage = subprocess.run([tracer, "-h"], capture_output=True, text=True,
                               timeout=10).stdout
    except (OSError, subprocess.TimeoutExpired):
        return ()
    return tuple(flag for flag in ("--kill-on-exit",) if flag in usage)


def build_failure_heading(returncode: int, output: str, traced: bool) -> str:
    if traced and re.search(r"^\S*strace:.*(?:PTRACE|ptrace|not permitted|not supported|invalid option|unrecognized option)", output, re.M):
        return ("ERROR: Discovery tracing failed or is unavailable in this execution "
                "environment. This is not a proof-failure verdict; inspect the "
                "tracer error and permissions before a diagnostic retry.")
    return f"Build failed (exit code {returncode})."


def _prune_traces(directory: Path, keep: int) -> None:
    """Keep the newest ``keep`` trace/context pairs."""
    traces = sorted(directory.glob("*.log"), key=lambda p: p.stat().st_mtime, reverse=True)
    for stale in traces[keep:]:
        stale.unlink(missing_ok=True)
        stale.with_suffix(".json").unlink(missing_ok=True)


def traced_build(command: list[str], workdir: Path, enabled: bool,
                 environment: dict) -> tuple[list[str], str]:
    if not enabled:
        return command, ""
    tracer = shutil.which("strace", path=environment.get("PATH"))
    if sys.platform != "linux" or not tracer:
        raise ValueError("trace_discovery=True requires Linux and strace; no build was started")
    directory = coordination.discovery_directory()
    _prune_traces(directory, TRACES_KEPT - 1)
    trace = directory / f"{uuid.uuid4().hex[:12]}.log"
    try:
        namespace = os.readlink("/proc/self/ns/mnt")
    except OSError:
        namespace = "unavailable"
    metadata = trace.with_suffix(".json")
    with metadata.open("x", encoding="utf-8") as stream:
        json.dump({"command": command, "workdir": str(workdir),
                   "server_pid": os.getpid(), "mount_namespace": namespace}, stream)
    wrapped = [tracer, "-f", *_tracer_options(tracer), "-s", "4096", "-e",
               "trace=chdir,fchdir,openat,newfstatat,getdents64",
               "-o", str(trace), "--", *command]
    note = (f"[Discovery trace: {trace}; context: {metadata}; "
            f"mount namespace: {namespace}. Inspect failed syscalls and their "
            "paths; the last printed directory is not necessarily the failure. "
            f"Tracing is opt-in and adds overhead; the newest {TRACES_KEPT} traces "
            "are kept. One traced run is the whole diagnostic — do not retrace retries.]")
    return wrapped, note
