#!/usr/bin/env python3
"""HOL4 MCP Server - provides theorem prover interaction tools.

Sessions are in-memory only. They survive within a single MCP server lifetime
(including across Claude context handoffs) but not across server restarts.
"""

import asyncio
import atexit
import hashlib
import json
import os
import re
import signal
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

from fastmcp import FastMCP, Context

from .hol_session import HOLSession, HOLDIR
from .hol_cursor import FileProofCursor
from .hol_file_parser import HOLParseError


DEFAULT_MAX_OUTPUT = 4096

# Server-level tactic timeout (set via --tactic-timeout CLI flag or HOL_TACTIC_TIMEOUT env)
TACTIC_TIMEOUT = float(os.environ.get("HOL_TACTIC_TIMEOUT", "5.0"))


def _file_offset_to_line_col(file_offset: int, content: str) -> tuple[int, int]:
    """Convert a byte offset in file content to absolute (line, col), both 1-indexed."""
    before = content[:file_offset]
    line = before.count('\n') + 1
    last_nl = before.rfind('\n')
    col = file_offset - last_nl if last_nl >= 0 else file_offset + 1
    return line, col


def _truncate_output(output: str, max_output: int, footer: str = "") -> str:
    """Truncate output to max_output bytes, showing tail.

    If footer is provided, it's appended AFTER truncation so it's never lost.
    """
    if max_output < 1:
        return f"ERROR: max_output must be positive (got {max_output})"
    # Reserve space for footer
    if footer:
        footer = "\n" + footer
        body_budget = max_output - len(footer)
        if body_budget < 100:
            # Not enough room — just show footer
            return footer.lstrip("\n")
        if len(output) > body_budget:
            return (
                f"[TRUNCATED: {len(output)} bytes, showing last {body_budget}]\n\n"
                + output[-body_budget:]
                + footer
            )
        return output + footer
    if len(output) > max_output:
        return f"[TRUNCATED: {len(output)} bytes, showing last {max_output}]\n\n{output[-max_output:]}"
    return output


@dataclass
class SessionEntry:
    """Registry entry for a HOL session."""
    session: HOLSession
    started: datetime
    workdir: Path
    last_used: float = 0.0  # time.time() of last activity
    cursor: Optional[FileProofCursor] = None
    holmake_env: Optional[dict] = None  # env vars for holmake (auto-captured on success)
    env: Optional[dict] = None  # env vars passed to HOL process

    def __post_init__(self):
        if self.last_used == 0.0:
            self.last_used = time.time()


mcp = FastMCP("hol", instructions="""HOL4 theorem prover - proof development workflow:

1. hol_state_at: Check proof state at cursor position (pass file= to auto-init)
2. Edit file directly, then hol_state_at to see new goals
3. Repeat until proof complete
4. holmake: Only at the end to verify the build

Do NOT:
- Call hol_restart after file edits (state_at auto-detects changes)
- Use hol_send for proof navigation (use hol_state_at instead)
""")
_sessions: dict[str, SessionEntry] = {}


def _sigint_handler(signum, frame):
    """Handle SIGINT by interrupting all HOL sessions.
    
    Called when pi sends SIGINT (e.g., user pressed ESC during tool execution).
    Interrupts all running HOL sessions to abort runaway tactics.
    
    Note: Takes a snapshot of sessions to avoid RuntimeError if dict is modified
    concurrently (e.g., session being added/removed when signal arrives).
    """
    # Snapshot to avoid "dictionary changed size during iteration"
    for entry in list(_sessions.values()):
        try:
            entry.session.interrupt()
        except Exception:
            pass  # Best effort - signal handlers must not raise


# Install SIGINT handler (replaces default KeyboardInterrupt behavior)
signal.signal(signal.SIGINT, _sigint_handler)


def _kill_all_sessions_sync():
    """Best-effort SIGKILL all HOL process groups. Safe from atexit/signal.

    Covers abnormal shutdown paths where async `hol_stop` won't run:
    - stdio_client's _terminate_process_tree sends SIGTERM to *our* pgid
      but HOL is in its own pgid (start_new_session=True in HOLSession).
    - atexit fires on normal interpreter shutdown.
    Without this, HOL children (multi-GB RSS) get reparented to PID 1 and leak.
    """
    for entry in list(_sessions.values()):
        try:
            entry.session.kill_sync()
        except Exception:
            pass  # best effort


def _sigterm_handler(signum, frame):
    """Kill HOL children, then re-raise default SIGTERM so we actually exit."""
    _kill_all_sessions_sync()
    signal.signal(signum, signal.SIG_DFL)
    os.kill(os.getpid(), signum)


signal.signal(signal.SIGTERM, _sigterm_handler)
atexit.register(_kill_all_sessions_sync)


_SESSION_IDLE_TIMEOUT = 1800  # 30 minutes
_PRUNE_INTERVAL = 300  # Check every 5 minutes at most
_last_prune_time = 0.0


def _gc_cursor_checkpoints(cursor: FileProofCursor):
    """Delete orphaned per-theorem checkpoint .save files from a dying cursor.

    Keeps base_deps.save and deps_only.save (expensive ~200MB rebuilds).
    Removes per-theorem context/end_of_proof saves (cheap to rebuild via replay).
    """
    ckpt_dir = cursor._checkpoint_dir
    if not ckpt_dir or not ckpt_dir.exists():
        return
    for f in ckpt_dir.glob("*_context.save"):
        f.unlink(missing_ok=True)
    for f in ckpt_dir.glob("*_end_of_proof.save"):
        f.unlink(missing_ok=True)
    try:
        ckpt_dir.rmdir()  # only removes if empty
    except OSError:
        pass


def _gc_dir_full(ckpt_dir: Path):
    """Remove all .save files and the checkpoint directory."""
    if not ckpt_dir or not ckpt_dir.exists():
        return
    for f in ckpt_dir.glob("*.save"):
        f.unlink(missing_ok=True)
    try:
        ckpt_dir.rmdir()
    except OSError:
        pass


def _gc_workdir_orphans(workdir: Path):
    """Clean orphaned per-theorem checkpoints from a workdir.

    Called on hol_start when no existing session owns the workdir.
    Deletes *_context.save and *_end_of_proof.save (cheap replay rebuilds)
    across all cursor_checkpoints/ dirs under the workdir.
    Keeps base_deps.save and deps_only.save (expensive ~200MB rebuilds).
    """
    for ckpt_dir in workdir.glob("**/cursor_checkpoints"):
        if not ckpt_dir.is_dir():
            continue
        for f in ckpt_dir.glob("*_context.save"):
            f.unlink(missing_ok=True)
        for f in ckpt_dir.glob("*_end_of_proof.save"):
            f.unlink(missing_ok=True)
        try:
            ckpt_dir.rmdir()
        except OSError:
            pass


async def _prune_idle_sessions():
    """Stop and remove sessions idle longer than _SESSION_IDLE_TIMEOUT.

    Throttled to run at most once per _PRUNE_INTERVAL seconds.
    """
    global _last_prune_time
    now = time.time()
    if now - _last_prune_time < _PRUNE_INTERVAL:
        return
    _last_prune_time = now
    to_prune = [
        name for name, entry in _sessions.items()
        if now - entry.last_used > _SESSION_IDLE_TIMEOUT
    ]
    for name in to_prune:
        entry = _sessions.get(name)
        if not entry:
            continue
        # Re-check: session may have been touched during a prior await
        if time.time() - entry.last_used <= _SESSION_IDLE_TIMEOUT:
            continue
        _sessions.pop(name, None)
        if entry.cursor:
            _gc_cursor_checkpoints(entry.cursor)
        await entry.session.stop()


_GC_CALL_INTERVAL = 10    # At most once per N tool calls
_GC_TIME_INTERVAL = 120   # At most once per K seconds
_gc_call_counter = 0
_gc_last_time = 0.0


async def _do_gc(session_name: str):
    """Actually run PolyML.fullGC(). Runs as background task."""
    entry = _sessions.get(session_name)
    if entry and entry.session.is_running:
        try:
            await entry.session.send('PolyML.fullGC();', timeout=10)
        except Exception:
            pass  # Best effort — don't crash on GC failure


def _schedule_gc(session_name: str):
    """Schedule background GC if due. Non-blocking — doesn't delay response.

    Triggers when both conditions met: N calls since last GC AND K seconds elapsed.
    """
    global _gc_call_counter, _gc_last_time
    _gc_call_counter += 1
    if _gc_call_counter < _GC_CALL_INTERVAL:
        return
    now = time.time()
    if now - _gc_last_time < _GC_TIME_INTERVAL:
        return
    _gc_call_counter = 0
    _gc_last_time = now
    asyncio.create_task(_do_gc(session_name))


async def _get_session(name: str) -> Optional[HOLSession]:
    """Get session from registry, or None if not found. Triggers idle pruning."""
    await _prune_idle_sessions()
    entry = _sessions.get(name)
    if entry:
        entry.last_used = time.time()
    return entry.session if entry else None


async def _get_cursor(name: str) -> Optional[FileProofCursor]:
    """Get cursor from registry, or None if not found. Triggers idle pruning."""
    await _prune_idle_sessions()
    entry = _sessions.get(name)
    if entry:
        entry.last_used = time.time()
    return entry.cursor if entry else None


def _session_age(name: str) -> str:
    """Get human-readable session age."""
    entry = _sessions.get(name)
    if not entry:
        return "unknown"
    started = entry.started
    delta = datetime.now() - started
    secs = int(delta.total_seconds())
    if secs < 60:
        return f"{secs}s"
    elif secs < 3600:
        return f"{secs // 60}m"
    else:
        return f"{secs / 3600:.1f}h"


@mcp.tool()
async def hol_start(workdir: str, name: str = "default", env: dict = None) -> str:
    """Start a HOL4 REPL session.

    Idempotent - returns existing session if already running.
    Usually called automatically by hol_state_at (via file= parameter).

    Args:
        workdir: Working directory (should contain Holmakefile for dependencies)
        name: Session identifier (e.g., "main")
        env: Optional environment variables (e.g. {"VFMDIR": "/path/to/vfm"})

    Returns: Session status
    """
    await _prune_idle_sessions()
    # If session exists and is running, return its state
    if name in _sessions:
        session = _sessions[name].session
        if session.is_running:
            goals = await session.send("top_goals();", timeout=10)
            return f"Session '{name}' already running.\n\n=== Goals ===\n{goals}"
        # Dead session - clean up
        del _sessions[name]

    # Validate workdir
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Working directory does not exist: {workdir}"

    # Create session with optional env
    session = HOLSession(str(workdir_path), env=env)

    try:
        result = await session.start()
    except Exception as e:
        return f"ERROR starting HOL: {e}"

    if not session.is_running:
        return f"ERROR: HOL failed to start. Output: {result}"

    # Register session. Handle concurrent hol_start(name=...) calls:
    # if another caller already registered a running session, stop this one
    # and return the existing session state.
    existing = _sessions.get(name)
    if existing and existing.session.is_running:
        await session.stop()
        goals = await existing.session.send("top_goals();", timeout=10)
        return f"Session '{name}' already running.\n\n=== Goals ===\n{goals}"

    _sessions[name] = SessionEntry(session, datetime.now(), workdir_path, env=env)

    # Clean orphaned per-theorem checkpoints left by previous server lifetimes
    _gc_workdir_orphans(workdir_path)

    return f"Session '{name}' started. {result}\nWorkdir: {workdir_path}"


@mcp.tool()
async def hol_sessions() -> str:
    """List all active HOL sessions with their workdir, age, status, cursor."""
    await _prune_idle_sessions()
    if not _sessions:
        return "No active sessions."

    lines = ["SESSION      WORKDIR                                    AGE     IDLE    STATUS   CURSOR"]
    lines.append("-" * 105)

    now = time.time()
    for name, entry in _sessions.items():
        status = "running" if entry.session.is_running else "dead"
        age = _session_age(name)
        idle_secs = int(now - entry.last_used)
        if idle_secs < 60:
            idle_str = f"{idle_secs}s"
        elif idle_secs < 3600:
            idle_str = f"{idle_secs // 60}m"
        else:
            idle_str = f"{idle_secs / 3600:.1f}h"
        workdir_str = str(entry.workdir)
        if len(workdir_str) > 40:
            workdir_str = "..." + workdir_str[-37:]

        # Cursor info
        if entry.cursor:
            cs = entry.cursor.status
            cursor_str = f"{cs['active_theorem']}" if cs['active_theorem'] else "(none)"
        else:
            cursor_str = "(none)"

        lines.append(f"{name:<12} {workdir_str:<42} {age:<7} {idle_str:<7} {status:<8} {cursor_str}")

    return "\n".join(lines)


_PROOF_STATE_PATTERNS = [
    (re.compile(r"^\s*e\s*\("), "e(...)"),
    (re.compile(r"^\s*b\s*\(\s*\)"), "b()"),
    (re.compile(r"^\s*drop\s*\(\s*\)"), "drop()"),
    (re.compile(r"^\s*top_goal\s*\(\s*\)"), "top_goal()"),
    (re.compile(r"^\s*g\s*[`(]"), "g()/g`...`"),
    (re.compile(r"^\s*p\s*\(\s*\)"), "p()"),
    (re.compile(r"^\s*r\s*\(\s*\)"), "r()"),
    (re.compile(r"^\s*prove\s*\("), "prove(...)"),
    (re.compile(r"proofManagerLib\."), "proofManagerLib.*"),
]


def _check_proof_state_command(command: str) -> str | None:
    """Block hol_send commands that interact with proof state.

    Returns an error message if blocked, None if allowed.
    """
    cmd = command.strip()
    for pattern, name in _PROOF_STATE_PATTERNS:
        if pattern.search(cmd):
            return (
                f"ERROR: hol_send BLOCKED — '{name}' interacts with proof state.\n"
                f"\n"
                f"hol_send must ONLY be used for read-only queries:\n"
                f"  DB.match, DB.find, type_of, EVAL, printing theorems\n"
                f"\n"
                f"For proof development, use:\n"
                f"  hol_state_at(line, col) — navigate to position, see goals\n"
                f"  Edit tool — modify tactics in the file\n"
                f"  hol_check_proof — validate complete proofs\n"
            )
    return None


@mcp.tool()
async def hol_send(command: str, timeout: int = 5, max_output: int = DEFAULT_MAX_OUTPUT, session: str = "default") -> str:
    """Send raw SML command to HOL session.

    WARNING: Do NOT use for proof navigation - use hol_state_at instead.
    hol_state_at handles file changes, checkpoints, and tactic replay automatically.

    Only use hol_send for:
      - Database queries: DB.match [], ``add _ _``
      - Type checking: type_of ``expr``
      - Term parsing: Term `expr`
      - One-off SML evaluation
      - Debugging session state

    Args:
        command: SML command to execute
        session: Session name (default: "default")
        timeout: Max seconds to wait (default 5, max 600)
        max_output: Max bytes of output to return (default 4096).
                    Shows tail when truncated (errors/results come after echoed input).

    Returns: HOL output (may include errors), truncated if exceeds max_output
    """
    blocked = _check_proof_state_command(command)
    if blocked:
        return blocked

    s = await _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."

    # Validate timeout
    if timeout < 1:
        timeout = 1
    elif timeout > 600:
        timeout = 600

    t0 = time.monotonic()
    result = await s.send(command, timeout=timeout)
    elapsed = time.monotonic() - t0
    _schedule_gc(session)
    timing = f"\n[{elapsed:.3f}s]"
    return _truncate_output(result, max_output, footer=timing)


@mcp.tool()
async def hol_interrupt(session: str = "default") -> str:
    """Send SIGINT to abort runaway tactic.

    Args:
        session: Session name (default: "default")

    Returns: Confirmation message
    """
    s = await _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died."

    s.interrupt()

    # Flush interrupt message by sending dummy command
    # HOL queues "Compilation interrupted" which pollutes next send() otherwise
    await asyncio.sleep(0.1)
    await s.send(";", timeout=1)

    return f"Sent SIGINT to session '{session}'. The tactic should be interrupted."


@mcp.tool()
async def hol_stop(session: str = "default") -> str:
    """Terminate HOL session.

    Args:
        session: Session name (default: "default")

    Returns: Confirmation message
    """
    entry = _sessions.get(session)
    if entry:
        if entry.cursor:
            _gc_cursor_checkpoints(entry.cursor)
        await entry.session.stop()
        del _sessions[session]
        return f"Session '{session}' stopped."
    return f"Session '{session}' not found."


@mcp.tool()
async def hol_restart(session: str = "default") -> str:
    """Restart HOL session (stop + start, preserves workdir).

    Only needed when:
    - HOL state is corrupted (rare)
    - Upstream dependencies changed (edited other .sml files that need Holmake)

    NOT needed for edits to current proof file - state_at auto-detects changes.

    Args:
        session: Session name to restart

    Returns: Same as hol_start (cursor is cleared, use hol_state_at file= to re-init)
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found."

    workdir = entry.workdir
    env = entry.env  # Preserve env through restart
    await hol_stop(session)
    return await hol_start(workdir=str(workdir), name=session, env=env)


@mcp.tool()
async def hol_setenv(env: dict, session: str = "default") -> str:
    """Set environment variables for a HOL session and auto-restart to apply.

    These are passed to the HOL process and affect Holmakefile INCLUDES expansion.

    Example: hol_setenv({"VFMDIR": "/home/user/verifereum"})

    Args:
        env: Environment variables to set (merged with existing)
        session: Session name (default: "default")

    Returns: Confirmation message (includes restart output if session was running)
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found. Use hol_start first."

    # Merge with existing env
    if entry.env:
        entry.env.update(env)
    else:
        entry.env = env

    # Auto-restart to apply new env to running process
    if entry.session.is_running:
        restart_result = await hol_restart(session)
        return f"Environment updated and session restarted: {env}\n{restart_result}"

    return f"Environment updated for session '{session}': {env}"


async def _kill_process_group(proc):
    """Kill process group: SIGTERM, wait, SIGKILL if needed.

    Must kill even if parent exited - children (buildheap) may still be alive.
    """
    if proc is None:
        return

    pgid = proc.pid

    # Send SIGTERM to the whole process group
    try:
        os.killpg(pgid, signal.SIGTERM)
    except OSError:
        return  # Process group doesn't exist

    # Wait for processes to die gracefully (up to 1s)
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=1.0)
        except (asyncio.TimeoutError, asyncio.CancelledError):
            pass
    else:
        # Parent already exited, give children time to die from SIGTERM
        try:
            await asyncio.sleep(1.0)
        except asyncio.CancelledError:
            pass  # Still need to SIGKILL

    # SIGKILL anything remaining in the group
    try:
        os.killpg(pgid, signal.SIGKILL)
    except OSError:
        pass  # Already gone

    # Reap parent if needed
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=0.5)
        except:
            pass


# Progress reporting interval for long builds (resets MCP client timeout)
_PROGRESS_INTERVAL = 10  # seconds


@mcp.tool()
async def holmake(workdir: str, target: str = None, env: dict = None, log_limit: int = 1024, timeout: int = 90, heap_size: int = 12288, jobs: int = None, ctx: Context = None) -> str:
    """Run Holmake --qof in directory.

    Args:
        workdir: Directory containing Holmakefile
        target: Optional specific target to build
        env: Optional environment variables (e.g. {"MY_VAR": "/some/path"})
        log_limit: Max bytes per log file to include on failure (default 1024)
        timeout: Max seconds to wait (default 90, max 1800)
        heap_size: Max heap size in MB for Poly/ML builds (default 12288)
        jobs: Max parallel jobs (-j flag). Default from HOL4_MCP_HOLMAKE_JOBS env var, or 1.

    Returns: Holmake output (stdout + stderr). On failure, includes recent build logs.

    Note: For builds > 60s, progress notifications are sent every 10s to prevent
    MCP client timeout. Configure tool_timeout_sec in ~/.codex/config.toml if needed.
    """
    # Validate limits
    timeout = max(1, min(timeout, 1800))
    heap_size = max(256, heap_size)
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Directory does not exist: {workdir}"

    holmake_bin = HOLDIR / "bin" / "Holmake"
    if not holmake_bin.exists():
        return f"ERROR: Holmake not found at {holmake_bin}"

    logs_dir = workdir_path / ".hol" / "logs"

    # Delete all prior logs so only this run's logs exist afterward.
    # Holmake only truncates a target's log when that target's job starts,
    # so stale logs from prior runs would otherwise persist for any target
    # not reached (e.g. due to timeout or dependency failure).
    if logs_dir.exists():
        for log_file in logs_dir.iterdir():
            if log_file.is_file():
                log_file.unlink()

    # Resolve parallelism: explicit param > env var > 1
    if jobs is None:
        jobs = int(os.environ.get("HOL4_MCP_HOLMAKE_JOBS", "1"))
    jobs = max(1, jobs)

    cmd = [str(holmake_bin), "--qof", f"--heap-size={heap_size}"]
    if jobs > 1:
        cmd.extend(["-j", str(jobs)])
    if target:
        cmd.append(target)

    # Build environment
    proc_env = os.environ.copy()
    if env:
        proc_env.update(env)

    proc = None
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            cwd=workdir_path,
            env=proc_env,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
            start_new_session=True,
        )

        # Poll with progress reporting to prevent MCP client timeout
        start_time = time.time()
        stdout_chunks = []
        timed_out = False

        while True:
            elapsed = time.time() - start_time
            if elapsed >= timeout:
                timed_out = True
                break

            # Report progress to reset client timeout (MCP resetTimeoutOnProgress)
            if ctx:
                try:
                    await ctx.report_progress(
                        progress=elapsed,
                        total=float(timeout),
                        message=f"Building... {int(elapsed)}s / {timeout}s"
                    )
                except Exception:
                    pass  # Don't fail build if progress reporting fails

            # Wait for output or timeout after interval
            try:
                chunk = await asyncio.wait_for(
                    proc.stdout.read(4096),
                    timeout=min(_PROGRESS_INTERVAL, timeout - elapsed)
                )
                if chunk:
                    stdout_chunks.append(chunk)
                else:
                    # EOF - wait for process to finish
                    try:
                        await asyncio.wait_for(proc.wait(), timeout=5)
                    except asyncio.TimeoutError:
                        pass
                    break
            except asyncio.TimeoutError:
                # Check if process finished
                if proc.returncode is not None:
                    break
                continue  # Keep polling

        wall = time.time() - start_time

        if timed_out:
            return f"ERROR: Build timed out after {timeout}s."

        output = b''.join(stdout_chunks).decode("utf-8", errors="replace")

        if proc.returncode == 0:
            result = f"Build succeeded.\n\n{output}"
            if env:
                # Store env in matching session entries for auto-holmake at startup
                for entry in _sessions.values():
                    if entry.workdir == workdir_path:
                        entry.holmake_env = env
                # Include env in output for caller to capture if needed
                result += f"\nHOLMAKE_ENV: {json.dumps(env)}"
            return f"{result}\n[{wall:.1f}s]"

        # Build failed - append relevant logs (all logs are from this run)
        result = f"Build failed (exit code {proc.returncode}).\n\n{output}"

        if logs_dir.exists():
            logs = sorted(
                [f for f in logs_dir.iterdir() if f.is_file()],
                key=lambda f: -f.stat().st_mtime
            )
            if logs:
                result += "\n\n=== Build Logs ===\n"
                for log_file in logs[:3]:
                    content = log_file.read_text(errors="replace")
                    if len(content) > log_limit:
                        content = f"...(truncated, showing last {log_limit} bytes)...\n" + content[-log_limit:]
                    result += f"\n--- {log_file.name} ---\n{content}\n"

        return f"{result}\n[{wall:.1f}s]"

    except Exception as e:
        return f"ERROR: {e}"
    finally:
        await _kill_process_group(proc)


@mcp.tool()
async def hol_log(workdir: str, theory: str, limit: int = 1024) -> str:
    """Read build log for a specific theory.

    Use after holmake to inspect warnings or errors in detail.

    Args:
        workdir: Directory containing .hol/logs/
        theory: Theory name (e.g., "fooTheory")
        limit: Max bytes to return (default 1024, 0 for unlimited)

    Returns: Log file contents (tail if truncated).
    """
    workdir_path = Path(workdir).resolve()
    log_file = workdir_path / ".hol" / "logs" / theory

    if not log_file.exists():
        # Try without "Theory" suffix
        log_file = workdir_path / ".hol" / "logs" / f"{theory}Theory"
        if not log_file.exists():
            available = []
            logs_dir = workdir_path / ".hol" / "logs"
            if logs_dir.exists():
                available = [f.name for f in logs_dir.iterdir() if f.is_file()]
            if available:
                return f"Log not found: {theory}\nAvailable: {', '.join(sorted(available))}"
            return f"Log not found: {theory}\nNo logs in {logs_dir}"

    content = log_file.read_text(errors="replace")
    if limit > 0 and len(content) > limit:
        return f"...(truncated, showing last {limit} bytes)...\n{content[-limit:]}"
    return content


@mcp.tool()
async def hol_logs(workdir: str) -> str:
    """List available build logs.

    Args:
        workdir: Directory containing .hol/logs/

    Returns: List of log files with sizes and modification times
    """
    workdir_path = Path(workdir).resolve()
    logs_dir = workdir_path / ".hol" / "logs"

    if not logs_dir.exists():
        return f"No logs directory: {logs_dir}"

    logs = []
    for log_file in sorted(logs_dir.iterdir()):
        if log_file.is_file():
            stat = log_file.stat()
            size = stat.st_size
            mtime = datetime.fromtimestamp(stat.st_mtime).strftime("%H:%M:%S")
            logs.append(f"  {log_file.name}: {size} bytes, modified {mtime}")

    if not logs:
        return "No log files found."
    return "Build logs:\n" + "\n".join(logs)


# =============================================================================
# Cursor Tools (for multi-theorem files)
# =============================================================================


async def _init_file_cursor(
    file: str,
    session: str = "default",
    workdir: str = None,
) -> str:
    """Initialize cursor for a HOL4 script file (internal helper).

    Parses file for theorems and their proofs. Auto-starts HOL session if needed.
    After init, use hol_state_at to navigate to specific positions and see goals.

    Args:
        file: Path to *Script.sml file containing theorems
        session: Session name (default: "default")
        workdir: Working directory for HOL (default: file's parent directory)

    Returns: List of theorems with line numbers and cheat status
    """
    # Validate file first
    file_path = Path(file).resolve()
    if not file_path.exists():
        return f"ERROR: File not found: {file}"

    # Determine target workdir
    target_workdir = Path(workdir).resolve() if workdir else file_path.parent

    # Auto-start or restart session if workdir changed or file content changed
    s = await _get_session(session)
    entry = _sessions.get(session)

    if s and s.is_running:
        # Check if workdir differs - need to restart
        if entry and entry.workdir != target_workdir:
            await hol_stop(session)
            s = None
        # Check if file content changed - session has stale definitions
        elif entry and entry.cursor:
            old_cursor = entry.cursor
            if Path(old_cursor.file).resolve() == file_path:
                # Same file - check if content changed
                old_hash = old_cursor._content_hash
                new_content = file_path.read_text()
                new_hash = hashlib.sha256(new_content.encode()).hexdigest()
                if old_hash and new_hash != old_hash:
                    # File changed - restart session to clear stale definitions
                    await hol_stop(session)
                    s = None

    if not s or not s.is_running:
        # Preserve per-session HOL env (e.g., VFMDIR) across auto-restarts.
        start_env = entry.env if entry else None
        start_result = await hol_start(workdir=str(target_workdir), name=session, env=start_env)
        if start_result.startswith("ERROR"):
            return start_result
        s = await _get_session(session)

    # GC stale per-theorem checkpoints from old cursor before replacing
    if entry and entry.cursor:
        _gc_cursor_checkpoints(entry.cursor)

    t0 = time.perf_counter()
    
    cursor = FileProofCursor(file_path, s, tactic_timeout=TACTIC_TIMEOUT)
    result = await cursor.init()
    
    init_time = time.perf_counter() - t0

    _sessions[session].cursor = cursor

    if result.get("error"):
        return f"ERROR: {result['error']}"

    # Build status output
    lines = [
        f"File: {file_path}",
        f"Theorems: {len(result['theorems'])} ({len(result['cheats'])} cheats)",
    ]

    if result['cheats']:
        lines.append("")
        lines.append("Cheats to fix:")
        for cheat in result['cheats']:
            lines.append(f"  {cheat['theorem']} (line {cheat['line']})")

    lines.append("")
    lines.append(f"[Init time: {init_time*1000:.0f}ms]")

    return "\n".join(lines)


@mcp.tool()
async def hol_state_at(
    line: int,
    col: int = 1,
    file: str = None,
    workdir: str = None,
    max_output: int = DEFAULT_MAX_OUTPUT,
    session: str = "default",
    show_partial: bool = False,
    all_goals: bool = False,
    context_before: int = 0,
    context_after: int = 0,
) -> str:
    """Get proof state at a file position.

    Replays tactics from theorem start up to (but not including) the tactic at
    the given position, then shows current goals. Auto-enters theorem if needed.

    By default only the top goal is shown (with total count). Set all_goals=True
    to see every goal on the stack.

    If replay fails before reaching the requested position, the default behavior
    is to refuse to show goals (they would be from the wrong proof state).
    Set show_partial=True to see the best-effort goals anyway.

    Args:
        line: 1-indexed line number (position in the proof)
        col: 1-indexed column number (default 1)
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        max_output: Max bytes of output (default 1000)
        session: Session name (default: "default")
        show_partial: If True, show best-effort goals even when replay fails
                      before reaching the requested position (default: False)
        all_goals: If True, show all goals; otherwise only the top goal (default: False)
        context_before: Number of preceding tactics to show on PROOF BROKEN (default: 0)
        context_after: Number of following tactics to show on PROOF BROKEN (default: 0)

    Returns: Proof position, goals at that position, errors if any
    """
    cursor = await _get_cursor(session)

    # Auto-init if file provided and no cursor (or different file)
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    result = await cursor.state_at(line, col)
    active_theorem = cursor._active_theorem
    thm = cursor._get_theorem(active_theorem) if active_theorem else None

    # Helper to convert tactic index to absolute line:col
    def tactic_to_loc(idx):
        if not thm:
            return None
        if not thm.proof_body or idx <= 0:
            # Start of proof body content (accounts for stripped whitespace)
            return _file_offset_to_line_col(thm.proof_body_offset, cursor._content)
        if idx > len(cursor._step_plan):
            idx = len(cursor._step_plan)
        if idx > 0:
            step = cursor._step_plan[idx - 1]
            file_pos = thm.proof_body_offset + step.end
            return _file_offset_to_line_col(file_pos, cursor._content)
        return _file_offset_to_line_col(thm.proof_body_offset, cursor._content)

    lines = []
    error_footer = ""  # Errors go in footer so truncation never hides them
    
    # Check if "no goals" error is actually success (proof complete)
    is_proof_complete = (
        result.error and 
        "no goals" in result.error.lower() and
        result.tactics_replayed == result.tactics_total and
        not result.goals
    )
    
    # Structural error (not in theorem, etc.) - no goals to show
    if result.error and result.tactics_total == 0:
        lines.append(f"ERROR: {result.error}")
        return "\n".join(lines)

    # Detect broken proof: replay couldn't reach the requested position
    is_broken = (
        result.error
        and not is_proof_complete
        and result.tactics_replayed < result.tactic_idx
    )

    # Show theorem name (useful for hol_check_proof after edits)
    if active_theorem:
        lines.append(f"Theorem: {active_theorem}")
    
    if is_broken:
        # Proof is broken before the requested position
        stuck_loc = tactic_to_loc(result.tactics_replayed)
        stuck_str = f"line {stuck_loc[0]} col {stuck_loc[1]}" if stuck_loc else ""
        # Compute where the failed tactic starts (next step after last success)
        fail_idx = result.tactics_replayed  # 0-indexed: the step that failed
        fail_loc = tactic_to_loc(fail_idx)
        fail_str = f"line {fail_loc[0]} col {fail_loc[1]}" if fail_loc else ""

        lines.append(
            f"PROOF BROKEN at {fail_str}"
        )
        lines.append(f"ERROR: {result.error}")

        # Show failing tactic and surrounding context when requested
        step_plan = cursor._step_plan if cursor else []
        if fail_idx < len(step_plan) and (context_before or context_after):
            lines.append("")
            lines.append("=== Failing tactic ===")
            lines.append(step_plan[fail_idx].text)
            for i in range(max(0, fail_idx - context_before), fail_idx):
                lines.append("")
                lines.append("--- Preceding tactic ---")
                lines.append(step_plan[i].text)
            for i in range(fail_idx + 1, min(len(step_plan), fail_idx + 1 + context_after)):
                lines.append("")
                lines.append("--- Following tactic ---")
                lines.append(step_plan[i].text)

        lines.append("")
        lines.append(
            f"Replay cannot reach the requested position because an earlier "
            f"tactic failed. The proof is sequential — later goals depend on "
            f"earlier tactics succeeding."
        )
        if fail_loc:
            lines.append(
                f"Fix the broken tactic, or inspect the failure point with:\n"
                f"  hol_state_at(line={fail_loc[0]}, col={fail_loc[1]})"
            )

        if result.goals:
            # Always show goals at failure point (useful for debugging)
            # show_partial controls whether ALL goals or just the first are shown
            display_goals = result.goals if all_goals else result.goals[:1]
            total = len(result.goals)
            goal_label = f"Goals at failure point" if all_goals else f"Goal at failure point (1 of {total})"
            lines.append("")
            lines.append(f"=== {goal_label} ({stuck_str}) ===")
            for i, g in enumerate(display_goals):
                if i > 0:
                    lines.append("")
                if g.get('asms'):
                    for asm in g['asms']:
                        lines.append(f"  {asm}")
                    lines.append("  " + "-" * 40)
                lines.append(f"  {g['goal']}")

        # Error footer for truncation safety
        error_footer = (
            f"ERROR: PROOF BROKEN at {fail_str}. "
            f"Fix the broken tactic before inspecting later positions."
        )
    else:
        # Normal path: replay succeeded (or position is at/before the failure)
        loc = tactic_to_loc(result.tactic_idx)
        loc_str = f"Line {loc[0]} col {loc[1]}, " if loc else ""
        lines.append(f"{loc_str}Proof position")
        if result.error and not is_proof_complete:
            error_footer = f"ERROR: {result.error}"
        lines.append("")
        if result.goals:
            display_goals = result.goals if all_goals else result.goals[:1]
            total = len(result.goals)
            if all_goals:
                lines.append(f"=== Goals ({total}) ===")
            else:
                lines.append(f"=== Goal (1 of {total}) ===")
            for i, g in enumerate(display_goals):
                if i > 0:
                    lines.append("")  # Blank line between goals
                if g.get('asms'):
                    for asm in g['asms']:
                        lines.append(f"  {asm}")
                    lines.append("  " + "-" * 40)
                lines.append(f"  {g['goal']}")
        elif is_proof_complete:
            lines.append("=== Goals ===")
            lines.append("No goals (proof complete)")
        else:
            lines.append("=== Goals ===")
            lines.append("No goals (proof complete)")

    # Suggest extracting by/>- subproof into a suspend/Resume block
    if result.inside_by and not result.error:
        lines.append("")
        lines.append("[Inside by/>- subproof. Consider extracting into a suspend/Resume block "
                     "for independent verification and easier editing.]")

    # Add timing info if available
    if result.timings:
        t = result.timings
        lines.append("")
        method = 'reused' if t.get('reused_state') else ('incremental' if t.get('incremental') else ('checkpoint' if t.get('used_checkpoint') else 'replay'))
        lines.append(f"[Timing: total={t.get('total', 0)*1000:.0f}ms, "
                     f"replay={t.get('replay', 0)*1000:.0f}ms, "
                     f"method={method}]")

    _schedule_gc(session)
    return _truncate_output("\n".join(lines), max_output, footer=error_footer)


@mcp.tool()
async def hol_check_proof(
    theorem: str,
    file: str = None,
    workdir: str = None,
    trace: bool = True,
    session: str = "default",
) -> str:
    """Check if a theorem's proof completes after editing.

    Use this after editing a proof to see if it works now. More reliable than
    hol_state_at with line numbers which may be stale after edits.

    Args:
        theorem: Theorem name to check
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        trace: If True, include full per-step timing trace
        session: Session name (default: "default")

    Returns: Whether proof completes, failure location, brief goal summary.
             With trace=True, also includes per-step timing and goal counts.
    """
    cursor = await _get_cursor(session)

    # Auto-init if file provided
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    # Re-parse file to pick up edits
    try:
        cursor._reparse_if_changed()
    except FileNotFoundError:
        return f"ERROR: File not found: {cursor.file}"

    # Enter theorem and get step plan
    enter_result = await cursor.enter_theorem(theorem)
    if "error" in enter_result:
        return f"ERROR: {enter_result['error']}"

    thm = cursor._get_theorem(theorem)
    if not thm:
        return f"ERROR: Theorem '{theorem}' not found"

    lines = [
        f"Theorem: {theorem}",
        f"Lines: {thm.start_line}-{thm.proof_end_line - 1}",
        "",
    ]

    if thm.has_cheat:
        lines.append("Status: CHEAT (not verified)")
        lines.append("NOTE: Tactics before 'cheat' are not replayed in this mode.")
        lines.append("      Remove 'cheat' and rerun hol_check_proof for full replay.")
        return "\n".join(lines)

    # Oracle tags are populated after execute_proof_traced (calls verify_theorem_json).
    # We check them after execution below.

    # Execute proof (clean mode by default - matches holmake, uses cache)
    trace_data = await cursor.execute_proof_traced(theorem)
    
    if not trace_data:
        if thm.kind == "Definition" and thm.proof_body:
            # Definition blocks can't use execute_proof_traced (TC goal context).
            # Fall back to state_at at the End line to check proof completion.
            result = await cursor.state_at(thm.proof_end_line - 1, col=1)
            # "no goals" error from goals_json means proof completed successfully
            no_goals_ok = result.error and "no goals" in result.error
            if not result.goals or no_goals_ok:
                lines.append(f"Status: OK (Definition termination proof)")
            elif result.error:
                lines.append(f"Status: FAILED")
                lines.append(f"Error: {result.error}")
            else:
                lines.append(f"Status: INCOMPLETE ({len(result.goals)} goals remaining)")
            return "\n".join(lines)
        lines.append("Status: NO TACTICS (trivial or unparseable)")
        return "\n".join(lines)

    # Find failure point
    failed_idx = None
    for i, entry in enumerate(trace_data):
        if entry.error or (i == len(trace_data) - 1 and entry.goals_after != 0):
            failed_idx = i
            break

    # Compute absolute line:col from proof_body offset using file content
    def offset_to_pos(offset):
        if not thm.proof_body or offset < 0:
            return _file_offset_to_line_col(thm.proof_body_offset, cursor._content)
        return _file_offset_to_line_col(thm.proof_body_offset + offset, cursor._content)

    # Get tactic start/end range
    def tactic_range(idx):
        if idx is None or idx >= len(cursor._step_plan):
            return (thm.proof_start_line, 1), (thm.proof_start_line, 1)
        start_offset = cursor._step_plan[idx - 1].end if idx > 0 else 0
        end_offset = cursor._step_plan[idx].end
        return offset_to_pos(start_offset), offset_to_pos(end_offset)

    final = trace_data[-1]
    total_ms = sum(e.real_ms for e in trace_data)
    total_steps = len(trace_data)
    
    if final.error:
        lines.append(f"Status: FAILED at step {failed_idx + 1}/{total_steps} ({total_ms}ms)")
        lines.append(f"Error: {final.error}")
    elif final.goals_after == 0:
        oracles = cursor._theorem_oracles.get(theorem, [])
        if oracles:
            lines.append(f"Status: OK ({total_ms}ms, {total_steps} steps) ⚠ depends on cheat")
        else:
            lines.append(f"Status: OK ({total_ms}ms, {total_steps} steps)")
        if not trace and not oracles:
            return "\n".join(lines)
    else:
        lines.append(f"Status: INCOMPLETE at step {len(trace_data)}/{total_steps} ({total_ms}ms)")

    # Per-step timing trace (when requested, or always on failure/incomplete)
    if trace:
        lines.append("")
        for i, entry in enumerate(trace_data, 1):
            (sp, sc), (ep, ec) = tactic_range(i - 1)
            loc = f"line/col {sp}:{sc}-{ep}:{ec}"
            cmd_text = entry.cmd.strip().replace('\n', ' ')
            if len(cmd_text) > 60:
                cmd_text = cmd_text[:57] + "..."
            lines.append(f"Step {i} ({loc}): {cmd_text}")
            if entry.error:
                lines.append(f"  ERROR: {entry.error}")
            else:
                gb = entry.goals_before if entry.goals_before is not None else "?"
                ga = entry.goals_after if entry.goals_after is not None else "?"
                lines.append(f"  {entry.real_ms}ms | Goals: {gb} -> {ga}")
        lines.append("")

    # Show failing tactic with location (when not in trace mode, which already shows all steps)
    if not trace and failed_idx is not None and failed_idx < len(trace_data):
        (start_line, start_col), (end_line, end_col) = tactic_range(failed_idx)
        tactic_text = trace_data[failed_idx].cmd.strip().replace('\n', ' ')
        if len(tactic_text) > 80:
            tactic_text = tactic_text[:77] + "..."
        loc = f"line/col {start_line}:{start_col}-{end_line}:{end_col}"
        lines.append(f"Tactic ({loc}): {tactic_text}")

    # Brief goal summary for failure/incomplete
    if failed_idx is not None:
        lines.append("")
        ga = final.goals_after if final.goals_after is not None else "unknown"
        lines.append(f"Remaining: {ga} goal(s)")
        (fail_line, fail_col), _ = tactic_range(failed_idx)
        lines.append(f"Use hol_state_at(line={fail_line}, col={fail_col}) for full goals")

    _schedule_gc(session)
    return "\n".join(lines)


@mcp.tool()
async def hol_file_status(file: str = None, workdir: str = None, timing: bool = True, session: str = "default") -> str:
    """Get current cursor position and file status.

    Args:
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        timing: If True, run all proofs and report timing (slower)
        session: Session name (default: "default")

    Returns: File info, active theorem, theorems with cheats, completion status
    """
    cursor = await _get_cursor(session)

    # Auto-init if file provided and no cursor (or different file)
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    status = cursor.status
    total = len(status['theorems'])

    # When timing, we verify proofs by execution; otherwise use static analysis
    if timing:
        # Run all proofs in clean state (efficient batch verification)
        all_traces = await cursor.verify_all_proofs()

        # Process results
        verified = []
        failed = []  # (name, error_msg)
        cheated = []
        timing_lines = []
        total_ms = 0

        for thm in status['theorems']:
            trace = all_traces.get(thm['name'], [])
            if thm['has_cheat'] or thm.get('proof_failed'):
                if thm['has_cheat']:
                    cheated.append(thm['name'])
                    timing_lines.append(f"  {thm['name']}: (cheat)")
                # proof_failed theorems are handled in the trace branch below
                if thm.get('proof_failed') and not trace:
                    failed.append((thm['name'], "proof failed"))
                    timing_lines.append(f"  {thm['name']}: (proof failed)")
                    continue
            if thm['has_cheat']:
                continue
            if trace:
                thm_ms = sum(e.real_ms for e in trace)
                total_ms += thm_ms
                error = next((e.error for e in trace if e.error), None)
                # Check proof actually completed (no remaining goals)
                final_goals = trace[-1].goals_after if trace else None
                if error:
                    failed.append((thm['name'], error))
                    timing_lines.append(f"  {thm['name']}: {thm_ms}ms (ERROR: {error})")
                elif final_goals is None or final_goals != 0:
                    fg = final_goals if final_goals is not None else "unknown"
                    failed.append((thm['name'], f"incomplete ({fg} goals remain)"))
                    timing_lines.append(f"  {thm['name']}: {thm_ms}ms (INCOMPLETE: {fg} goals)")
                else:
                    # Check oracle tags from HOL4 — detects cheat cascades
                    oracles = cursor._theorem_oracles.get(thm['name'], [])
                    warn = f" ⚠ depends on cheat" if oracles else ""
                    verified.append(thm['name'])
                    timing_lines.append(f"  {thm['name']}: {thm_ms}ms{warn}")
            else:
                # Check if this is a Definition block (loaded as a unit, no timing)
                thm_info = cursor._get_theorem(thm['name']) if cursor else None
                if thm_info and thm_info.kind == "Definition":
                    timing_lines.append(f"  {thm['name']}: (definition)")
                    verified.append(thm['name'])
                else:
                    timing_lines.append(f"  {thm['name']}: (no tactics)")
                    # No tactics = likely just goal statement, count as incomplete
                    failed.append((thm['name'], "no tactics"))

        lines = [
            f"File: {status['file']}",
            f"Progress: {len(verified)}/{total} theorems VERIFIED by execution",
            "",
        ]

        if status['active_theorem']:
            lines.append(f"Active theorem: {status['active_theorem']}")
            lines.append(f"Active tactics: {status['active_tactics']}")
        else:
            lines.append("Active theorem: None")

        # Show failures prominently at top
        if failed:
            lines.append("")
            lines.append(f"FAILED ({len(failed)}):")
            for name, err in failed:
                lines.append(f"  {name}: {err}")

        if cheated:
            lines.append("")
            lines.append(f"Cheated ({len(cheated)}): {', '.join(cheated)}")

        lines.append("")
        lines.append(f"Verified: {', '.join(verified) or 'None'}")

        lines.append("")
        lines.append("Proof times:")
        lines.extend(timing_lines)
        lines.append(f"Total: {total_ms}ms")

        # Warn about potential holmake divergence
        if len(verified) == total - len(cheated) and len(cheated) == 0:
            lines.append("")
            lines.append("NOTE: Run 'holmake' to confirm batch build succeeds.")
            lines.append("      Session may have stale theory deps from prior builds.")
    else:
        # Static analysis only (fast but unreliable)
        complete_in_file = [t['name'] for t in status['theorems'] if not t['has_cheat']]

        lines = [
            f"File: {status['file']}",
            f"Progress: {len(complete_in_file)}/{total} theorems (static, unverified)",
            "",
        ]

        if status['active_theorem']:
            lines.append(f"Active theorem: {status['active_theorem']}")
            lines.append(f"Active tactics: {status['active_tactics']}")
        else:
            lines.append("Active theorem: None")

        lines.append("")
        lines.append(f"No cheat keyword: {', '.join(complete_in_file) or 'None'}")

        if status['cheats']:
            lines.append("")
            lines.append(f"Has cheat keyword ({len(status['cheats'])}):")
            for c in status['cheats']:
                marker = " <--" if c['theorem'] == status['active_theorem'] else ""
                lines.append(f"  {c['theorem']} (line {c['line']}){marker}")

    return "\n".join(lines)



def _install_pi_extension():
    """Install the pi extension to ~/.pi/agent/extensions/."""
    import shutil
    
    # Find the extension file bundled with the package
    ext_source = Path(__file__).parent / "pi_extension" / "hol4-mcp.ts"
    if not ext_source.exists():
        print(f"Error: Extension file not found at {ext_source}", file=sys.stderr)
        sys.exit(1)
    
    # Target directory
    ext_dir = Path.home() / ".pi" / "agent" / "extensions"
    ext_dir.mkdir(parents=True, exist_ok=True)
    
    ext_target = ext_dir / "hol4-mcp.ts"
    shutil.copy2(ext_source, ext_target)
    print(f"Installed pi extension to {ext_target}")


def main():
    """CLI entry point for HOL4 MCP server."""
    import argparse
    import logging

    parser = argparse.ArgumentParser(description="HOL4 MCP Server and Tools")
    subparsers = parser.add_subparsers(dest="command")

    # install-pi subcommand
    subparsers.add_parser("install-pi", help="Install pi extension to ~/.pi/agent/extensions/")

    # serve subcommand (default behavior)
    serve_parser = subparsers.add_parser("serve", help="Run the MCP server (default)")
    serve_parser.add_argument(
        "--transport",
        choices=["stdio", "http", "sse"],
        default="stdio",
        help="Transport protocol (default: stdio)",
    )
    serve_parser.add_argument("--port", type=int, default=8000, help="Port for HTTP/SSE (default: 8000)")
    serve_parser.add_argument("--host", default="127.0.0.1", help="Host for HTTP/SSE (default: 127.0.0.1)")
    serve_parser.add_argument("-v", "--verbose", action="store_true", help="Enable debug logging")
    serve_parser.add_argument("--tactic-timeout", type=float, default=None, help="Max seconds per tactic during proof replay (default: 5.0, or HOL_TACTIC_TIMEOUT env)")

    # Also allow serve options at top level for backwards compat
    parser.add_argument("--transport", choices=["stdio", "http", "sse"], default="stdio", help=argparse.SUPPRESS)
    parser.add_argument("--port", type=int, default=8000, help=argparse.SUPPRESS)
    parser.add_argument("--host", default="127.0.0.1", help=argparse.SUPPRESS)
    parser.add_argument("-v", "--verbose", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--tactic-timeout", type=float, default=None, help=argparse.SUPPRESS)

    args = parser.parse_args()

    if args.command == "install-pi":
        _install_pi_extension()
        return

    # Default to serve behavior
    global TACTIC_TIMEOUT
    if args.tactic_timeout is not None:
        TACTIC_TIMEOUT = args.tactic_timeout

    if args.verbose:
        logging.basicConfig(
            level=logging.DEBUG,
            format="%(asctime)s %(levelname)s %(name)s: %(message)s",
            stream=sys.stderr,
        )
        logging.getLogger("mcp").setLevel(logging.DEBUG)

    if args.transport == "stdio":
        mcp.run(show_banner=False)
    else:
        print(f"HOL MCP server starting on {args.host}:{args.port} ({args.transport})", file=sys.stderr)
        mcp.run(transport=args.transport, host=args.host, port=args.port, show_banner=False)


if __name__ == "__main__":
    main()
