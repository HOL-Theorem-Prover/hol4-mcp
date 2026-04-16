"""Direct HOL subprocess management with clean interrupt support."""

import asyncio
import os
import re
import signal
import time
from pathlib import Path
from typing import Optional

HOLDIR = Path(os.environ.get("HOLDIR", Path.home() / "HOL"))
SCRIPT_DIR = Path(__file__).parent
ETQ_PATH = SCRIPT_DIR / "sml_helpers" / "etq.sml"


def escape_sml_string(s: str) -> str:
    """Escape a string for use in an SML string literal.

    Handles backslashes (e.g., /\\ in HOL terms), quotes, and control chars.
    """
    # Backslash must be first (otherwise we'd double-escape)
    s = s.replace('\\', '\\\\')
    s = s.replace('"', '\\"')
    s = s.replace('\n', '\\n')
    s = s.replace('\t', '\\t')
    s = s.replace('\r', '\\r')
    return s

# ANSI escape sequence pattern (colors, cursor movement, etc.)
_ANSI_ESCAPE_RE = re.compile(r'\x1b\[[0-9;?]*[A-Za-z]')


def strip_ansi(text: str) -> str:
    """Remove ANSI escape codes from text."""
    return _ANSI_ESCAPE_RE.sub('', text)


class HOLSession:
    """Direct HOL subprocess management with clean interrupt support."""

    def __init__(self, workdir: str = ".", strip_ansi: bool = True, env: dict | None = None):
        self.workdir = Path(workdir)
        self.strip_ansi = strip_ansi
        self.env = env  # Extra env vars to merge with os.environ
        self.process: Optional[asyncio.subprocess.Process] = None
        self._buffer = b""
        self._lock = asyncio.Lock()  # Serialize send() to prevent concurrent stdout reads

    async def start(self) -> str:
        """Start HOL subprocess."""
        if self.process and self.process.returncode is None:
            return "HOL already running"

        # Build environment: inherit from os.environ, add any extras
        proc_env = os.environ.copy()
        if self.env:
            proc_env.update(self.env)

        self.process = await asyncio.create_subprocess_exec(
            str(HOLDIR / "bin" / "hol"), "--maxheap", "8192", "--zero",
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            # Merge stderr to stdout: HOL's interactive mode sends all output
            # (warnings, errors, proof state) to stdout. Stderr is empty in
            # practice - only batch tools use it. Merging preserves ordering
            # with null-byte framing.
            stderr=asyncio.subprocess.STDOUT,
            cwd=self.workdir,
            env=proc_env,
            start_new_session=True,  # New process group for clean kill
        )

        # Wait for initial prompt (null-terminated)
        await self._read_response(timeout=60)

        # Load etq.sml (goaltree mode helpers)
        # NOTE: Legacy - cursor now uses goalstack mode with tactic_prefix.sml instead.
        # Kept for backwards compatibility with manual goaltree workflows.
        await self.send(ETQ_PATH.read_text(), timeout=30)

        # Load tactic_prefix for prefix-based replay (includes TacticParse)
        tactic_prefix = SCRIPT_DIR / "sml_helpers" / "tactic_prefix.sml"
        if tactic_prefix.exists():
            await self.send(tactic_prefix.read_text(), timeout=30)

        # Load .hol_init.sml if present
        init_file = self.workdir / ".hol_init.sml"
        if init_file.exists():
            await self.send(init_file.read_text(), timeout=60)

        return f"HOL started (PID {self.process.pid})"

    async def _write_command(self, sml_code: str):
        """Write SML code to stdin with null terminator."""
        self.process.stdin.write(sml_code.encode() + b'\0')
        await self.process.stdin.drain()

    async def _drain_pipe(self):
        """Drain any stale data from pipe before sending new command."""
        while True:
            try:
                chunk = await asyncio.wait_for(
                    self.process.stdout.read(65536),
                    timeout=0.01
                )
                if not chunk:
                    break
            except asyncio.TimeoutError:
                break

    async def send(self, sml_code: str, timeout: float = 5) -> str:
        """Send SML code and wait for response."""
        if not self.process or self.process.returncode is not None:
            return "ERROR: HOL not running"

        async with self._lock:
            await self._drain_pipe()
            await self._write_command(sml_code)

            try:
                return await self._read_response(timeout=timeout)
            except asyncio.TimeoutError:
                self.interrupt()
                try:
                    remaining = await self._read_response(timeout=5)
                except asyncio.TimeoutError:
                    remaining = ""
                msg = f"TIMEOUT after {timeout}s - sent interrupt."
                return f"{msg}\n{remaining}" if remaining else msg

    async def _read_response(self, timeout: float) -> str:
        """Read until null terminator, return all segments joined."""
        self._buffer = b""
        async def read_loop():
            while not self._buffer.endswith(b'\0'):
                chunk = await self.process.stdout.read(65536)
                if not chunk:
                    raise RuntimeError("HOL process died unexpectedly")
                self._buffer += chunk

            parts = self._buffer.split(b'\0')
            self._buffer = b""
            result = "\n".join(p.decode() for p in parts if p)
            return strip_ansi(result) if self.strip_ansi else result

        return await asyncio.wait_for(read_loop(), timeout=timeout)

    def interrupt(self):
        """Send SIGINT to entire process group."""
        if self.process and self.process.returncode is None:
            try:
                pgid = os.getpgid(self.process.pid)
                os.killpg(pgid, signal.SIGINT)
                # give time for hol to write to stdout
                time.sleep(0.01)
            except (ProcessLookupError, PermissionError):
                pass

    def kill_sync(self):
        """SIGKILL the HOL process group. Safe from signal handlers / atexit.

        Sync, best-effort: no waits, no asyncio. Used by shutdown paths
        (atexit, SIGTERM) where the event loop may be dead or unsafe to
        re-enter. SIGKILL (not SIGTERM) because we can't afford to wait for
        a graceful shutdown in these contexts.
        """
        if self.process and self.process.returncode is None:
            try:
                pgid = os.getpgid(self.process.pid)
                os.killpg(pgid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError, OSError):
                pass

    async def stop(self):
        """Kill the HOL process group and wait for cleanup."""
        if self.process and self.process.returncode is None:
            try:
                pgid = os.getpgid(self.process.pid)
                os.killpg(pgid, signal.SIGTERM)
            except (ProcessLookupError, PermissionError):
                pass
            # Wait for process to actually terminate
            try:
                await asyncio.wait_for(self.process.wait(), timeout=5)
            except asyncio.TimeoutError:
                # Force kill if it doesn't terminate
                try:
                    self.process.kill()
                    await self.process.wait()
                except Exception:
                    pass
        self.process = None
        self._buffer = b""

    @property
    def is_running(self) -> bool:
        return self.process is not None and self.process.returncode is None

    async def __aenter__(self):
        await self.start()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        await self.stop()
