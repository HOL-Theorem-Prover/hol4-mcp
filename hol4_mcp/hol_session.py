"""Direct HOL subprocess management with clean interrupt support."""

import asyncio
import os
import re
import signal
import time
from pathlib import Path
from typing import Optional

from .failure_evidence import FailureEvidence

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


# HOL diagnostics that carry information no structured channel reproduces: the
# goal printer's same-name/different-type warning, parser messages about
# invented type variables and overload resolution. They ride the SUCCESS path,
# so unless they are harvested here they reach the caller only by accident.
_DIAGNOSTIC_RE = re.compile(r'^[ \t]*(WARNING:.*|<<HOL message:.*)$', re.M)
_FAILURE_RE = re.compile(
    r'^(?:Exception[- ]|Fail |TIMEOUT|poly: : error:|parse error at )|'
    r'"error"\s*:\s*"[^"\s]', re.M)

BUSY_TEXT = ("HOL is still busy with an earlier command that did not stop on "
             "SIGINT.")

# Compiles only against a TacticParse whose combinator fragments carry spans,
# the shapes sml_helpers/tactic_prefix.sml matches.
_TACTICPARSE_PROBE = (
    "val _ = (TacticParse.FOpenThen1 (0, 0), "
    "TacticParse.FOpenBy ((0, 0), (0, 0)), "
    "TacticParse.FOpenSufficesBy ((0, 0), (0, 0)));")


class HOLSession:
    """Direct HOL subprocess management with clean interrupt support."""

    # Lost-reply watch (`_await_reply`): seconds between checks, and idle
    # checks in a row before HOL is probed.
    LOST_REPLY_INTERVAL = 5.0
    LOST_REPLY_CHECKS = 2

    def __init__(self, workdir: str = ".", strip_ansi: bool = True, env: dict | None = None):
        self.workdir = Path(workdir)
        self.strip_ansi = strip_ansi
        self.env = env  # Extra env vars to merge with os.environ
        self.process: Optional[asyncio.subprocess.Process] = None
        self._buffer = b""
        self._last_raw = b""  # the bytes of the last frame read, NULs kept
        self._lock = asyncio.Lock()  # Serialize send() to prevent concurrent stdout reads
        # (command, diagnostic line) pairs, so a reader can separate what HOL
        # said about the caller's own tactics from prefix-loading chatter.
        self.diagnostics: list[tuple[str, str]] = []
        # Diagnostics ever recorded: `diagnostics` keeps only the newest 500,
        # so a reader takes its own as the last (seen - seen_before) entries.
        self.diagnostics_seen = 0
        self._resync_seq = 0              # distinct sentinel per resync
        # A command timed out and HOL has not answered a sentinel since: it is
        # still running, so no new command may be written behind it.
        self.busy = False
        # A lost-reply probe's sentinel whose own reply has not been read yet.
        self._unclaimed_sentinel = False
        self.maxheap_mb: int | None = None  # effective limit of the live process
        self.failure_evidence = FailureEvidence()
        self.request_context: dict = {}

    async def start(self) -> str:
        """Start HOL subprocess."""
        if self.process and self.process.returncode is None:
            return "HOL already running"

        # Build environment: inherit from os.environ, add any extras
        proc_env = os.environ.copy()
        if self.env:
            proc_env.update(self.env)

        # Keep the historical default; large projects may opt in explicitly.
        # Validate before spawning so a typo cannot silently select a limit.
        raw_heap = proc_env.get("HOL4_MCP_MAXHEAP_MB", "8192")
        try:
            heap_mb = int(raw_heap)
        except (TypeError, ValueError):
            raise ValueError("HOL4_MCP_MAXHEAP_MB must be an integer >= 256") from None
        if heap_mb < 256:
            raise ValueError("HOL4_MCP_MAXHEAP_MB must be an integer >= 256")

        self.process = await asyncio.create_subprocess_exec(
            str(HOLDIR / "bin" / "hol"), "--maxheap", str(heap_mb), "--zero",
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
        self.maxheap_mb = heap_mb

        try:
            # Wait for initial prompt (null-terminated).
            await self._read_response(timeout=60)

            # CompilerSpecific is compiled into hol.state by poly-init.ML but
            # ordinary REPL startup does not register it with Meta.loadedMods.
            # holdeptool can therefore report it for Q-filter-expanded source,
            # and a later `load "CompilerSpecific"` spuriously searches for a
            # nonexistent .ui.  Mirror HOL's LSP startup registration here.
            output = await self.send('Meta.fakeload "CompilerSpecific";', timeout=5)
            if _FAILURE_RE.search(output) or output.startswith("ERROR:"):
                raise RuntimeError(f"Failed to register CompilerSpecific: {output}")

            output = await self.send(_TACTICPARSE_PROBE, timeout=10)
            if _FAILURE_RE.search(output) or output.startswith("ERROR:"):
                raise RuntimeError(
                    f"the HOL at {HOLDIR} is too old for hol4-mcp: its "
                    f"TacticParse lacks the positioned combinators (FOpenThen1, "
                    f"FOpenBy and FOpenSufficesBy carrying spans). Update HOL to "
                    f"current master and rebuild it.")

            # etq supports manual goaltree workflows; tactic_prefix supplies
            # goalstack replay. A failed helper/init load is a failed startup.
            startup_files = (
                (ETQ_PATH, 30),
                (SCRIPT_DIR / "sml_helpers" / "tactic_prefix.sml", 30),
                (self.workdir / ".hol_init.sml", 60),
            )
            for path, budget in startup_files:
                if path != ETQ_PATH and not path.exists():
                    continue
                output = await self.send(path.read_text(), timeout=budget)
                if _FAILURE_RE.search(output) or output.startswith("ERROR:"):
                    raise RuntimeError(f"Failed to load {path.name}: {output}")
        except BaseException:
            # __aexit__ is not called if __aenter__/startup raises, and the
            # server cannot register this session until startup succeeds.
            # Include cancellation so an abandoned request cannot orphan HOL.
            await self.stop()
            raise

        return f"HOL started (PID {self.process.pid}, maxheap={heap_mb} MB)"

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

    async def resync(self, timeout: float = 30) -> bool:
        """Re-align the pipe after a `send` was abandoned mid-read.

        Cancelling a send (an overall-budget abort, which SIGINTs HOL) leaves
        the aborted command's reply unwritten. HOL emits it while unwinding —
        measured from 0.2 ms to 352 ms — long after `_drain_pipe`'s 10 ms poll
        gives up, so the next command reads the ABORTED command's frame and
        every reply after it is off by one, indefinitely. Write a sentinel and
        swallow frames until its own reply arrives.
        """
        if not self.process or self.process.returncode is not None:
            return False
        async with self._lock:
            return (await self._realign(timeout))[0]

    async def _realign(self, timeout: float) -> tuple[bool, str]:
        """`resync`'s body, for a caller that holds the send lock: whether
        HOL's own reply to a sentinel arrived in time, and the text of the
        frames swallowed before it.

        A command interrupted by SIGINT may never get its reply frame: HOL
        returns to the prompt without one. Waiting for that reply would last
        the caller's whole budget while HOL sits idle; the sentinel's reply
        always comes once HOL reads input again.
        """
        self._resync_seq += 1
        marker = f"HOL_MCP_RESYNC_{self._resync_seq}"
        self._buffer = b""
        swallowed = []
        try:
            await self._write_command(f'print "{marker}\\n";')
        except Exception:
            return False, ""
        deadline = time.monotonic() + timeout
        while True:
            left = deadline - time.monotonic()
            if left <= 0:
                return False, "\n".join(swallowed)
            try:
                frame = await self._read_response(timeout=left)
            except (asyncio.TimeoutError, RuntimeError):
                return False, "\n".join(swallowed)
            if marker in frame:
                self.busy = False
                self._unclaimed_sentinel = False
                return True, "\n".join(swallowed)
            swallowed.append(frame)

    async def interrupt_and_realign(self, waits=(5, 10)) -> bool:
        """SIGINT HOL and wait for a sentinel's reply, once per entry of
        `waits` (seconds). False, with the session marked busy, when HOL
        never answered: it ignores SIGINT, and only stopping it ends that."""
        if not self.is_running:
            return False
        async with self._lock:
            for wait in waits:
                self.interrupt()
                if (await self._realign(wait))[0]:
                    return True
            self.busy = True
            return False

    async def drain_stale(self):
        """Drop residual output, holding the send lock.

        `_drain_pipe` reads stdout directly, so calling it while another
        coroutine is inside `send` raises "read() called while another
        coroutine is already waiting for incoming data". Callers outside
        `send` must come through here.
        """
        if not self.process or self.process.returncode is not None:
            return
        async with self._lock:
            await self._drain_pipe()

    async def send(self, sml_code: str, timeout: float = 5) -> str:
        """Send SML code and wait for response."""
        if not self.process or self.process.returncode is not None:
            return "ERROR: HOL not running"

        async with self._lock:
            if ((self.busy and not (await self._realign(timeout=1))[0])
                    or (self._unclaimed_sentinel and not (await self._realign(timeout=5))[0])):
                self.busy = True
                return (f"ERROR: {BUSY_TEXT} Nothing was sent. hol_interrupt "
                        f"may stop it; hol_stop ends the session (the next call "
                        f"restarts HOL and reloads the prefix).")
            await self._drain_pipe()
            await self._write_command(sml_code)

            try:
                return self._note_diagnostics(
                    sml_code, await self._await_reply(timeout))
            except asyncio.TimeoutError:
                partial = self._buffer.decode("utf-8", errors="replace")
                self.interrupt()
                aligned, remaining = await self._realign(timeout=5)
                if not aligned and not self.is_running:
                    raise RuntimeError(await self._death_reason())
                if aligned:
                    msg = f"TIMEOUT after {timeout}s - sent interrupt."
                else:
                    self.busy = True
                    msg = (f"TIMEOUT after {timeout}s - sent interrupt, but HOL "
                           f"did not return to the prompt: {BUSY_TEXT} hol_stop "
                           f"ends the session (the next call restarts HOL and "
                           f"reloads the prefix).")
                self._record_failure(sml_code, partial + "\n" + remaining, "timeout")
                return self._note_diagnostics(
                    sml_code, f"{msg}\n{remaining}" if remaining else msg,
                    record_failure=False)
            except (asyncio.CancelledError, RuntimeError) as exc:
                self._record_failure(sml_code,
                    self._buffer.decode("utf-8", errors="replace") + "\n" + str(exc),
                    "cancelled" if isinstance(exc, asyncio.CancelledError) else "process failure")
                raise

    async def _await_reply(self, timeout: float) -> str:
        """`_read_response`, watching for a reply that will never come.

        HOL can finish a command without sending its reply frame (a SIGINT
        from outside the server stops it that way). When no byte has arrived
        and HOL has used no CPU for LOST_REPLY_CHECKS checks in a row, write a
        sentinel: HOL reads it only once the command is over, so if the
        sentinel's reply comes with no reply before it, the command's own was
        lost. A command that merely sleeps answers first and is returned as
        usual; the sentinel's reply is then swallowed by the next send."""
        reader = asyncio.ensure_future(self._read_response(timeout))
        idle_checks, seen, sentinel, claimed = 0, 0, None, False
        try:
            while True:
                done, _ = await asyncio.wait({reader}, timeout=self.LOST_REPLY_INTERVAL)
                if done:
                    frame = reader.result()
                    if sentinel is None:
                        return frame
                    claimed = True
                    if sentinel in frame:
                        # One read can hold the command's reply and then the
                        # sentinel's: the reply was lost only when no frame
                        # ended before the sentinel's, not even an empty one.
                        raw = self._last_raw
                        if b"\0" in raw[:raw.find(sentinel.encode())]:
                            return frame[:frame.index(sentinel)].rstrip()
                        return (f"ERROR: HOL finished this command without sending "
                                f"its reply (idle for {idle_checks * self.LOST_REPLY_INTERVAL:g}s"
                                f" with no output); its output is lost. The session "
                                f"is aligned again: re-run the command.")
                    self._unclaimed_sentinel = True
                    return frame
                if sentinel is not None:
                    continue
                if len(self._buffer) != seen or await self.is_computing() is not False:
                    seen, idle_checks = len(self._buffer), 0
                    continue
                idle_checks += 1
                if idle_checks >= self.LOST_REPLY_CHECKS:
                    self._resync_seq += 1
                    sentinel = f"HOL_MCP_RESYNC_{self._resync_seq}"
                    await self._write_command(f'print "{sentinel}\\n";')
        finally:
            if sentinel is not None and not claimed:
                self._unclaimed_sentinel = True
            if not reader.done():
                reader.cancel()
                await asyncio.wait({reader})

    def _record_failure(self, command: str, response: str, kind: str) -> None:
        self.failure_evidence.record(command, response, kind,
            workdir=str(self.workdir), pid=self.process.pid if self.process else None,
            maxheap_mb=self.maxheap_mb, context=dict(self.request_context),
            timestamp=time.time())

    def _note_diagnostics(self, command: str, output: str,
                           record_failure: bool = True) -> str:
        """Record HOL diagnostics from one reply; returns the reply unchanged."""
        for m in _DIAGNOSTIC_RE.finditer(output):
            self.diagnostics.append((command, m.group(1).strip()))
            self.diagnostics_seen += 1
        if len(self.diagnostics) > 500:
            del self.diagnostics[:-500]
        if record_failure and _FAILURE_RE.search(output):
            self._record_failure(command, output, "HOL error")
        return output

    async def _read_response(self, timeout: float) -> str:
        """Read until null terminator, return all segments joined."""
        self._buffer = b""
        async def read_loop():
            while not self._buffer.endswith(b'\0'):
                chunk = await self.process.stdout.read(65536)
                if not chunk:
                    raise RuntimeError(await self._death_reason())
                self._buffer += chunk

            parts = self._buffer.split(b'\0')
            self._last_raw, self._buffer = self._buffer, b""
            result = "\n".join(p.decode("utf-8", errors="replace") for p in parts if p)
            return strip_ansi(result) if self.strip_ansi else result

        return await asyncio.wait_for(read_loop(), timeout=timeout)

    async def _death_reason(self) -> str:
        """Diagnostic for unexpected HOL death. Detects memcg OOM."""
        try:
            rc = await asyncio.wait_for(self.process.wait(), timeout=0.5)
        except asyncio.TimeoutError:
            return "HOL process died unexpectedly (no exit code yet)"
        if rc == -signal.SIGKILL:
            return (
                "HOL process OOM-killed (SIGKILL from kernel cgroup). "
                "The tactic or goal exceeded the memory cap. "
                "Simplify the tactic (avoid large rewrites/EVAL on big terms), "
                "split the lemma, or reduce case-splits."
            )
        if rc is not None and rc < 0:
            return f"HOL process killed by signal {-rc} (returncode={rc})"
        return f"HOL process died unexpectedly (returncode={rc})"

    async def is_computing(self, window: float = 0.3) -> bool | None:
        """Whether HOL's process group used CPU over `window` seconds; None
        where /proc is unavailable."""
        if not self.is_running:
            return False
        try:
            pgid = os.getpgid(self.process.pid)
        except (ProcessLookupError, PermissionError):
            return False

        def ticks():
            total = 0
            for entry in os.listdir("/proc"):
                if not entry.isdigit():
                    continue
                try:
                    with open(f"/proc/{entry}/stat", encoding="utf-8",
                              errors="replace") as stream:
                        fields = stream.read().rsplit(")", 1)[1].split()
                except (OSError, IndexError):
                    continue
                if int(fields[2]) == pgid:
                    total += int(fields[11]) + int(fields[12])
            return total
        try:
            before = ticks()
            await asyncio.sleep(window)
            return ticks() > before
        except OSError:
            return None

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
            except (ProcessLookupError, PermissionError, OSError):
                pass
            # Wait for process to actually terminate
            try:
                await asyncio.wait_for(self.process.wait(), timeout=5)
            except asyncio.TimeoutError:
                # Force kill entire group if it doesn't terminate
                self.kill_sync()
                try:
                    await asyncio.wait_for(self.process.wait(), timeout=2)
                except Exception:
                    pass
        self.process = None
        self._buffer = b""
        self.busy = False
        self._unclaimed_sentinel = False

    @property
    def is_running(self) -> bool:
        return self.process is not None and self.process.returncode is None

    async def __aenter__(self):
        await self.start()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        await self.stop()
