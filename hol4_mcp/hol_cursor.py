"""Proof cursor for navigating through theorems without reloading."""

import asyncio
import hashlib
import re
import time
import uuid
from dataclasses import dataclass, field
from pathlib import Path

from .hol_file_parser import (
    TheoremInfo, parse_theorems, LocalBlock, parse_local_blocks,
    build_line_starts, line_col_to_offset, HOLParseError,
    parse_step_plan_output, StepPlan, step_text_start,
    construct_start_line, _find_json_line, suspension_base,
)
from .hol_session import HOLSession, HOLDIR, escape_sml_string
from .budgets import PER_THEOREM_TIMEOUT, PREFIX_LOAD_TIMEOUT, dep_load_timeout


@dataclass(frozen=True)
class SessionPosition:
    """Immutable snapshot of where the HOL session is within the active theorem.

    Updated atomically — only state_at sets this. All other methods
    read from it but never mutate it. This prevents the tracking state
    from getting out of sync (which silently killed incremental/reuse paths).
    """
    tactic_idx: int = 0          # Step index (0 = before any tactic)
    content_hash: str = ""       # File hash when this position was established
    initialized: bool = False     # True after goal setup + successful replay

    def can_reuse(self, current_hash: str) -> bool:
        """Can we reuse this position without any replay?"""
        return self.initialized and self.content_hash == current_hash

    def at_step(self, idx: int, hash_: str) -> 'SessionPosition':
        """New position at a step boundary."""
        return SessionPosition(tactic_idx=idx,
                               content_hash=hash_, initialized=True)




_ANTIQUOTE_RE = re.compile(
    r"\^(?:\(((?:[^()]|\((?:[^()]|\([^()]*\))*\))*)\)|([A-Za-z_][A-Za-z0-9_']*))")


def definition_quotation(body: str) -> str:
    """The SML `term frag list` for a Definition body, as HOL's quotation
    filter compiles it: `^x` / `^(e)` antiquote SML values in scope, and
    `:^ty` a type. Inside a quotation `^` has no other reading."""
    parts, pos = [], 0
    for m in _ANTIQUOTE_RE.finditer(body):
        if m.start() > pos:
            parts.append(f'QUOTE "{escape_sml_string(body[pos:m.start()])}"')
        expr = m.group(1) if m.group(1) is not None else m.group(2)
        in_type = re.search(r":\s*$", body[pos:m.start()]) is not None
        parts.append(f"ANTIQUOTE (ty_antiq ({expr}))" if in_type
                     else f"ANTIQUOTE ({expr})")
        pos = m.end()
    if pos < len(body) or not parts:
        parts.append(f'QUOTE "{escape_sml_string(body[pos:])}"')
    return "[" + ", ".join(parts) + "]"


def _try_find_json_line(output: str, context: str = "") -> dict:
    """Best-effort JSON parse from HOL output. Returns {} on failure."""
    try:
        return _find_json_line(output, context)
    except HOLParseError:
        return {}


def _line_is_error_marker(s: str) -> bool:
    """True iff a single output line GENUINELY signals a HOL/Poly error.

    Deliberately marker-based: it must NOT fire on a printed goal term merely
    because it contains the substring 'error'/'exception' inside an identifier
    or constructor (e.g. `Rerr`, `Rtype_error`, `no_ReturnException`). A failing
    proof prints its goal — which routinely mentions such constructors — BEFORE
    the real exception, so a substring match grabs the goal line and misreports
    a slow/aborted proof as a tactic failure.
    """
    if s.startswith("TIMEOUT"):
        return True
    if s.startswith("Exception-") or s.startswith("Exception "):
        return True
    if "raised exception" in s.lower():
        return True
    if "HOL_ERR" in s:
        return True
    if "poly: : error:" in s.lower():
        return True
    if re.match(r'parse error at \d+:\d+', s):
        return True
    if s.startswith("Fail "):
        return True
    return False


def _error_reason(output: str, limit: int = 240) -> str:
    """Compact one-line reason from HOL error output (for _failed_proofs).

    Returns a TIMEOUT reason for budget timeouts, otherwise the first line
    carrying a GENUINE error marker (see _line_is_error_marker), with bounded
    continuation text for Poly/ML's multiline exceptions. Never returns
    a goal-term line just because it contains the substring 'error'/'exception'
    — that misreported slow/aborted proofs as tactic failures (the
    `[auto-cheated deps: foo (error: | (SOME (Rerr ...)) => T)]` bug).
    """
    stripped = output.lstrip()
    if stripped.startswith("TIMEOUT"):
        first = next((l.strip() for l in stripped.splitlines() if l.strip()), "TIMEOUT")
        return first[:limit]
    lines = output.splitlines()
    for index, line in enumerate(lines):
        s = line.strip()
        if s and _line_is_error_marker(s):
            if s.startswith(("Exception-", "Exception ", "HOL_ERR")):
                parts = [s]
                for continuation in lines[index + 1:index + 17]:
                    if parts[-1].endswith("raised") or sum(map(len, parts)) >= limit:
                        break
                    parts.append(continuation.strip())
                s = " ".join(part for part in parts if part)
            return f"error: {s[:limit]}"
    return "could not validate (no recognizable error marker; proof likely aborted/timed out)"


def _trace_reason(trace: list["TraceEntry"], limit: int = 120) -> str:
    """Compact reason from a verify trace (for _failed_proofs)."""
    for i, entry in enumerate(trace):
        if entry.error:
            e = entry.error.strip()
            kind = "timeout" if e.upper().startswith("TIMEOUT") else "error"
            at = f" at step {i + 1}" if entry.cmd else ""
            return f"{kind}{at}: {e[:limit]}"
    if trace and trace[-1].goals_after not in (0, None):
        return f"proof incomplete ({trace[-1].goals_after} goals remaining)"
    return "proof failed"


def _is_interrupt_reply(output: str) -> bool:
    """A reply HOL gave because SIGINT stopped the command from outside —
    hol_interrupt, a signal sent by hand — not the session's own timeout,
    whose TIMEOUT reply carries the same exception line."""
    return (not output.startswith("TIMEOUT")
            and any(line.startswith("Exception- Interrupt raised")
                    for line in output.split("\n")))


def _is_hol_error(output: str) -> bool:
    """Check if HOL output indicates an actual error (not just a warning).

    Returns True for real errors like:
    - SML exceptions ("Exception-", "raised exception")
    - HOL errors ("HOL_ERR")
    - Poly/ML errors ("poly: : error:")
    - Tactic failures ("Fail ")
    - TIMEOUT strings from HOL session

    Returns False for:
    - HOL warnings/messages ("<<HOL message:", "<<HOL warning:")
    - The word "Exception" in identifiers (e.g., "no_ReturnException")
    - "goal has already been proved" (proof completed early, not an error)
    """
    if output.startswith("TIMEOUT"):
        return True
    if output.lstrip().startswith("ERROR:") or output.lstrip().startswith("Error:"):
        return True
    # "goal has already been proved" means proof completed - not an error
    if "goal has already been proved" in output:
        return False
    # Poly/ML uncaught exception format: "Exception- Fail ..." or "Exception- HOL_ERR ..."
    if any(line.startswith("Exception- ") for line in output.split('\n')):
        return True
    if "HOL_ERR" in output:
        return True
    if "poly: : error:" in output.lower():
        return True
    # HOLSourceParser error format: "parse error at <line>:<col>: ..."
    if any(re.match(r'parse error at \d+:\d+', line) for line in output.split('\n')):
        return True
    if "raised exception" in output.lower():
        return True
    # Tactic Fail with message
    if "\nFail " in output or output.startswith("Fail "):
        return True
    return False


# Sends that run the CALLER's own proof work, as opposed to loading the prefix.
_REPLAY_CMD_RE = re.compile(r'^\s*(ef\s*\(|gf\s|e\s*\(|goals_json)')


def _step_label(cmd: str, limit: int = 60) -> str:
    """A readable tactic snippet from a replay command."""
    text = " ".join(cmd.split()).rstrip(';')
    m = re.match(r'^ef\s*\(\s*goalFrag\.\w+\s*\((.*)\)\s*\)$', text)
    if m:
        text = m.group(1).strip()
    return text if len(text) <= limit else text[:limit] + "..."


def _is_fatal_hol_error(output: str) -> bool:
    """Check if HOL output indicates a fatal error that prevents further loading.

    Unlike _is_hol_error, this ignores normal proof/tactic failures (HOL_ERR from
    proving) since those only mean a theorem wasn't established.

    Returns True for:
    - TIMEOUT
    - Poly/ML syntax/type errors
    - Static Errors
    - Missing-file/load failures (environment/dependency setup problems)
    """
    if output.startswith("TIMEOUT"):
        return True
    # Poly/ML syntax/parse/type errors are fatal
    if "poly: : error:" in output.lower():
        return True
    # HOLSourceParser error format: "parse error at <line>:<col>: ..."
    if any(re.match(r'parse error at \d+:\d+', line) for line in output.split('\n')):
        return True
    # "Static Errors" from Poly/ML parser
    if "Static Errors" in output:
        return True
    # Dependency/setup failures during context loading are fatal
    if "Cannot find file" in output:
        return True
    if "error in load " in output:
        return True
    return False


def _format_context_error(output: str) -> str:
    """Format a context loading error with actionable suggestions.

    Detects common patterns and provides helpful messages:
    - Missing Structure/signature -> dependency/setup hints
    - Missing file with $(VAR) -> env var + restart guidance
    - Timeout -> simplify or increase timeout
    """
    def _missing_file_hint(text: str) -> str | None:
        file_match = re.search(r'Cannot find file\s+"?([^"\n]+)"?', text)
        if not file_match:
            return None

        missing_file = file_match.group(1).strip()
        env_vars = sorted(set(re.findall(r'\$\(([^)]+)\)', missing_file)))

        if env_vars:
            var = env_vars[0]
            return (
                f"Missing dependency file: {missing_file}\n"
                f"Likely cause: unresolved env var $({var}) in Holmakefile INCLUDES\n"
                f"  Fix:\n"
                f"    1) holmake(workdir=..., env={{\"{var}\": \"/abs/path\"}})\n"
                f"    2) hol_setenv(env={{\"{var}\": \"/abs/path\"}}) — it restarts "
                f"the session itself"
            )

        return (
            f"Missing dependency file: {missing_file}\n"
            "  Hint: run 'Holmake' in the script workdir to build dependencies"
        )

    # Missing structure: "Structure (X) has not been declared"
    match = re.search(r'Structure \((\w+)\) has not been declared', output)
    if match:
        struct = match.group(1)
        file_hint = _missing_file_hint(output)
        if file_hint:
            return f"Missing dependency: {struct}\n{file_hint}"
        return (
            f"Missing dependency: {struct}\n"
            "  Hint: run 'Holmake' to build dependencies.\n"
            "  If INCLUDES uses $(...) variables, set them via holmake env + hol_setenv, then hol_restart."
        )

    # Missing signature: "Signature (X) has not been declared"
    match = re.search(r'Signature \((\w+)\) has not been declared', output)
    if match:
        sig = match.group(1)
        file_hint = _missing_file_hint(output)
        if file_hint:
            return f"Missing dependency: {sig}\n{file_hint}"
        return (
            f"Missing dependency: {sig}\n"
            "  Hint: run 'Holmake' to build dependencies.\n"
            "  If INCLUDES uses $(...) variables, set them via holmake env + hol_setenv, then hol_restart."
        )

    # Missing value/constructor (often forward reference or stale prelude assumptions)
    match = re.search(r'Value or constructor \(([^)]+)\) has not been declared', output)
    if match:
        ident = match.group(1)
        line_match = re.search(r':(\d+):\s*error:', output)
        line_hint = f" (line {line_match.group(1)})" if line_match else ""
        return (
            f"Unknown identifier: {ident}{line_hint}\n"
            "  Likely causes:\n"
            "    - forward reference (used before declaration in file order)\n"
            "    - earlier theorem failed, so its name was never bound\n"
            "    - missing prelude/import change (open/load/Theory/Ancestors)\n"
            "  Hint: run hol_check_proof on earlier theorems and run Holmake to confirm file order/build."
        )

    # Missing file (without structure/signature wrapper)
    file_hint = _missing_file_hint(output)
    if file_hint:
        return file_hint

    # Timeout
    if output.startswith("TIMEOUT"):
        return "Timeout executing file content (a definition or proof may be looping)\n  Hint: check for infinite loops or increase timeout"

    # Generic: keep the end, where Poly/ML reports the actual parse/type error.
    # Retain a short beginning for context without letting successful prefix
    # chatter hide the diagnostic that caused context loading to fail.
    limit = 2000
    if len(output) <= limit:
        return output
    head = output[:200].rstrip()
    tail = output[-(limit - 300):].lstrip()
    omitted = len(output) - len(head) - len(tail)
    return f"{head}\n...[{omitted} characters omitted; showing final diagnostics]...\n{tail}"


async def get_script_dependencies(script_path: Path) -> list[str]:
    """Get dependencies using holdeptool.exe.

    Returns all deps from holdeptool. Caller should try to load each one
    and handle "Cannot find file" errors (build-time deps or holmake not run).
    
    Raises FileNotFoundError if holdeptool.exe doesn't exist.
    """
    holdeptool = HOLDIR / "bin" / "holdeptool.exe"
    if not holdeptool.exists():
        raise FileNotFoundError(f"holdeptool.exe not found at {holdeptool}")

    proc = await asyncio.create_subprocess_exec(
        str(holdeptool), str(script_path),
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )
    stdout, stderr = await proc.communicate()
    if proc.returncode != 0:
        raise RuntimeError(
            f"holdeptool.exe failed: {stderr.decode()}"
            # e.g. lexical error when .sml has syntax issues (missing QED, etc.)
        )

    return [line.strip() for line in stdout.decode().splitlines() if line.strip()]


# =============================================================================
# FileProofCursor - File-centric proof state inspection
# =============================================================================

@dataclass
class StateAtResult:
    """Result of state_at() call."""
    goals: list[dict]         # Current goals: [{"asms": [...], "goal": "..."}, ...]
    tactic_idx: int           # Index of tactic at position (0-based)
    tactics_replayed: int     # Step index actually reached (a position, not a
                              # count of commands issued: see _NavResult)
    tactics_total: int        # Total tactics in proof
    file_hash: str            # Content hash when this state was computed
    error: str | None = None  # Error message if replay failed
    timings: dict[str, float] | None = None  # Timing breakdown (ms)
    inside_by: bool = False   # Position is inside a decomposed by/>- subproof (between open/close)
    inside_step_idx: int | None = None  # Step index when position is strictly INSIDE
    # Set when the position inside an opaque step was reached by replaying
    # the step's flat sub-plan (single-goal group entry): {"step", "sub_idx",
    # "sub_total", "start_line", "end_line", "error", "fail_line"}.
    inside_group: dict | None = None
                                        # an opaque step (state shown = step entry)
    warnings: list[str] | None = None   # HOL diagnostics emitted while producing
                                        # this state (success path included)


@dataclass
class _TargetInfo:
    """Intermediate: parsed theorem + target position within it."""
    thm: TheoremInfo
    tactic_idx: int           # Step boundary at/before cursor
    total_tactics: int        # Total steps in step_plan
    incremental_update: tuple[int, int] | None  # (first_diff, old_tactic_idx) or None
    changed: bool             # Whether file content changed
    proof_offset: int = 0     # Target offset within the proof body


@dataclass
class _NavResult:
    """Result of navigation strategy dispatch."""
    reached_idx: int          # Step index the session now sits at, NOT a
                              # command count: "reused" issues nothing and
                              # still reaches the target.
    error_msg: str | None
    strategy: str             # "reused" | "incremental" | "checkpoint" | "replay"


@dataclass
class TraceEntry:
    """Single entry in a proof timing trace."""
    cmd: str                    # Command that was executed
    real_ms: int                # Real time in milliseconds
    usr_ms: int                 # User CPU time in milliseconds
    sys_ms: int                 # System CPU time in milliseconds
    # SML always emits both fields; None should be unreachable (defensive against malformed JSON)
    goals_before: int | None     # Number of goals before execution
    goals_after: int | None      # Number of goals after execution
    error: str | None = None    # Error message if tactic failed
    start_offset: int | None = None  # Start offset in theorem proof_body
    end_offset: int | None = None    # End offset in theorem proof_body


@dataclass
class TheoremCheckpoint:
    """Checkpoint state for a theorem.

    Two types of checkpoints with different semantics:
    - context_path: theory state after loading theorem content (QED → stored).
      Valid prefix for successor theorems. Saved during _load_context_to_line.
    - end_of_proof_path: proof replay state after all tactics (for backup_n).
      NOT a valid prefix — theorem not bound. Saved during state_at.
    """
    theorem_name: str
    tactics_count: int            # Number of tactics when end_of_proof saved
    end_of_proof_path: Path | None = None   # Proof replay checkpoint (for state_at)
    context_path: Path | None = None       # Context checkpoint (theory state, for navigation)
    content_hash: str = ""        # Hash of the file PREFIX through this
                                  # theorem, i.e. the content this saved state
                                  # was produced from (_theorem_prefix_hash)


class FileProofCursor:
    """File-centric proof cursor - agent edits file, cursor inspects state.

    Key design principles:
    - Content hash for change detection (poll-on-demand, no watchdog)
    - Single active theorem at a time
    - Agent edits file directly; cursor is read-only inspector
    - Replay from theorem start for correctness
    """

    def __init__(self, source_file: Path, session: HOLSession, *,
                 checkpoint_dir: Path | None = None,
                 tactic_timeout: float = 5.0):
        """Initialize file proof cursor.

        Args:
            source_file: Path to the SML script
            session: HOL session to use
            checkpoint_dir: Where to store checkpoints (default: .hol/cursor_checkpoints/)
            tactic_timeout: Max seconds per tactic (default 5.0, None=unlimited)
        """
        self.file = source_file
        self.session = session

        # Tactic timeout for build discipline
        self._tactic_timeout = tactic_timeout
        
        # Checkpoint directory: .hol/cursor_checkpoints/ (alongside holmake artifacts)
        if checkpoint_dir is None:
            self._checkpoint_dir = source_file.parent / ".hol" / "cursor_checkpoints"
        else:
            self._checkpoint_dir = checkpoint_dir
        # Per-theorem SaveState paths are never reused within a live cursor.
        # Poly/ML refuses to save over any file in the loaded state's parent
        # chain; a fresh name avoids both that collision and corrupting child
        # checkpoints that still refer to the earlier file.
        self._checkpoint_nonce = uuid.uuid4().hex[:8]
        self._checkpoint_generation = 0

        # Cached file state
        self._content: str = ""
        self._content_hash: str = ""
        self._line_starts: list[int] = []
        self._theorems: list[TheoremInfo] = []
        self._local_blocks: list[LocalBlock] = []

        # Active theorem state
        self._active_theorem: str | None = None
        self._step_plan: list[StepPlan] = []  # Step boundaries aligned with e() commands
        # Hash of self._content at which _step_plan was computed. If it diverges
        # from self._content_hash, _step_plan is stale — _compute_target must
        # reparse. Prevents stale-plan drift when _reparse_if_changed runs via
        # a non-state_at caller (e.g. cursor.status for hol_sessions) and
        # updates _content_hash without re-running goalfrag_step_plan_json.
        self._step_plan_hash: str = ""
        self._pos = SessionPosition()  # Where HOL session is (updated atomically by state_at)
        # Set when a hol_send command may have mutated the live proofManager out
        # from under our position cache (set_goal/e/b/drop_all/set_suspended_goal/…).
        # While true, the next state_at MUST NOT take the `reused` fast path
        # (which blindly returns the live goal) — it re-establishes the goal via
        # checkpoint/replay (cheap: current theorem only) and clears this flag.
        self._session_dirty: bool = False

        # What's been loaded into HOL
        self._loaded_to_line: int = 0
        self._loaded_content_hash: str = ""  # Hash of content up to _loaded_to_line

        # Checkpoint cache: theorem_name -> TheoremCheckpoint
        self._checkpoints: dict[str, TheoremCheckpoint] = {}

        # Base checkpoint (saved after deps loaded, ~132MB once)
        # All theorem checkpoints are saved as children of this (~1.4MB each)
        self._base_checkpoint_path: Path | None = None
        self._base_checkpoint_saved: bool = False

        # Deps-only checkpoint (saved after deps but before file content)
        # Used for clean verification of proofs
        self._deps_checkpoint_path: Path | None = None
        self._deps_checkpoint_saved: bool = False

        # Proof timing cache: theorem_name -> list[TraceEntry]
        # Invalidated when file content changes
        self._proof_traces: dict[str, list[TraceEntry]] = {}

        # Termination condition goals for Definition blocks:
        # Maps definition name -> TC goal string (e.g., "?R. WF R /\ ...")
        # Extracted during context loading BEFORE each Definition
        # block is processed (required because Hol_defn can't be re-called
        # after the constant exists without corrupting theory state).
        self._tc_goals: dict[str, str] = {}

        # Theorems whose proofs failed during content loading and were
        # auto-cheated to prevent cascading compile errors, mapped to a short
        # reason ("timeout >Ns …" / "error: …"). Cleared on file change.
        self._failed_proofs: dict[str, str] = {}
        # Top-level SML spans of the prefix (start, end, reason) that raised
        # when sent: their bindings are missing although loading continued.
        self._prefix_errors: list[tuple[int, int, str]] = []

        # Per-step cost of the last step-by-step replay:
        # (step index, elapsed seconds, "ok" | "budget" | "failed").
        self._step_costs: list[tuple[int, float, str]] = []

        # Oracle tags per theorem from verify_all_proofs.
        # e.g. {"thm_c": ["cheat"]} means thm_c transitively depends on a cheat.
        self._theorem_oracles: dict[str, list[str]] = {}

        # Resume goals: name -> {"asms": [...], "goal": "..."}
        # Extracted during context loading BEFORE each Resume block
        self._resume_goals: dict[str, dict] = {}

        # True when pre-theorem context changed (e.g., open/Theory/Ancestors).
        # Such changes require rebuilding HOL session context from scratch.
        self._needs_session_reinit: bool = False
        self._context_rewind_pending = False

        # Include absent interfaces and earlier load-path candidates: a newly
        # built or newly shadowing artifact invalidates the loaded context too.
        self._dep_artifacts: dict[str, dict[Path, tuple[int, int, int] | None]] = {}
        self._dep_parent_stamps: dict[Path, tuple[tuple | None, bool]] = {}
        self._dep_dangling_links: dict[Path, str] = {}
        self._dep_present_artifacts: list[tuple[str, Path, tuple]] = []
        self._dep_absent_artifacts: dict[Path, list[tuple[str, Path]]] = {}

        # One-line notices about session-level events (reload after an
        # ancestor rebuild, restart into another workdir) for the next tool
        # output; the server takes and clears them (take_notices).
        self._session_notices: list[str] = []
        # O(1) progress metadata; inspection never sends a command to HOL.
        self._phase: dict = {}

        # Seconds spent (re)starting HOL and loading dependencies since the
        # last navigation reported them (`startup=` in the Timing line), and
        # what incurred them, so a slow prefix can be attributed to its cause
        # rather than read as an inherent cost of the file.
        self._startup_seconds: float = 0.0
        self._startup_cause: str | None = None
        # Why the pending full reinit was scheduled (None: not pending, or
        # scheduled without a stated reason).
        self._reinit_reason: str | None = None

        # perf_counter at which the current navigation began replaying the
        # TARGET theorem's own tactics (None until the prefix is in place), so
        # a budget timeout can be attributed to prefix vs target.
        self._target_replay_started: float | None = None

        # (theorem, step index, count) of consecutive edit→navigate cycles
        # that broke at the same step; a passing navigation clears it.
        self._break_streak: tuple[str, int, int] | None = None

        # Prefix-skip mode (state_at(skip_prefix=True)): when on, prefix theorems
        # are bound via `cheat` (statement only) instead of being replayed, so
        # navigation into a target theorem is instant even in a cold, unbuilt
        # theory full of slow/looping proofs. _skipped_thms records which prefix
        # theorems were cheated this way (reported, but NOT as per-theorem
        # auto-cheat failures). Changing the mode forces a clean prefix reload.
        self._skip_prefix: bool = False
        self._skipped_thms: set[str] = set()

    def _compute_hash(self, content: str) -> str:
        """Compute SHA256 hash of content."""
        return hashlib.sha256(content.encode()).hexdigest()

    def _first_changed_line(self, old_content: str, new_content: str) -> int | None:
        """Return first line number (1-indexed) where content differs, or None if identical."""
        old_lines = old_content.split('\n')
        new_lines = new_content.split('\n')

        for i, (old, new) in enumerate(zip(old_lines, new_lines)):
            if old != new:
                return i + 1

        # Length difference (lines added/removed at end)
        if len(old_lines) != len(new_lines):
            return min(len(old_lines), len(new_lines)) + 1

        return None

    def _dep_load_error(self, dep: str, result: str, elapsed: float,
                        budget: float) -> str:
        """Error text for a dependency that failed to load at init."""
        if "Cannot find file" in result:
            return (f"Missing compiled dependency {dep}: {result.strip()}\n"
                    f"Build {dep}.uo in its owning directory (a .dat alone "
                    f"does not provide the compiled interface), then retry "
                    f"navigation; no target proof has run.")
        if "Run out of store" in result:
            heap_mb = getattr(self.session, "maxheap_mb", None)
            return (f"Failed to load dependency {dep}: {result.strip()}\n"
                    f"Interactive maxheap={heap_mb} MB "
                    f"(HOL4_MCP_MAXHEAP_MB); no target proof has run.")
        if not result.lstrip().startswith("TIMEOUT"):
            return f"Failed to load dependency {dep}: {result}"
        holmakefile = Path(self.session.workdir) / "Holmakefile"
        try:
            declares = re.search(r"^\s*HOLHEAP\s*=", holmakefile.read_text(),
                                 re.M) is not None
        except OSError:
            declares = False
        heap = ("declares HOLHEAP" if declares else
                "does not declare HOLHEAP; a heap with the heavy ancestors "
                "pre-loaded makes this load instant")
        return (f"Dependency {dep} timed out loading after {elapsed:.1f}s "
                f"(budget {budget:g}s per dependency, env "
                f"HOL4_MCP_DEP_LOAD_TIMEOUT). The Holmakefile {heap}.")

    # Filesystem timestamps are coarse (kernel tick, or whole seconds on some
    # filesystems): a directory entry created within this window of the
    # directory's own mtime can leave that mtime unchanged, so a stamp taken
    # inside the window cannot prove the directory unchanged.
    _RACY_WINDOW_NS = 2_000_000_000

    @staticmethod
    def _artifact_stamp(path: Path) -> tuple[int, int, int] | None:
        try:
            stat = path.stat()
        except FileNotFoundError:
            return None
        return stat.st_mtime_ns, stat.st_size, stat.st_ino

    async def _record_dep_artifacts(self, deps: list[str]) -> None:
        """Snapshot load candidates, including missing .ui/.uo/.dat files.

        Stop at the first existing file for each suffix, but remember absent
        candidates before it: their appearance could shadow the loaded file.
        Relative loadPath entries are relative to HOL's cwd, not the server's.
        """
        workdir = Path(self.session.workdir).resolve()
        dirs = [workdir]
        out = await self.session.send("!loadPath;", timeout=10)
        for p in re.findall(r'"((?:[^"\\]|\\.)*)"', out):
            path = Path(p)
            dirs.append(path if path.is_absolute() else workdir / path)
        dirs = list(dict.fromkeys(dirs))
        self._dep_parent_stamps = {}
        self._dep_dangling_links = {}
        self._dep_present_artifacts = []
        self._dep_absent_artifacts = {}
        for dep in deps:
            artifacts = self._dep_artifacts[dep] = {}
            for suffix in ("uo", "ui", "dat"):
                candidates = (c for d in dirs for c in
                              (d / ".hol" / "objs" / f"{dep}.{suffix}",
                               d / f"{dep}.{suffix}"))
                for path in candidates:
                    # Sample BEFORE the child: a concurrent creation must not
                    # be hidden behind a newer directory snapshot.
                    parent = path.parent
                    if parent not in self._dep_parent_stamps:
                        self._dep_parent_stamps[parent] = self._directory_sample(parent)
                    stamp = self._artifact_stamp(path)
                    artifacts[path] = stamp
                    if stamp is not None:
                        self._dep_present_artifacts.append((dep, path, stamp))
                        break
                    self._dep_absent_artifacts.setdefault(parent, []).append((dep, path))
                    if path.is_symlink():
                        self._dep_dangling_links[path] = dep

    @staticmethod
    def _directory_stamp(path: Path) -> tuple | None:
        try:
            stat = path.stat()
        except FileNotFoundError:
            return None
        return stat.st_mtime_ns, stat.st_ctime_ns, stat.st_ino, stat.st_dev

    def _directory_sample(self, path: Path) -> tuple[tuple | None, bool]:
        """(stamp, trusted): a stamp is trusted to prove the directory unchanged
        only once its mtime is older than _RACY_WINDOW_NS at sampling time."""
        stamp = self._directory_stamp(path)
        trusted = stamp is None or time.time_ns() - stamp[0] > self._RACY_WINDOW_NS
        return stamp, trusted

    def _check_dep_artifacts(self) -> str | None:
        """First dependency changed, created or removed since initialization.

        A disappearance invalidates the old context too; a mid-build retry must
        report missing interfaces, not validate against an obsolete heap.
        """
        # Large load paths have many absent candidates. An unchanged parent
        # cannot acquire a new directory entry; stat it once per call rather
        # than every absent file, unless its recorded stamp is untrusted
        # (_directory_sample), in which case the candidates are scanned.
        # Existing files and dangling symlinks still need direct stats (the
        # latter's target can appear without changing the link's own directory).
        if not self._dep_artifacts:
            return None
        for dep, path, stamp in self._dep_present_artifacts:
            if self._artifact_stamp(path) != stamp:
                return dep
        for path, dep in self._dep_dangling_links.items():
            if self._artifact_stamp(path) is not None:
                return dep
        parents = {}
        for parent, candidates in self._dep_absent_artifacts.items():
            recorded, trusted = self._dep_parent_stamps[parent]
            parents[parent] = self._directory_sample(parent)
            if trusted and parents[parent][0] == recorded:
                continue
            for dep, path in candidates:
                if self._artifact_stamp(path) is not None:
                    return dep
                if path.is_symlink():
                    self._dep_dangling_links[path] = dep
                else:
                    self._dep_dangling_links.pop(path, None)
        # Retain the pre-child-check samples only after all checks pass.
        self._dep_parent_stamps.update(parents)
        return None

    def _schedule_full_reinit(self, reason: str | None = None) -> None:
        """Rebuild the session from scratch on the next call: drop every
        cache and checkpoint, the deps-only one included.

        ``reason`` is reported with the startup time the reinit costs.
        """
        self._needs_session_reinit = True
        self._reinit_reason = reason
        self._context_rewind_pending = False
        self._loaded_to_line = 0
        self._loaded_content_hash = ""
        self._pos = SessionPosition()
        self._active_theorem = None
        self._invalidate_all_checkpoints()
        self._proof_traces.clear()
        self._tc_goals.clear()
        self._resume_goals.clear()
        self._failed_proofs.clear()
        self._prefix_errors.clear()
        self._theorem_oracles.clear()
        for ckpt_path in [self._base_checkpoint_path, self._deps_checkpoint_path]:
            if ckpt_path and ckpt_path.exists():
                try:
                    ckpt_path.unlink()
                except OSError:
                    pass
        self._base_checkpoint_path = None
        self._deps_checkpoint_path = None
        self._base_checkpoint_saved = False
        self._deps_checkpoint_saved = False

    def take_notices(self) -> list[str]:
        """Session-level notices accumulated since the last call, cleared."""
        out, self._session_notices = self._session_notices, []
        return out

    def _reparse_if_changed(self) -> bool:
        """Re-read and parse file if content changed. Returns True if changed.

        Raises FileNotFoundError if file was deleted.
        """
        content = self.file.read_text()  # Let FileNotFoundError propagate
        content_hash = self._compute_hash(content)

        rebuilt = self._check_dep_artifacts()
        if rebuilt is not None:
            self._dep_artifacts = {}
            self._schedule_full_reinit(
                f"session reload: ancestor {rebuilt} rebuilt since it was loaded")
            self._session_notices.append(
                f"[Session reloaded: ancestor {rebuilt} rebuilt since it was "
                f"loaded; dependencies and prefix replayed from the new artifacts]")

        if content_hash == self._content_hash:
            return False

        # Find first changed line before updating. A fresh cursor's first parse
        # is not an edit: nothing is loaded or cached, and init builds the
        # session that the "edit at line 1, before the first theorem" reading
        # would otherwise schedule a second time.
        old_content = self._content
        first_changed = (self._first_changed_line(old_content, content)
                         if old_content else None)

        self._content = content
        self._content_hash = content_hash
        self._line_starts = build_line_starts(content)
        self._theorems = parse_theorems(content)
        self._local_blocks = parse_local_blocks(content)

        # Invalidate checkpoints and traces for theorems at or after the change
        if first_changed is not None:
            # An edit landing in a suspend/Resume chain that is currently BROKEN
            # (a body auto-cheated, its children orphaned) is invalidated like
            # any other edit: the prefix is truncated to the edited block and,
            # if that block had run, the next enter_theorem rewinds to a context
            # checkpoint — a Poly/ML heap image taken before it ran — which
            # restores markerLib's suspension stores along with everything
            # else, so the fixed block re-registers its labels on the partial
            # path. What a broken chain does owe the caller is an account of
            # the cost its red member adds to every reload; built BEFORE
            # _invalidate_from_line drops the _failed_proofs verdicts it names.
            chain_notice = self._broken_chain_notice(first_changed)

            self._invalidate_from_line(first_changed)
            # Also reset loaded context tracking - can't trust context after change point.
            # The reload resumes at the truncation point, so it must be a construct
            # BOUNDARY: mid-construct, HOL is handed the tail of a
            # Definition/Datatype/Theorem and the resulting "Unknown identifier"
            # is sticky across every later navigation.
            if first_changed <= self._loaded_to_line:
                # Lowering this Python counter does not undo executed ML
                # effects or remove later theorem bindings from the heap.
                # Restore a valid predecessor before replaying the edit.
                self._context_rewind_pending = True
                self._active_theorem = None
                boundary = construct_start_line(content, first_changed)
                # `_loaded_to_line` is EXCLUSIVE — lines 1..n-1 are loaded and
                # the resend starts AT n — so the boundary is the value itself.
                # Storing boundary-1 restarted one line early, handing HOL the
                # last line of whatever precedes the construct; for a multi-line
                # comment that tail parses as terms and surfaces as
                # "Unknown identifier: <word of the comment>". 0 is kept for the
                # first construct, where it means "cold" to the load path.
                self._loaded_to_line = boundary if boundary > 1 else 0
                self._loaded_content_hash = ""  # Empty string = needs recompute

            if chain_notice:
                self._session_notices.append(chain_notice)

            # If change is before first theorem, pre-theorem context may have changed
            # (e.g., open/Theory/Ancestors). Rebuild HOL session on next query.
            first_thm_line = self._theorems[0].start_line if self._theorems else None
            if first_thm_line and first_changed < first_thm_line:
                reason = (f"session reinit: the edit at line {first_changed} "
                          f"precedes the first theorem (line {first_thm_line}), "
                          f"so the header/open context may have changed")
                self._schedule_full_reinit(reason)
                self._session_notices.append(
                    f"[{reason.capitalize()}; HOL restarts, dependencies reload "
                    f"and the prefix replays from line 1]")

        # Clear active theorem if it was renamed/deleted
        if self._active_theorem:
            if not any(t.name == self._active_theorem for t in self._theorems):
                self._active_theorem = None

        return True

    def _get_theorem(self, name: str) -> TheoremInfo | None:
        """Get theorem by name from cached parse."""
        for thm in self._theorems:
            if thm.name == name:
                return thm
        return None

    def _nearest_theorem_ranges(self, line: int, span: int = 2) -> str:
        """Valid line ranges around ``line``, for a bad-position rejection.

        A rejection that names no valid range costs the caller a
        guess-and-retry round trip.
        """
        if not self._theorems:
            return " The file contains no parsed theorem blocks."
        ordered = sorted(self._theorems, key=lambda t: t.start_line)
        before = [t for t in ordered if t.proof_end_line <= line][-span:]
        after = [t for t in ordered if t.start_line > line][:span]
        near = before + after
        if not near:
            near = ordered[:span]
        listed = ", ".join(
            f"{t.name} (lines {t.start_line}-{t.proof_end_line - 1})"
            for t in near
        )
        return f" Nearest theorem blocks: {listed}."

    def _get_theorem_at_position(self, line: int) -> TheoremInfo | None:
        """Get theorem containing the given line number."""
        for thm in self._theorems:
            # Theorem spans from Theorem keyword to QED
            # proof_end_line is "line after QED" (exclusive upper bound)
            # Valid range: start_line <= line < proof_end_line
            if thm.start_line <= line < thm.proof_end_line:
                return thm
        return None

    def _check_stale_state(self) -> bool:
        """Check if loaded content has changed (stale HOL state)."""
        if self._loaded_to_line == 0:
            return False
        # Compare hash of content up to loaded line
        loaded_content = '\n'.join(self._content.split('\n')[:self._loaded_to_line - 1])
        return self._compute_hash(loaded_content) != self._loaded_content_hash

    async def _reinitialize_session_if_needed(self) -> str | None:
        """Rebuild HOL session/context after pre-theorem file edits.

        Needed when imports/theory header/ancestor block changes, since those
        alter top-level context that cannot be safely undone incrementally.

        Returns:
            None on success, or an error string.
        """
        if not self._needs_session_reinit:
            return None
        t_start = time.perf_counter()
        reason, self._reinit_reason = self._reinit_reason, None
        self._startup_cause = reason or (
            "session reinit: HOL restart, dependency reload and prefix "
            "replay from line 1")

        # Restart HOL process for a clean top-level environment
        if self.session.is_running:
            await self.session.stop()
        await self.session.start()

        # Reset runtime tracking before re-init
        self._loaded_to_line = 0
        self._loaded_content_hash = ""
        self._pos = SessionPosition()
        self._active_theorem = None
        self._step_plan = []
        self._step_plan_hash = ""
        self._needs_session_reinit = False

        # Re-run full initialization to rebuild deps/context/checkpoints
        init_result = await self.init()
        self._startup_seconds += time.perf_counter() - t_start
        if init_result.get("error"):
            self._needs_session_reinit = True
            self._reinit_reason = reason
            return init_result["error"]

        return None

    # =========================================================================
    # Checkpoint Management
    # =========================================================================

    def _get_checkpoint_path(self, theorem_name: str, checkpoint_type: str) -> Path:
        """Get path for a checkpoint file."""
        # Sanitize: allow only alphanumeric, underscore, prime (valid SML identifiers)
        safe_name = re.sub(r"[^a-zA-Z0-9_']", "_", theorem_name) or "unnamed"
        return self._checkpoint_dir / f"{safe_name}_{checkpoint_type}.save"

    def _new_checkpoint_path(self, theorem_name: str, checkpoint_type: str) -> Path:
        """Return a fresh per-theorem path safe to save in this live heap.

        Old saves remain until cursor GC because newer child states may name
        them as parents.  Reusing or unlinking one while the heap is live can
        cause SaveState parent collisions or later ENOENT loads.
        """
        safe_name = re.sub(r"[^a-zA-Z0-9_']", "_", theorem_name) or "unnamed"
        self._checkpoint_generation += 1
        return self._checkpoint_dir / (
            f"{safe_name}_{self._checkpoint_nonce}_{self._checkpoint_generation:06d}_"
            f"{checkpoint_type}.save"
        )

    _DEPTH_UNREADABLE = "SaveState hierarchy depth unreadable"

    async def _get_hierarchy_depth(self) -> int | None:
        """Get current PolyML SaveState hierarchy length, or None if the reply
        does not state it.

        The hierarchy is a list of parent states. saveChild(path, N) saves as
        child of entry at index N-1. To save as child of the current state,
        use N = hierarchy length. The length grows as checkpoints are saved,
        so no fixed value can stand in for an unreadable one.
        """
        depth_result = await self.session.send(
            'length (PolyML.SaveState.showHierarchy());', timeout=5
        )
        depth_match = re.search(r'val it = (\d+)', depth_result)
        return int(depth_match.group(1)) if depth_match else None

    async def _save_base_checkpoint(self) -> bool:
        """Save base checkpoint after dependencies loaded.

        This ~132MB checkpoint captures the HOL state after all dependencies
        are loaded. Theorem checkpoints saved as children of this are only ~1.4MB.

        Returns True if saved successfully.
        """
        if self._base_checkpoint_saved:
            return True

        self._checkpoint_dir.mkdir(parents=True, exist_ok=True)
        self._base_checkpoint_path = self._checkpoint_dir / "base_deps.save"
        ckpt_path_str = escape_sml_string(str(self._base_checkpoint_path))

        depth = await self._get_hierarchy_depth()
        if depth is None:
            return False
        # Save child checkpoint at current depth
        result = await self.session.send(
            f'PolyML.SaveState.saveChild ("{ckpt_path_str}", {depth});', timeout=60
        )
        if _is_hol_error(result):
            return False

        self._base_checkpoint_saved = True
        return True

    async def _save_deps_checkpoint(self) -> bool:
        """Save deps-only checkpoint (before any file content).

        This captures HOL state with only dependencies loaded, used for
        clean verification of proofs without accumulated session state.

        Returns True if saved successfully.
        """
        if self._deps_checkpoint_saved:
            return True

        self._checkpoint_dir.mkdir(parents=True, exist_ok=True)
        self._deps_checkpoint_path = self._checkpoint_dir / "deps_only.save"
        ckpt_path_str = escape_sml_string(str(self._deps_checkpoint_path))

        depth = await self._get_hierarchy_depth()
        if depth is None:
            return False
        result = await self.session.send(
            f'PolyML.SaveState.saveChild ("{ckpt_path_str}", {depth});', timeout=60
        )
        if _is_hol_error(result):
            return False

        self._deps_checkpoint_saved = True
        return True

    async def _restore_to_deps(self) -> bool:
        """Restore session to deps-only state (no file content).

        Returns True if restored successfully.
        """
        if not self._deps_checkpoint_path or not self._deps_checkpoint_path.exists():
            return False

        ckpt_path_str = escape_sml_string(str(self._deps_checkpoint_path))
        result = await self.session.send(
            f'PolyML.SaveState.loadState "{ckpt_path_str}";', timeout=30
        )
        if _is_hol_error(result):
            return False

        # Reset loaded state - no file content after restore
        self._loaded_to_line = 0
        self._loaded_content_hash = ""
        return True

    async def _rewind_or_reinit(self, thm: TheoremInfo | None, reason: str) -> str | None:
        """Bring the heap back to a state holding no file content from ``thm``
        onwards (from line 1 when ``thm`` is None), or restart HOL.

        Tries the nearest predecessor context checkpoint, then the deps-only
        one. When neither loads, the heap still holds everything that ran,
        and every per-theorem checkpoint saved in it is part of its
        SaveState parent chain: Poly/ML refuses to save over a parent
        ("File being saved is used as a parent of this file"), so replaying
        in that heap silently loses every checkpoint it tries to re-save.
        HOL restarts instead.

        Returns None on success, or an error string from the restart.
        """
        if thm is not None:
            predecessor = self._find_predecessor_checkpoint(thm)
            if (predecessor is not None
                    and await self._load_context_checkpoint(predecessor.name)):
                return None
        if await self._restore_to_deps():
            return None
        self._schedule_full_reinit(reason)
        self._session_notices.append(
            f"[{reason.capitalize()}; HOL restarts, dependencies reload and "
            f"the prefix replays from line 1]")
        return await self._reinitialize_session_if_needed()

    def _theorem_prefix_hash(self, theorem_name: str) -> str:
        """Hash of the file content a theorem's checkpoint was built from.

        A checkpoint is the theory state after the file up to and including
        this theorem has run, so only that PREFIX determines it — an edit
        after the theorem's QED cannot change the state it captured. Same
        prefix convention as _check_stale_state (lines[:end_line - 1]).
        """
        thm = self._get_theorem(theorem_name)
        if thm is None:
            # Renamed or deleted: no prefix to compare, so nothing validates.
            return self._content_hash
        return self._compute_hash(
            '\n'.join(self._content.split('\n')[:thm.proof_end_line - 1])
        )

    def _is_checkpoint_valid(self, theorem_name: str) -> bool:
        """Check if end_of_proof checkpoint exists and is valid."""
        ckpt = self._checkpoints.get(theorem_name)
        if ckpt is None:
            return False
        if ckpt.end_of_proof_path is None or not ckpt.end_of_proof_path.exists():
            return False
        if (ckpt.content_hash != ""
                and ckpt.content_hash != self._theorem_prefix_hash(theorem_name)):
            return False
        return True

    def _is_context_checkpoint_valid(self, theorem_name: str) -> bool:
        """Check if context checkpoint exists and is valid."""
        ckpt = self._checkpoints.get(theorem_name)
        if ckpt is None:
            return False
        if ckpt.context_path is None or not ckpt.context_path.exists():
            return False
        if (ckpt.content_hash != ""
                and ckpt.content_hash != self._theorem_prefix_hash(theorem_name)):
            return False
        return True

    async def _save_end_of_proof_checkpoint(self, theorem_name: str, tactics_count: int) -> bool:
        """Save checkpoint after all tactics have been replayed.

        Call this when GOALFRAG has all tactics applied. The checkpoint
        captures this state for fast state_at via loadState + backup_n.

        Strategy: Save current state directly - no reload needed.
        The session already has base as parent (from init), context loaded,
        and tactics replayed. Just call saveChild to capture the delta.

        ASSUMPTION: The PolyML state hierarchy (ancestors) must not change between
        checkpoint save and load. If the hierarchy changes (e.g., HOL is restarted
        with different heaps), checkpoints become invalid. This is detected by
        content_hash validation - if the file changes, checkpoints are invalidated.
        If HOL restarts, a new session starts fresh without cached checkpoints.

        Returns True if checkpoint was saved successfully.
        """
        if not self._base_checkpoint_saved:
            return False

        self._checkpoint_dir.mkdir(parents=True, exist_ok=True)
        ckpt_path = self._new_checkpoint_path(theorem_name, "end_of_proof")
        ckpt_path_str = escape_sml_string(str(ckpt_path))

        depth = await self._get_hierarchy_depth()
        if depth is None:
            self._note_checkpoint_save_failure(ckpt_path, self._DEPTH_UNREADABLE)
            return False
        # Save checkpoint directly from current state
        result = await self.session.send(
            f'PolyML.SaveState.saveChild ("{ckpt_path_str}", {depth});', timeout=30
        )
        if _is_hol_error(result):
            self._note_checkpoint_save_failure(ckpt_path, result)
            return False

        # Merge with existing entry (may already have context_path). The hash
        # is refreshed too: the state just saved is the state of the file as it
        # is NOW, whatever the entry was first stamped with.
        if theorem_name in self._checkpoints:
            self._checkpoints[theorem_name].end_of_proof_path = ckpt_path
            self._checkpoints[theorem_name].tactics_count = tactics_count
            self._checkpoints[theorem_name].content_hash = \
                self._theorem_prefix_hash(theorem_name)
        else:
            self._checkpoints[theorem_name] = TheoremCheckpoint(
                theorem_name=theorem_name,
                tactics_count=tactics_count,
                end_of_proof_path=ckpt_path,
                content_hash=self._theorem_prefix_hash(theorem_name),
            )
        return True

    def _note_checkpoint_save_failure(self, ckpt_path: Path, result: str) -> None:
        """Report a checkpoint that failed to save; without it, backward
        navigation to that point falls back to a long replay."""
        error = next((ln.strip() for ln in result.splitlines() if ln.strip()), "")
        notice = (f"[Checkpoint not saved: {ckpt_path.name}: {error[:200]}; "
                  f"backward navigation past it replays instead]")
        if notice not in self._session_notices:
            self._session_notices.append(notice)

    async def _save_context_checkpoint(self, theorem_name: str) -> None:
        """Save context checkpoint: theory state after theorem content is loaded.

        The session has the theorem stored (QED → store_thm) and clean
        top-level proof state. This checkpoint is a valid prefix for
        successor theorems — unlike end_of_proof checkpoints which have
        proof replay state but no theorem binding.

        Called after each theorem loads in _load_context_to_line.
        Unconditional — frequent checkpoints keep saveChild deltas small
        and bound replay distance for backward navigation.
        """
        if not self._base_checkpoint_saved:
            return

        self._checkpoint_dir.mkdir(parents=True, exist_ok=True)
        ckpt_path = self._new_checkpoint_path(theorem_name, "context")
        ckpt_path_str = escape_sml_string(str(ckpt_path))

        depth = await self._get_hierarchy_depth()
        if depth is None:
            self._note_checkpoint_save_failure(ckpt_path, self._DEPTH_UNREADABLE)
            return
        result = await self.session.send(
            f'PolyML.SaveState.saveChild ("{ckpt_path_str}", {depth});', timeout=60
        )
        if _is_hol_error(result):
            self._note_checkpoint_save_failure(ckpt_path, result)
            return

        # Update checkpoint dict (merge with any existing end_of_proof entry).
        # The hash is refreshed too — see _save_end_of_proof_checkpoint.
        if theorem_name in self._checkpoints:
            self._checkpoints[theorem_name].context_path = ckpt_path
            self._checkpoints[theorem_name].content_hash = \
                self._theorem_prefix_hash(theorem_name)
        else:
            self._checkpoints[theorem_name] = TheoremCheckpoint(
                theorem_name=theorem_name,
                tactics_count=0,
                context_path=ckpt_path,
                content_hash=self._theorem_prefix_hash(theorem_name),
            )

    async def _load_checkpoint_and_backup(self, theorem_name: str, target_tactic_idx: int) -> bool:
        """Load checkpoint and backup to target position.

        Strategy: Just load theorem checkpoint - Poly/ML auto-loads parent chain.
        No need to explicitly load base first.

        Args:
            theorem_name: Theorem whose checkpoint to load
            target_tactic_idx: Target tactic index (0 = initial state, N = after N tactics)

        Returns True if successful, False if checkpoint invalid or load failed.
        """
        ckpt = self._checkpoints.get(theorem_name)
        if ckpt is None or not self._is_checkpoint_valid(theorem_name):
            return False

        # Load theorem checkpoint - Poly/ML auto-loads parent chain (base)
        ckpt_path_str = escape_sml_string(str(ckpt.end_of_proof_path))
        result = await self.session.send(
            f'PolyML.SaveState.loadState "{ckpt_path_str}";', timeout=30
        )
        if _is_hol_error(result):
            # loadState failure may leave PolyML in corrupted state.
            # Invalidate this checkpoint and reset tracking so the caller's
            # fallback path (full replay) can restart cleanly.
            self._invalidate_checkpoint(theorem_name)
            self._loaded_to_line = 0
            self._loaded_content_hash = ""
            self._pos = SessionPosition()
            return False
        
        # End-of-proof checkpoint has proof replay state but NO theorem binding
        # (proof was replayed via g/e, not loaded via QED). Set _loaded_to_line
        # to this theorem's proof_end_line — the session has content up to here
        # from the checkpoint's parent chain (base + context), but NOT later theorems.
        thm = self._get_theorem(theorem_name)
        self._loaded_to_line = thm.proof_end_line if thm else 0
        self._loaded_content_hash = ckpt.content_hash

        # Backup to target position (~11ms for any N)
        backups_needed = ckpt.tactics_count - target_tactic_idx
        if backups_needed > 0:
            result = await self.session.send(f'backup_n {backups_needed};', timeout=30)
            if _is_hol_error(result):
                return False

        self._pos = self._pos.at_step(target_tactic_idx, self._content_hash)
        return True

    def _find_predecessor_checkpoint(self, target_thm: TheoremInfo) -> TheoremInfo | None:
        """Find latest predecessor with a valid context checkpoint.

        Walks theorems backward from target, returning the closest one
        whose context checkpoint exists and content_hash matches.
        """
        for thm in reversed(self._theorems):
            if thm.proof_end_line > target_thm.start_line:
                continue  # Not a predecessor
            if self._is_context_checkpoint_valid(thm.name):
                return thm
        return None

    async def _load_context_checkpoint(self, theorem_name: str) -> bool:
        """Load a context checkpoint (theory state after theorem stored).

        Unlike _load_checkpoint_and_backup, this loads a checkpoint that
        has the theorem bound in theory — valid prefix for successors.
        Sets _loaded_to_line to the theorem's proof_end_line.

        Returns True if loaded successfully.
        """
        ckpt = self._checkpoints.get(theorem_name)
        if ckpt is None or ckpt.context_path is None:
            return False
        if not ckpt.context_path.exists():
            # File gone — clean up the stale reference
            ckpt.context_path = None
            if ckpt.end_of_proof_path is None:
                self._checkpoints.pop(theorem_name, None)
            return False

        ckpt_path_str = escape_sml_string(str(ckpt.context_path))
        result = await self.session.send(
            f'PolyML.SaveState.loadState "{ckpt_path_str}";', timeout=30
        )
        if _is_hol_error(result):
            # Remove just the context_path (keep end_of_proof if any)
            if ckpt.context_path and ckpt.context_path.exists():
                ckpt.context_path.unlink()
            ckpt.context_path = None
            self._loaded_to_line = 0
            self._loaded_content_hash = ""
            # If no paths remain, remove dict entry entirely
            if ckpt.end_of_proof_path is None and ckpt.context_path is None:
                self._checkpoints.pop(theorem_name, None)
            return False

        thm = self._get_theorem(theorem_name)
        self._loaded_to_line = thm.proof_end_line if thm else 0
        self._loaded_content_hash = ckpt.content_hash
        return True

    def _invalidate_checkpoint(self, theorem_name: str) -> None:
        """Invalidate and delete checkpoint for a theorem."""
        ckpt = self._checkpoints.pop(theorem_name, None)
        if not ckpt:
            return
        if ckpt.end_of_proof_path and ckpt.end_of_proof_path.exists():
            ckpt.end_of_proof_path.unlink()
        if ckpt.context_path and ckpt.context_path.exists():
            ckpt.context_path.unlink()

    def _invalidate_all_checkpoints(self) -> None:
        """Invalidate all checkpoints (e.g., when file changes significantly)."""
        for name in list(self._checkpoints.keys()):
            self._invalidate_checkpoint(name)

    def _invalidate_from_line(self, start_line: int) -> None:
        """Invalidate checkpoints and traces for theorems at or after start_line.

        When content changes at line N, all theorems starting at N or later,
        OR containing line N, have invalid checkpoints/traces.
        Also invalidates for deleted theorems (not in new parse).

        Resume goals have special handling: they're only invalidated when the
        change affects the main theorem containing the corresponding `suspend`,
        because re-extraction requires the original suspension to still hold
        its label (which may already be consumed after the Resume ran).
        """
        current_thm_names = {thm.name for thm in self._theorems}
        # A top-level span at or after the change is re-sent on the next load.
        self._prefix_errors = [e for e in self._prefix_errors if e[1] < start_line]

        # Build name → theorem lookup for fast suspension-source queries
        name_to_thm = {thm.name: thm for thm in self._theorems}

        # Invalidate checkpoints/traces/tc_goals for theorems that no longer exist
        for name in list(self._checkpoints.keys()):
            if name not in current_thm_names:
                self._invalidate_checkpoint(name)
        for name in list(self._proof_traces.keys()):
            if name not in current_thm_names:
                del self._proof_traces[name]
        for name in list(self._tc_goals.keys()):
            if name not in current_thm_names:
                del self._tc_goals[name]
        for name in list(self._resume_goals.keys()):
            if name not in current_thm_names:
                del self._resume_goals[name]
        # Auto-cheat verdicts for deleted/renamed theorems are stale; drop them
        # so a vanished name can never carry a "failed at load" reason forward.
        for name in list(self._failed_proofs.keys()):
            if name not in current_thm_names:
                del self._failed_proofs[name]
        for name in list(self._theorem_oracles.keys()):
            if name not in current_thm_names:
                del self._theorem_oracles[name]

        # Invalidate checkpoints/traces/tc_goals/resume_goals for theorems at or after change point
        for thm in self._theorems:
            if thm.proof_end_line >= start_line:
                self._invalidate_checkpoint(thm.name)
                if thm.name in self._proof_traces:
                    del self._proof_traces[thm.name]
                if thm.name in self._tc_goals:
                    del self._tc_goals[thm.name]
                # Drop the cached auto-cheat verdict: the theorem (or one before
                # it) changed, so its prior "failed at load / SKIPPED" reason is
                # stale and MUST be re-derived on the next load. Without this a
                # fixed Resume body keeps reporting its first-load failure (and a
                # sub-dispatcher's children keep showing "SKIPPED") until a full
                # session restart — file=changed alone never refreshed it.
                if thm.name in self._failed_proofs:
                    del self._failed_proofs[thm.name]
                # Same for the cached oracle tags: an edit at or before this
                # theorem can discharge the cheat its "⚠ depends on cheat"
                # verdict was derived from.
                if thm.name in self._theorem_oracles:
                    del self._theorem_oracles[thm.name]
                # Resume goals: invalidate only when change affects the
                # extraction context (main theorem or a nested suspending
                # Resume earlier in the chain). Once a Resume's label has
                # been consumed by its own run, re-extraction is impossible
                # without session rollback.
                if thm.kind == "Resume" and thm.name in self._resume_goals:
                    source_thm = name_to_thm.get(thm.suspension_name) if thm.suspension_name else None
                    # The main `suspend "X"` for a Resume block lives either
                    # in the original Theorem or in an earlier Resume of the
                    # same theorem chain. Walk the chain to see if any
                    # ancestor's body was touched.
                    affected = False
                    if source_thm and start_line <= source_thm.proof_end_line:
                        affected = True
                    if not affected:
                        # Check earlier Resume blocks on the same suspension:
                        # their bodies can contain further `suspend` calls
                        # whose labels this Resume depends on.
                        for other in self._theorems:
                            if other is thm:
                                break
                            if (other.kind == "Resume"
                                    and other.suspension_name == thm.suspension_name
                                    and other.start_line < thm.start_line
                                    and start_line <= other.proof_end_line):
                                affected = True
                                break
                    if affected:
                        del self._resume_goals[thm.name]
                elif thm.name in self._resume_goals:
                    # Non-Resume (shouldn't happen, but keep safe): drop
                    del self._resume_goals[thm.name]

    def _chain_members(self, root_name: str) -> list[TheoremInfo]:
        """The root Theorem plus every ``Resume`` block that belongs to it."""
        return [
            t for t in self._theorems
            if t.name == root_name
            or (t.kind == "Resume" and t.suspension_name == root_name)
        ]

    def _affected_chain_roots(self, start_line: int) -> list[TheoremInfo]:
        """Suspend/Resume chains whose already-registered part a change at
        ``start_line`` invalidates: the chain ROOT begins at/before the change
        and at least one member reaches to/past it.

        A chain lying entirely AFTER the change is NOT affected — none of its
        text changed and it has not run, so nothing of its registered state
        is stale. Scoping by straddling (rather than "every theorem after
        the change") is what keeps an unrelated broken chain later in the
        file from being blamed for an edit elsewhere.

        The root of a ``Resume thm[label]`` is the Theorem named ``thm`` (its
        ``suspension_name``); a ``Theorem``/``Triviality`` whose body contains
        ``suspend`` is its own root.
        """
        name_to_thm = {t.name: t for t in self._theorems}
        roots: dict[str, TheoremInfo] = {}
        for thm in self._theorems:
            if thm.proof_end_line < start_line:
                continue
            if thm.kind == "Resume":
                root = name_to_thm.get(thm.suspension_name) if thm.suspension_name else None
            elif (thm.kind in ("Theorem", "Triviality")
                    and re.search(r'\bsuspend\b', thm.proof_body or "")):
                root = thm
            else:
                root = None
            if root is not None and root.start_line <= start_line:
                roots[root.name] = root
        return list(roots.values())

    def _suspension_chain_root_line(self, start_line: int) -> int | None:
        """Earliest start_line of a suspend/Resume chain ROOT affected by a
        change at ``start_line``, or None if no chain is affected."""
        roots = self._affected_chain_roots(start_line)
        return min((r.start_line for r in roots), default=None)

    def _affected_chain_is_broken(self, start_line: int) -> bool:
        """True if a change at ``start_line`` lands in a suspend/Resume chain
        that currently has a failed/auto-cheated/orphaned body recorded in
        ``_failed_proofs``.

        Such a chain replays like any other after an edit (the rewind to a
        context checkpoint restores the suspension stores with the heap);
        what distinguishes it is that the red member re-runs and re-fails on
        every load, which ``_broken_chain_notice`` reports. A broken chain the
        change does not touch is not the edit's concern.
        """
        return any(
            member.name in self._failed_proofs
            for root in self._affected_chain_roots(start_line)
            for member in self._chain_members(root.name)
        )

    _CHAIN_REMEDY = (
        "Keep loaded bodies green: end an unfinished arm in `cheat` or "
        "`>- suspend \"Label\"` and iterate inside its Resume body.")

    @staticmethod
    def _suspended_labels(thm: TheoremInfo) -> list[str]:
        """Labels a body registers when it runs (``suspend "X"`` occurrences)."""
        return re.findall(r'suspend\s*"([^"]+)"', thm.proof_body or "")

    def _broken_chain_notice(self, start_line: int) -> str | None:
        """Account of the broken suspend/Resume chain(s) a change at
        ``start_line`` lands in, or None when every affected chain is healthy.

        A member in ``_failed_proofs`` either failed at load and was
        auto-cheated (so the labels its body suspends were never registered
        and their Resume blocks are orphaned — "No such label"), or is such an
        orphan itself. Each reload past a failed body re-runs it, up to
        PER_THEOREM_TIMEOUT, and auto-cheats it again unless the edit fixed it;
        the notice attributes that recurring cost to the red member.
        """
        if not self._affected_chain_is_broken(start_line):
            return None
        out: list[str] = []
        for root in self._affected_chain_roots(start_line):
            members = self._chain_members(root.name)
            failed = [m for m in members if m.name in self._failed_proofs]
            if not failed:
                continue
            red = [m for m in failed
                   if not self._failed_proofs[m.name].startswith("label not found")]
            labels = {lab for m in red for lab in self._suspended_labels(m)}
            orphans = [m.name for m in members
                       if m not in red
                       and (m.label_name in labels or m.name in self._failed_proofs)]
            if red:
                red_str = "; ".join(
                    f"{m.name} (line {m.start_line}) failed at load — "
                    f"{self._failed_proofs[m.name]}" for m in red)
                orphan_str = (
                    f" Its `suspend` labels were never registered, so "
                    f"{', '.join(orphans)} cannot be resumed (\"No such label\")."
                    if orphans else "")
                out.append(
                    f"[Broken suspend/Resume chain `{root.name}`: {red_str}."
                    f"{orphan_str} The reload after this edit re-runs that body "
                    f"(up to {PER_THEOREM_TIMEOUT:g}s) and auto-cheats it again "
                    f"unless the edit fixed it; only the prefix from the edited "
                    f"block on is replayed. {self._CHAIN_REMEDY}]")
            else:
                out.append(
                    f"[Broken suspend/Resume chain `{root.name}`: "
                    f"{', '.join(orphans)} could not be resumed (label not found "
                    f"at load) although no member failed — no loaded body of "
                    f"this chain suspends that label; check the label name.]")
        return "\n".join(out) if out else None

    def _record_failed_proof(self, thm: TheoremInfo, reason: str) -> None:
        """Record an auto-cheat verdict. For a suspend/Resume chain member —
        a Resume block, or a Theorem that suspends — also queue a notice that
        names the Resume blocks its labels would have served and what the red
        body costs every load from now on."""
        self._failed_proofs[thm.name] = reason
        if thm.kind == "Resume":
            root = thm.suspension_name
        elif thm.kind in ("Theorem", "Triviality") and re.search(
                r'\bsuspend\b', thm.proof_body or ""):
            root = thm.name
        else:
            return
        labels = set(self._suspended_labels(thm))
        orphans = [t.name for t in self._theorems
                   if t.kind == "Resume" and t.suspension_name == root
                   and t.label_name in labels]
        orphan_str = (
            f" Its `suspend` labels were never registered, so "
            f"{', '.join(orphans)} cannot be resumed (\"No such label\")."
            if orphans else "")
        self._session_notices.append(
            f"[Auto-cheated {thm.kind} {thm.name} (line {thm.start_line}) "
            f"after its body failed at load: {reason}.{orphan_str} Every load "
            f"past it re-runs this body (up to {PER_THEOREM_TIMEOUT:g}s) and "
            f"auto-cheats it again until it loads green. {self._CHAIN_REMEDY}]")

    async def init(self) -> dict:
        """Initialize cursor - parse file and load deps.

        Does NOT verify theorems - that happens lazily via state_at/trace_proof.

        Returns:
            dict with:
              - theorems: list of {name, line, has_cheat}
              - cheats: list of cheat locations
              - error: error message if init failed
        """
        self._dep_artifacts = {}
        try:
            self._reparse_if_changed()
        except FileNotFoundError:
            return {
                "theorems": [], "cheats": [],
                "error": f"File not found: {self.file}"
            }

        if not self._theorems:
            return {"error": "No theorems found in file", "theorems": [], "cheats": []}

        if not self.session.is_running:
            await self.session.start()

        # Load dependencies from holdeptool
        # Non-theory build-time modules may already live in the base heap.
        # Required theory interfaces must not be silently skipped.
        try:
            deps = await get_script_dependencies(self.file)
            await self._record_dep_artifacts(deps)
            budget = dep_load_timeout()
            for dep in deps:
                t_dep = time.perf_counter()
                result = await self._send_phase(
                    f'load "{dep}";', budget, "dependency load", dep)
                if _is_hol_error(result):
                    if "Cannot find file" in result and not dep.endswith("Theory"):
                        continue
                    self._needs_session_reinit = True
                    return {
                        "theorems": [],
                        "cheats": [],
                        "error": self._dep_load_error(
                            dep, result, time.perf_counter() - t_dep, budget),
                    }
        except (FileNotFoundError, RuntimeError):
            pass  # holdeptool not available or failed (parse error), skip dep loading

        thm_list = [
            {"name": t.name, "line": t.start_line, "has_cheat": t.has_cheat}
            for t in self._theorems
        ]
        cheats = [
            {
                "theorem": t.name,
                "line": t.proof_start_line,
                "col": 1,
            }
            for t in self._theorems if t.has_cheat
        ]

        # Save deps-only checkpoint for clean verification
        await self._save_deps_checkpoint()

        # Save base checkpoint now (same state as deps-only) so that context
        # checkpoints can be saved as children of base from the very first
        # _load_context_to_line call. Without this, _base_checkpoint_saved is False
        # during the first load and no context checkpoints are created.
        await self._save_base_checkpoint()

        # File content loading is LAZY — handled by enter_theorem →
        # _load_context_to_line when a specific theorem is requested.
        # This avoids loading all theorems upfront (expensive for large files).

        return {
            "theorems": thm_list,
            "cheats": cheats,
        }

    async def _extract_tc_goal(self, thm: TheoremInfo) -> None:
        """Extract termination conditions goal for a Definition block.

        Calls extract_tc_goal_json_q which temporarily creates the defn via
        Hol_defn inside try_grammar_extension + try_theory_extension,
        extracts the TC goal string (every variable and numeral typed, so the
        later reparse cannot pick another overload), then rolls back all
        changes. The body goes over as the quotation HOL's own filter would
        compile, so its `^x` antiquotes resolve to the session's SML values.

        MUST be called BEFORE the Definition block is processed (before
        the function constant exists in the theory).

        Results are cached in self._tc_goals[thm.name].
        """
        goal_body = thm.goal.replace('\n', ' ').strip()
        tc_result = await self.session.send(
            f'extract_tc_goal_json_q {definition_quotation(goal_body)};', timeout=30
        )
        tc_data = _try_find_json_line(tc_result)
        if 'ok' in tc_data and tc_data['ok']:
            self._tc_goals[thm.name] = tc_data['ok']

    async def _extract_resume_goal(self, thm: TheoremInfo) -> str | None:
        """Extract goal for a Resume block from the suspension DB.

        Must be called AFTER the original Theorem with suspend has been loaded,
        but BEFORE the Resume block itself is loaded.

        Results are cached in self._resume_goals[thm.name].
        Returns the extraction error (e.g. label not found), or None on success.
        """
        if not thm.suspension_name or thm.label_name is None:
            return None
        escaped_susp = escape_sml_string(thm.suspension_name)
        escaped_label = escape_sml_string(thm.label_name)
        result = await self.session.send(
            f'extract_resume_goal_json "{escaped_susp}" "{escaped_label}";',
            timeout=30
        )
        data = _try_find_json_line(result)
        if 'ok' in data:
            self._resume_goals[thm.name] = data['ok']
            return None
        return data.get('err', f'unexpected output: {result[:200]}')

    async def _cheat_failed_theorem(
        self, thm: TheoremInfo, reason: str = "proof failed"
    ) -> str | None:
        """After a proof failure, re-send the theorem with cheat to bind its name.

        Without this, later theorems that reference the failed one get a fatal
        Poly/ML compile error ("Value or constructor not declared").

        ``reason`` is recorded in _failed_proofs so outputs can name WHY the
        dependency was auto-cheated.

        Returns error string if the cheat itself fails, else None.
        """
        if thm.kind == "Resume":
            attrs_parts = [thm.label_name] if thm.label_name else []
            attrs_parts.extend(thm.attributes)
            attrs_str = ','.join(attrs_parts)
            cheat_block = f'Resume {thm.suspension_name}[{attrs_str}]:\n  cheat\nQED'
            result = await self.session.send(cheat_block, timeout=30)
            if _is_hol_error(result):
                return (
                    f"Resume '{thm.name}' failed (line {thm.start_line}) "
                    f"and could not be cheated: {result}"
                )
            self._record_failed_proof(thm, reason)
            return None

        attrs = f"[{','.join(thm.attributes)}]" if thm.attributes else ""
        cheat_block = f'Theorem {thm.name}{attrs}:\n{thm.goal}\nProof\n  cheat\nQED'
        # Drain extra residual output from the failed proof before cheating
        await asyncio.sleep(0.1)
        await self.session.drain_stale()
        result = await self.session.send(cheat_block, timeout=30)
        # Check for success: val <name> = ... : thm in output
        # (residual output from the original failed proof can pollute the result,
        # so checking for errors is unreliable — check for success instead)
        if f"val {thm.name}" in result:
            self._record_failed_proof(thm, reason)
            return None
        if _is_hol_error(result):
            return (
                f"Proof of '{thm.name}' failed (line {thm.start_line}) "
                f"and could not be cheated: {result[-500:]}"
            )
        self._record_failed_proof(thm, reason)
        return None

    async def _cheat_skip_theorem(self, thm: TheoremInfo) -> bool:
        """Bind a prefix theorem via `cheat` WITHOUT replaying its proof.

        Used by prefix-skip navigation mode (state_at skip_prefix=True): rather
        than replaying a (possibly very slow or non-terminating) prefix proof,
        re-assert its STATEMENT with a cheat so its name is bound for later
        theorems. The target theorem is still replayed for real, so its live
        goal is exactly what holmake would see — only the prefix is trusted by
        statement.

        Returns True if the theorem was cheated; False if it isn't a cheatable
        shape (Definition / Resume / suspend-dispatcher / no goal / already a
        cheat) or the bare statement failed to re-parse — in which case the
        caller must fall back to a normal replay.
        """
        if thm.kind not in ("Theorem", "Triviality"):
            return False
        # A suspend-dispatcher's separate Resume blocks would be orphaned if we
        # cheated the dispatcher; an already-cheated body replays instantly
        # anyway; an empty goal can't be re-asserted.
        if (not thm.goal.strip() or thm.has_cheat
                or re.search(r'\bsuspend\b', thm.proof_body)):
            return False

        attrs = f"[{','.join(thm.attributes)}]" if thm.attributes else ""
        cheat_block = f'Theorem {thm.name}{attrs}:\n{thm.goal}\nProof\n  cheat\nQED'
        result = await self.session.send(cheat_block, timeout=30)
        if f"val {thm.name}" in result:
            self._skipped_thms.add(thm.name)
            return True
        # Bare statement didn't re-parse standalone — drain any residual and let
        # the caller replay the real proof so navigation stays correct.
        await self.session.drain_stale()
        return False

    def _local_block_at(self, line: int) -> LocalBlock | None:
        """Return the local block containing the given line, or None."""
        for lb in self._local_blocks:
            if lb.local_line <= line <= lb.end_line:
                return lb
        return None

    def _local_block_overlapping(self, start_line: int, end_line: int) -> LocalBlock | None:
        """Return the first local block that overlaps [start_line, end_line].

        Used to check if pre-content (the gap between current position and
        next theorem) includes the start of a local block.
        """
        for lb in self._local_blocks:
            if lb.local_line <= end_line and lb.end_line >= start_line:
                return lb
        return None

    def _line_to_idx(self, line: int) -> int:
        """Convert 1-indexed line to 0-indexed array index, clamped to valid range."""
        if line <= 0:
            return 0
        return line - 1

    async def _send_phase(self, content: str, timeout: float, phase: str,
                          item: str = "", start_line: int = 0,
                          end_line: int = 0) -> str:
        self._phase = {"phase": phase, "item": item, "file": str(self.file),
                       "start_line": start_line, "end_line": end_line,
                       "started": time.perf_counter(), "budget": timeout,
                       "active": True}
        previous_context = getattr(self.session, "request_context", {})
        self.session.request_context = self._phase
        try:
            return await self.session.send(content, timeout=timeout)
        except asyncio.CancelledError:
            self._phase["interrupted"] = True
            raise
        finally:
            self._phase["active"] = False
            self.session.request_context = previous_context

    async def _send_and_check(self, content: str, timeout: float,
                              start_line: int = 0, end_line: int = 0) -> str | None:
        """Send content to HOL, return error string on fatal error, else None."""
        if not content.strip():
            return None
        result = await self._send_phase(content, timeout, "top-level SML/translation",
                                        start_line=start_line, end_line=end_line)
        if _is_fatal_hol_error(result):
            return f"Error executing file content: {_format_context_error(result)}"
        if any(line.startswith("Exception-") for line in result.split('\n')):
            # An uncaught exception in one top-level item (classically a
            # Definition whose automatic termination proof failed) ends the
            # chunk: that item and everything after it in this span did not
            # run, although loading continues with the next span.
            span = (start_line, end_line)
            self._prefix_errors = [e for e in self._prefix_errors if e[:2] != span]
            self._prefix_errors.append((start_line, end_line, _error_reason(result)))
        return None

    async def _handle_theorem_error(self, thm: TheoremInfo, result: str) -> str | None:
        """Handle HOL error from a theorem send. Returns error string or None."""
        if thm.kind == "Definition":
            return f"Definition '{thm.name}' failed (line {thm.start_line}): {result}"
        return await self._cheat_failed_theorem(thm, _error_reason(result))

    async def _extract_goals_for(self, theorems: list[TheoremInfo]) -> None:
        """Extract Definition/Resume goals before theorems are processed."""
        for thm in theorems:
            if thm.kind == "Definition" and thm.proof_body and thm.name not in self._tc_goals:
                await self._extract_tc_goal(thm)
            if thm.kind == "Resume" and thm.name not in self._resume_goals:
                err = await self._extract_resume_goal(thm)
                if err is not None:
                    # HOL processes a Resume whose label is missing as a
                    # SILENT no-op (no output, nothing runs). Record it so
                    # outputs can name the skipped block instead of letting
                    # it masquerade as loaded.
                    self._failed_proofs.setdefault(
                        thm.name,
                        f"label not found at load — Resume block "
                        f"SKIPPED, never ran ({_error_reason(err)})"
                    )

    async def _load_context_to_line(self, target_line: int,
                                    timeout: float = PREFIX_LOAD_TIMEOUT) -> str | None:
        """Load file content up to target_line into HOL session.
        
        Loads content granularly - theorem by theorem - so that a broken proof
        in one theorem doesn't prevent loading of subsequent content.

        When theorems fall inside SML `local ... in ... end` blocks, the entire
        block is sent as one chunk because Poly/ML requires the complete local
        declaration as a syntactic unit.
        
        Args:
            target_line: 1-indexed line to load up to (exclusive)
            timeout: Timeout for HOL send (default PREFIX_LOAD_TIMEOUT)
            
        Returns:
            Error message if failed, None if success.
        """
        if target_line <= self._loaded_to_line:
            return None
            
        content_lines = self._content.split('\n')
        theorems_in_range = [
            t for t in self._theorems
            if self._loaded_to_line < t.proof_end_line <= target_line
        ]
        
        if not theorems_in_range:
            # No theorems in range — but check if the content spans a local block.
            # If pre-content includes 'local ... in' without the matching 'end',
            # we must extend the load to include 'end'.
            actual_target = target_line
            start_line = self._loaded_to_line + 1
            lb = self._local_block_overlapping(start_line, target_line - 1)
            if lb:
                actual_target = max(target_line, lb.end_line + 1)
            start_idx = self._line_to_idx(self._loaded_to_line)
            to_load = '\n'.join(content_lines[start_idx:actual_target - 1])
            err = await self._send_and_check(to_load, timeout,
                                              max(1, self._loaded_to_line), actual_target - 1)
            if err:
                return err
            self._loaded_to_line = actual_target
            loaded_content = '\n'.join(content_lines[:actual_target - 1])
            self._loaded_content_hash = self._compute_hash(loaded_content)
            return None
        else:
            current_line = self._loaded_to_line
            i = 0
            
            while i < len(theorems_in_range):
                thm = theorems_in_range[i]
                # Check if either the theorem or the pre-content gap before it
                # overlaps a local block. If pre-content contains 'local ... in',
                # it must be sent together with theorems + 'end'.
                local_block = self._local_block_at(thm.start_line)
                if local_block is None and current_line < thm.start_line:
                    local_block = self._local_block_overlapping(current_line, thm.start_line - 1)

                if local_block is None:
                    # Normal theorem (no local block overlap)
                    if thm.start_line > current_line:
                        pre = '\n'.join(content_lines[self._line_to_idx(current_line):self._line_to_idx(thm.start_line)])
                        err = await self._send_and_check(pre, timeout,
                                                          max(1, current_line), thm.start_line - 1)
                        if err:
                            return err

                    await self._extract_goals_for([thm])

                    cheated = False
                    if self._skip_prefix:
                        cheated = await self._cheat_skip_theorem(thm)
                    if not cheated:
                        thm_content = '\n'.join(content_lines[self._line_to_idx(thm.start_line):self._line_to_idx(thm.proof_end_line)])
                        if thm_content.strip():
                            # One PREFIX theorem gets the per-theorem budget, not
                            # the caller's whole-navigation timeout: a single slow
                            # proof must be cheated and named, not abort the
                            # navigation and leave the target unreachable.
                            thm_timeout = min(timeout, PER_THEOREM_TIMEOUT) if timeout else PER_THEOREM_TIMEOUT
                            result = await self._send_phase(
                                thm_content, thm_timeout, "preceding theorem",
                                thm.name, thm.start_line, thm.proof_end_line - 1)
                            if result.startswith("TIMEOUT"):
                                err = await self._cheat_failed_theorem(
                                    thm, f"timeout >{thm_timeout:g}s loading whole proof"
                                )
                                if err:
                                    return err
                            elif _is_fatal_hol_error(result):
                                return f"Error executing file content: {_format_context_error(result)}"
                            elif _is_hol_error(result):
                                err = await self._handle_theorem_error(thm, result)
                                if err:
                                    return err

                    current_line = thm.proof_end_line
                    await self._save_context_checkpoint(thm.name)
                    i += 1
                else:
                    # Local block: collect theorems, send as one chunk from
                    # current_line through the block's 'end'
                    lb = local_block
                    block_thms = []
                    while i < len(theorems_in_range) and lb.local_line <= theorems_in_range[i].start_line <= lb.end_line:
                        block_thms.append(theorems_in_range[i])
                        i += 1

                    await self._extract_goals_for(block_thms)

                    # Must include 'end' even if target_line falls inside the
                    # local block — Poly/ML requires the complete local...end
                    block_end = lb.end_line + 1
                    if block_end > current_line:
                        block_content = '\n'.join(content_lines[self._line_to_idx(current_line):self._line_to_idx(block_end)])
                        if block_content.strip():
                            result = await self._send_phase(
                                block_content, timeout, "local SML block",
                                start_line=max(1, current_line), end_line=block_end - 1)
                            if _is_fatal_hol_error(result):
                                return f"Error executing file content: {_format_context_error(result)}"
                            if _is_hol_error(result):
                                for bt in block_thms:
                                    err = await self._handle_theorem_error(bt, result)
                                    if err:
                                        return err
                        current_line = block_end
                        # Save context checkpoint for last theorem in local block
                        if block_thms:
                            await self._save_context_checkpoint(block_thms[-1].name)

            # Remaining content after last theorem — check for local block
            # overlap (pre-content may include 'local ... in' without 'end')
            if current_line < target_line:
                actual_target = target_line
                lb = self._local_block_overlapping(current_line, target_line - 1)
                if lb:
                    actual_target = max(target_line, lb.end_line + 1)
                remaining = '\n'.join(content_lines[self._line_to_idx(current_line):self._line_to_idx(actual_target)])
                err = await self._send_and_check(remaining, timeout,
                                                  max(1, current_line), actual_target - 1)
                if err:
                    return err
                current_line = actual_target
        
        # Update tracking — current_line may be past target_line if we loaded
        # an entire local block
        self._loaded_to_line = max(target_line, current_line)
        loaded_content = '\n'.join(content_lines[:self._loaded_to_line - 1])
        self._loaded_content_hash = self._compute_hash(loaded_content)
        return None

    async def enter_theorem(self, name: str) -> dict:
        """Enter a theorem for proof state inspection.

        Loads context up to theorem start, parses tactics, sets up for state_at.

        Args:
            name: Theorem name to enter

        Returns:
            dict with:
              - theorem: theorem name
              - goal: theorem goal
              - tactics: number of tactics in proof
              - has_cheat: whether proof has cheat
              - error: error message if failed
        """
        try:
            self._reparse_if_changed()
        except FileNotFoundError:
            return {"error": f"File not found: {self.file}"}

        reinit_error = await self._reinitialize_session_if_needed()
        if reinit_error:
            return {"error": reinit_error}

        thm = self._get_theorem(name)
        if not thm:
            return {"error": f"Theorem '{name}' not found"}

        if self._context_rewind_pending:
            error = await self._rewind_or_reinit(
                thm, "session reinit: no context or deps checkpoint "
                     "could be restored to rewind past the edit")
            if error:
                return {"error": error}
            self._context_rewind_pending = False
            self._pos = SessionPosition()

        # Load context up to theorem start
        error = await self._load_context_to_line(thm.start_line)
        if error:
            return {"error": error}

        # Lazily extract TC goal / Resume goal for this theorem
        # (must happen BEFORE the theorem block is processed)
        if thm.kind == "Definition" and thm.proof_body and thm.name not in self._tc_goals:
            await self._extract_tc_goal(thm)
        if thm.kind == "Resume" and thm.name not in self._resume_goals:
            await self._extract_resume_goal(thm)

        # Base checkpoint should have been saved in init(). If somehow it
        # wasn't, save it now (without drop_all — we just loaded context).
        if not self._base_checkpoint_saved:
            await self._save_base_checkpoint()

        # Parse step plan from proof body using TacticParse.
        # Pass the body so byte→char offset conversion happens at the
        # parse boundary — SML emits byte positions, Python uses chars.
        if thm.proof_body:
            escaped_body = escape_sml_string(thm.proof_body)
            step_result = await self.session.send(
                f'goalfrag_step_plan_json "{escaped_body}";', timeout=30
            )
            try:
                self._step_plan = parse_step_plan_output(step_result, thm.proof_body)
            except HOLParseError as e:
                return {"error": f"Failed to parse step plan: {e}"}
        else:
            self._step_plan = []
        self._step_plan_hash = self._content_hash

        self._active_theorem = name
        self._pos = SessionPosition()  # Reset position for new theorem

        # For Resume blocks, show the extracted goal if available
        goal_display = thm.goal
        if thm.kind == "Resume" and thm.name in self._resume_goals:
            rg = self._resume_goals[thm.name]
            goal_display = rg.get('goal', '')
            asms = rg.get('asms', [])
            if asms:
                goal_display = ", ".join(asms) + " ⊢ " + goal_display

        return {
            "theorem": name,
            "goal": goal_display,
            "tactics": len(self._step_plan),
            "has_cheat": thm.has_cheat,
        }

    async def _setup_proof_goal(self, thm_name: str) -> str | None:
        """Drop all goals and set up the proof goal for a theorem.

        Handles Theorem, Definition (TC goal), and Resume (goal + assumptions).
        Re-extracts Resume/TC goals if not cached (e.g. after invalidation).
        Returns error string on failure, None on success.
        """
        thm = self._get_theorem(thm_name)
        if not thm:
            return f"Theorem '{thm_name}' not found"

        await self.session.send('drop_all();', timeout=5)

        # Re-extract Resume/Definition goals if invalidated
        if thm.kind == "Resume" and thm.name not in self._resume_goals:
            await self._extract_resume_goal(thm)
        elif thm.kind == "Definition" and thm.proof_body and thm.name not in self._tc_goals:
            await self._extract_tc_goal(thm)

        if thm.kind == "Resume":
            if not thm.suspension_name or thm.label_name is None:
                return f"Resume '{thm.name}' has no suspension info"
            # Set the goal directly from the suspension store via an SML helper.
            # Avoids a term->string->term round-trip (term_to_string +
            # Parse.Term) which can rename bound variables under a clashing
            # parse context. Mirrors markerLib.set_suspended_goal so the goal
            # presented here is identical to what Holmake runs the Resume
            # body against.
            susp = escape_sml_string(thm.suspension_name)
            label = escape_sml_string(thm.label_name)
            gt_result = await self.session.send(
                f'set_resume_goalfrag_json "{susp}" "{label}";',
                timeout=30,
            )
            # Surface helper-level errors (e.g. missing suspension) clearly.
            data = _try_find_json_line(gt_result)
            if 'err' in data:
                self._pos = SessionPosition()
                return f"Failed to set up Resume goal: {data['err']}"
        elif thm.kind == "Definition" and thm.name in self._tc_goals:
            tc_goal = self._tc_goals[thm.name]
            gt_result = await self.session.send(f'gf `{tc_goal}`;', timeout=30)
        else:
            goal = thm.goal.replace('\n', ' ').strip()
            gt_result = await self.session.send(f'gf `{goal}`;', timeout=30)

        if _is_hol_error(gt_result):
            self._pos = SessionPosition()
            return f"Failed to set up goal: {gt_result}"
        self._pos = self._pos.at_step(0, self._content_hash)
        return None



    # =========================================================================
    # Proof Navigation Helpers
    # =========================================================================

    def _batch_timeout_for(self, n_cmds: int) -> int:
        """Compute batch send timeout for n step commands."""
        step_timeout = self._tactic_timeout or 30
        return max(30, int(step_timeout * max(1, n_cmds)))

    def _common_prefix_length(self, old_plan: list[StepPlan]) -> int:
        """Find length of common command prefix between old and current step plans.

        Returns the index of the first divergent step, or min(len(old), len(new))
        if all shared steps match.
        """
        limit = min(len(old_plan), len(self._step_plan))
        for i in range(limit):
            if old_plan[i].cmd != self._step_plan[i].cmd:
                return i
        return limit

    async def _send_step_batch(self, cmds: list[str]) -> bool:
        """Send a batch of step commands. Returns True on success."""
        text = "".join(cmds)
        if not text.strip():
            return True
        result = await self.session.send(text, timeout=self._batch_timeout_for(len(cmds)))
        return not _is_hol_error(result)

    async def _navigate_steps(self, from_idx: int, to_idx: int) -> bool:
        """Navigate proof position from from_idx to to_idx using step_plan.

        Uses backup_n (backward) or step batch (forward). Commands come from
        self._step_plan, which is sound when from_idx..to_idx is within the
        common prefix of old and new plans (commands are identical).

        Returns True if navigation succeeded.
        """
        if from_idx == to_idx:
            return True
        if from_idx > to_idx:
            result = await self.session.send(
                f'backup_n {from_idx - to_idx};', timeout=30
            )
            return not _is_hol_error(result)
        # Forward: execute delta commands
        cmds = [step.cmd for step in self._step_plan[from_idx:to_idx]]
        return await self._send_step_batch(cmds)

    async def _try_reuse_state(
        self, tactic_idx: int
    ) -> bool:
        """Try to reuse current session state for target position.

        Handles:
        - Exact match: same step boundary → no replay
        - Forward: advance through delta steps → partial replay

        Returns True if session is now at target position.
        """
        if self._session_dirty:
            # A hol_send may have mutated the live proofManager; the reuse path
            # would return the wrong (polluted) goal. Force re-setup instead.
            return False
        if not self._pos.can_reuse(self._content_hash):
            return False

        if self._pos.tactic_idx == tactic_idx:
            return True  # Exact match
        if self._pos.tactic_idx < tactic_idx:
            return await self._navigate_steps(self._pos.tactic_idx, tactic_idx)
        return False  # Can't go backward without proof manager

    async def _try_incremental_navigate(
        self, first_diff: int, old_tactic_idx: int, tactic_idx: int
    ) -> bool:
        """Navigate from old position to target after file change.

        Strategy: commands 0..first_diff-1 are identical between old and new plans,
        so the corresponding proof states are interchangeable. Navigate to a safe
        pivot point within the common prefix, then play forward with new commands.

        Pivot point: min(first_diff, tactic_idx) if target is in common prefix,
        otherwise first_diff (must cross the divergence boundary there).

        Returns True if navigation succeeded.
        """
        if self._session_dirty:
            # Same veto as _try_reuse_state: this path navigates FROM the live
            # position, which a hol_send may have moved. When the target is in
            # the common prefix it can issue zero commands and hand back the
            # probe's goal stack. Force checkpoint/replay instead.
            return False
        if tactic_idx <= first_diff:
            # Target in common prefix: navigate directly (all commands identical)
            return await self._navigate_steps(old_tactic_idx, tactic_idx)

        # Target is past the divergence point: navigate to first_diff first,
        # then play forward with new commands.
        if not await self._navigate_steps(old_tactic_idx, first_diff):
            return False
        # Commands from first_diff onward come from the new step_plan
        new_cmds = [step.cmd for step in self._step_plan[first_diff:tactic_idx]]
        if not new_cmds:
            return True
        return await self._send_step_batch(new_cmds)

    async def _replay_steps_with_fallback(
        self, thm_name: str, cmds: list[str], batch_timeout: int
    ) -> tuple[int, str | None]:
        """Replay commands; on batch failure, replay one-by-one to recover progress.

        Returns (count_replayed, error_or_none).
        """
        if not cmds:
            return 0, None
        batch_cmds = "".join(cmds)
        if not batch_cmds.strip():
            return 0, None

        result = await self.session.send(batch_cmds, timeout=batch_timeout)
        if not _is_hol_error(result):
            return len(cmds), None
        if _is_interrupt_reply(result):
            # Someone stopped this replay on purpose; replaying it step by
            # step would run the very tactic they stopped.
            self.mark_interrupted()
            return 0, ("Tactic replay interrupted (SIGINT); it was not re-run. "
                       "Navigate again to replay from a clean position.")

        # Batch failed: recover last good state by replaying step-by-step.
        setup_err = await self._setup_proof_goal(thm_name)
        if setup_err:
            return 0, setup_err

        replayed = 0
        step_timeout = self._tactic_timeout or 30
        # Per-step cost of THIS replay: (step index, seconds, outcome). The
        # step boundaries exist here anyway; keeping their elapsed times is
        # what lets a report separate a blow-up (finished, slowly) from a
        # candidate loop (only ever hits the budget, never returns).
        self._step_costs = []
        for idx, cmd in enumerate(cmds):
            t_step = time.perf_counter()
            step_result = await self.session.send(cmd, timeout=step_timeout)
            elapsed = time.perf_counter() - t_step
            if _is_hol_error(step_result):
                if step_result.startswith("TIMEOUT"):
                    self._step_costs.append((idx, elapsed, "budget"))
                    return replayed, (
                        f"Tactic replay timed out: step {idx} "
                        f"({_step_label(cmd)}) did not finish within the "
                        f"per-step budget of {step_timeout}s — a candidate "
                        f"LOOP, since a looping tactic never returns."
                        + self._step_cost_report()
                    )
                self._step_costs.append((idx, elapsed, "failed"))
                return replayed, (
                    f"Tactic replay failed at step {idx} "
                    f"({_step_label(cmd)}): {step_result}"
                    + self._step_cost_report()
                )
            self._step_costs.append((idx, elapsed, "ok"))
            replayed += 1

        # Shouldn't happen: fallback fully succeeded but batch didn't?
        return replayed, f"Tactic replay failed: {result}"

    def _step_cost_report(self, top: int = 3) -> str:
        """The costliest COMPLETED steps of the last replay.

        A step that finished carries a real elapsed time (superlinear but
        terminating work — a blow-up); a step that only ever hits its budget
        has none to report. Printing the completed ones is what tells a
        reader which of the two happened.
        """
        done = [(i, secs) for i, secs, outcome in self._step_costs
                if outcome == "ok"]
        if not done:
            return ""
        done.sort(key=lambda p: -p[1])
        shown = ", ".join(
            f"step {i} {secs * 1000:.0f}ms" for i, secs in done[:top]
        )
        return f"\nCompleted steps by cost: {shown}."

    async def _replay_to_boundary(
        self, thm: TheoremInfo, tactic_idx: int, total_tactics: int
    ) -> tuple[bool, int, str | None, bool]:
        """Replay to a step boundary using checkpoint or full replay.

        Try O(1) checkpoint path first, then fall back to full replay with
        step-by-step fallback on batch failure.

        Returns (success, reached_idx, error_msg, used_checkpoint).
        """
        # Try checkpoint path
        if self._is_checkpoint_valid(thm.name) and thm.proof_body:
            if await self._load_checkpoint_and_backup(thm.name, tactic_idx):
                return True, tactic_idx, None, True
            # A failed load leaves the heap unchanged, possibly holding
            # content past this theorem: rewind before replaying it.
            error = await self._rewind_or_reinit(
                thm, "session reinit: a proof checkpoint failed to load and "
                     "no context or deps checkpoint could be restored")
            if error:
                return False, 0, error, False
            enter_result = await self.enter_theorem(thm.name)
            if "error" in enter_result:
                return False, 0, enter_result["error"], False

        # Full replay from scratch
        setup_err = await self._setup_proof_goal(thm.name)
        if setup_err:
            return False, 0, setup_err, False

        if not thm.proof_body or total_tactics == 0:
            return True, 0, None, False

        # Replay full proof or prefix depending on target position
        if tactic_idx == total_tactics:
            cmds = [step.cmd for step in self._step_plan]
        else:
            cmds = [step.cmd for step in self._step_plan[:tactic_idx]]

        batch_timeout = (self._batch_timeout_for(total_tactics)
                         if tactic_idx == total_tactics
                         else self._batch_timeout_for(tactic_idx))
        replayed, replay_error = await self._replay_steps_with_fallback(
            thm.name, cmds, batch_timeout
        )

        # Save checkpoint at proof end on success
        if replay_error is None and tactic_idx == total_tactics:
            await self._save_end_of_proof_checkpoint(thm.name, total_tactics)

        success = replay_error is None
        return success, replayed, replay_error, False

    def _detect_inside_by(self, tactic_idx: int) -> bool:
        """Detect if position is inside a decomposed by/>- subproof.

        Walks backward through step plan tracking open/close nesting.
        An unmatched open means we're inside a subproof.
        """
        if not self._step_plan or tactic_idx <= 0:
            return False
        depth = 0
        for i in range(tactic_idx - 1, -1, -1):
            step = self._step_plan[i]
            if step.kind == "close":
                depth += 1
            elif step.kind == "open":
                if depth > 0:
                    depth -= 1
                else:
                    return True
        return False

    async def _prepare_session(
        self, line: int, col: int, timings: dict[str, float]
    ) -> bool | StateAtResult:
        """Reparse file, reinit session if needed, enter theorem at position.

        Returns True if session is ready (may have changed), False if unchanged,
        or StateAtResult on unrecoverable error.
        """
        t0 = time.perf_counter()
        try:
            changed = self._reparse_if_changed()
        except FileNotFoundError:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash="", error=f"File not found: {self.file}"
            )
        timings['reparse'] = time.perf_counter() - t0

        reinit_error = await self._reinitialize_session_if_needed()
        if reinit_error:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash, error=reinit_error
            )

        thm_at_pos = self._get_theorem_at_position(line)
        if not thm_at_pos:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash,
                error=(f"Position ({line}, {col}) is not within any theorem."
                       f"{self._nearest_theorem_ranges(line)}")
            )

        t1 = time.perf_counter()
        # Backward navigation: the loaded prefix runs PAST this theorem's own
        # block, so later theorems — and their [simp] attributes — are in scope
        # and can close a goal the file's own order leaves open. Drop back to
        # the nearest predecessor checkpoint, as execute_proof_traced does.
        if (self._deps_checkpoint_saved
                and self._loaded_to_line > thm_at_pos.proof_end_line):
            error = await self._rewind_or_reinit(
                thm_at_pos, "session reinit: no context or deps checkpoint "
                            "could be restored for backward navigation")
            if error:
                return StateAtResult(
                    goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                    file_hash=self._content_hash, error=error
                )

        # Re-enter when the target changed, and ALSO when the loaded prefix no
        # longer reaches this theorem's start: an edit BEFORE the theorem
        # truncates _loaded_to_line, and everything between there and the
        # theorem (including derived `Theorem foo = <expr>` blocks, which are
        # not parsed as theorems) must be re-executed before its tactics replay.
        # Skipping that replays the proof against stale bindings, so a fix to
        # something earlier in the file silently has no effect.
        if (self._active_theorem != thm_at_pos.name
                or self._loaded_to_line < thm_at_pos.start_line):
            enter_result = await self.enter_theorem(thm_at_pos.name)
            if "error" in enter_result:
                return StateAtResult(
                    goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                    file_hash=self._content_hash, error=enter_result["error"]
                )
        timings['enter_theorem'] = time.perf_counter() - t1

        return changed

    def _active_theorem_info(self) -> TheoremInfo | StateAtResult:
        """Get active theorem info, or error result if none active."""
        thm = self._get_theorem(self._active_theorem)
        if thm:
            return thm
        return StateAtResult(
            goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
            file_hash=self._content_hash,
            error=f"Theorem '{self._active_theorem}' no longer exists"
        )

    async def _compute_target(
        self, thm: TheoremInfo, line: int, col: int, changed: bool
    ) -> _TargetInfo | StateAtResult:
        """Compute target position: reparse step plan, find tactic index, detect partial.

        On file change, invalidates checkpoints, reparses step plan, and computes
        incremental diff for optimization. Returns _TargetInfo or error StateAtResult.
        """
        # Reparse step plan if content changed since state_at last ran (changed=True)
        # OR if the step plan is stale relative to current content (drift — can happen
        # when a non-state_at caller like cursor.status ran _reparse_if_changed and
        # advanced _content_hash without updating _step_plan).
        needs_reparse = changed or self._step_plan_hash != self._content_hash
        incremental_update = None
        if needs_reparse:
            incremental_update = await self._reparse_steps_on_edit(thm)
            if isinstance(incremental_update, StateAtResult):
                return incremental_update

        # Bounds check
        proof_keyword_line = thm.proof_start_line - 1
        qed_line = thm.proof_end_line - 1
        if line < proof_keyword_line or line > qed_line:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash,
                error=f"Position ({line}, {col}) not in theorem '{self._active_theorem}' "
                      f"(valid lines {proof_keyword_line}-{qed_line})"
            )

        # Convert (line, col) → proof body offset → tactic index
        proof_body_offset = self._line_col_to_proof_offset(thm, line, col)
        tactic_idx = self._offset_to_tactic_idx(proof_body_offset)
        total_tactics = len(self._step_plan)

        return _TargetInfo(
            thm=thm, tactic_idx=tactic_idx, total_tactics=total_tactics,
            incremental_update=incremental_update, changed=changed,
            proof_offset=proof_body_offset,
        )

    def _line_col_to_proof_offset(self, thm: TheoremInfo, line: int, col: int) -> int:
        """Convert (line, col) to offset within the proof body."""
        qed_line = thm.proof_end_line - 1
        if line == qed_line:
            return len(thm.proof_body) if thm.proof_body else 0
        file_offset = line_col_to_offset(line, col, self._line_starts)
        return max(0, file_offset - thm.proof_body_offset)

    def _offset_to_tactic_idx(self, proof_body_offset: int) -> int:
        """Find step boundary index at or before the given proof body offset."""
        tactic_idx = 0
        for i, step in enumerate(self._step_plan):
            if proof_body_offset >= step.end:
                tactic_idx = i + 1
            else:
                break
        return tactic_idx



    async def _reparse_steps_on_edit(
        self, thm: TheoremInfo
    ) -> tuple[int, int] | None | StateAtResult:
        """On file change: invalidate checkpoint, reparse step plan, compute diff.

        Returns (first_diff, old_tactic_idx) for incremental update,
        None if incremental not viable, or StateAtResult on parse error.
        """
        old_plan = list(self._step_plan)
        old_tactic_idx = self._pos.tactic_idx
        self._invalidate_checkpoint(self._active_theorem)

        if thm.proof_body:
            escaped_body = escape_sml_string(thm.proof_body)
            step_result = await self.session.send(
                f'goalfrag_step_plan_json "{escaped_body}";', timeout=30
            )
            try:
                self._step_plan = parse_step_plan_output(step_result, thm.proof_body)
            except HOLParseError as e:
                return StateAtResult(
                    goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                    file_hash=self._content_hash,
                    error=f"Failed to parse step plan: {e}"
                )
        else:
            self._step_plan = []
        self._step_plan_hash = self._content_hash

        # Commands that match produce identical proof state.
        # Keep the common prefix, redo from first divergence.
        if (old_plan and self._step_plan
                and self._pos.initialized and old_tactic_idx > 0):
            first_diff = self._common_prefix_length(old_plan)
            if first_diff > 0:
                return (first_diff, old_tactic_idx)
        return None

    async def _navigate_to_target(self, target: _TargetInfo) -> _NavResult:
        """Dispatch navigation strategy to reach target position.

        Priority chain: reuse → incremental → checkpoint → full replay.
        Partial positions (inside a step) always land at the nearest step boundary,
        same as incremental update behavior.
        """
        # Strategy 1: Reuse current session state (file unchanged)
        if not target.changed and await self._try_reuse_state(
            target.tactic_idx
        ):
            return _NavResult(reached_idx=target.tactic_idx, error_msg=None, strategy="reused")

        # Strategy 2: Incremental update (file changed, common prefix available)
        if target.incremental_update is not None and await self._try_incremental_navigate(
            target.incremental_update[0], target.incremental_update[1], target.tactic_idx
        ):
            return _NavResult(reached_idx=target.tactic_idx, error_msg=None, strategy="incremental")

        # Strategy 3: Checkpoint or full replay (step boundary)
        return await self._navigate_step_boundary(target)



    async def _navigate_step_boundary(self, target: _TargetInfo) -> _NavResult:
        """Navigate to a step boundary via checkpoint or full replay."""
        success, replayed, replay_error, used_checkpoint = (
            await self._replay_to_boundary(
                target.thm, target.tactic_idx, target.total_tactics
            )
        )
        strategy = "checkpoint" if used_checkpoint else "replay"
        return _NavResult(reached_idx=replayed, error_msg=replay_error, strategy=strategy)

    def _update_position(self, target: _TargetInfo, nav: _NavResult) -> None:
        """Update session position tracking after successful navigation."""
        if nav.error_msg is not None:
            return
        self._pos = self._pos.at_step(target.tactic_idx, self._content_hash)
        # The session is now re-synced with the cache at this position; any
        # prior hol_send pollution has been discarded by the checkpoint/replay.
        self._session_dirty = False

    # Operators that make a parenthesised group's flat replay depend on how
    # many goals the group receives.
    _POSITIONAL_RE = re.compile(r">-|>\||>~|>>~|\bTHEN1\b|\bTHENL\b")

    def _file_line(self, file_offset: int) -> int:
        return self._content.count("\n", 0, file_offset) + 1

    @classmethod
    def _group_entry_checks(cls, text: str, sub: list[StepPlan]) -> set[int]:
        """Sub-step indices at which the goal count must be 1 before
        continuing: the first sub-step of each positional group that is
        applied by a THEN combinator (or starts the step) rather than being
        the arm of a THEN1-like selector, which already hands it one goal."""
        checks: set[int] = set()
        for j in range(len(sub)):
            start = step_text_start(sub, j, text)
            i = start - 1
            while i >= 0 and text[i].isspace():
                i -= 1
            if i < 0 or text[i] != "(":
                continue
            depth, close = 1, i + 1
            while close < len(text) and depth:
                depth += {"(": 1, ")": -1}.get(text[close], 0)
                close += 1
            if not cls._POSITIONAL_RE.search(text[i + 1:close]):
                continue
            before = text[:i].rstrip()
            if before.endswith((">-", "THEN1")):
                continue
            checks.add(j)
        return checks

    @staticmethod
    def _is_then_group(body: str, text_start: int) -> bool:
        """True when the step text at `text_start` sits in parentheses that a
        THEN combinator (or the proof start) applies, rather than the arm of
        a THEN1-like selector."""
        i = text_start - 1
        while i >= 0 and body[i].isspace():
            i -= 1
        if i < 0 or body[i] != "(":
            return False
        return not body[:i].rstrip().endswith((">-", "THEN1"))

    async def _navigate_inside_group(self, target: _TargetInfo, nav: _NavResult) -> dict | None:
        """Replay the flat sub-plan of the opaque step the target sits inside,
        when that is sound: every positional group the replay enters under a
        THEN combinator receives exactly one goal (checked live). On success
        the live state is the state AT the position; it is never cached — the
        session is marked dirty so the next navigation re-establishes it.
        Returns the inside_group record, or None to keep the entry state."""
        k = self._detect_inside_step(target)
        if k is None or nav.error_msg is not None:
            return None
        step = self._step_plan[k]
        if step.kind != "expand":
            return None
        thm = target.thm
        body = thm.proof_body or ""
        text = step.text
        text_start = step_text_start(self._step_plan, k, body)
        out = await self.session.send(
            f'goalfrag_step_plan_json_flat "{escape_sml_string(text)}";', timeout=30)
        try:
            sub = parse_step_plan_output(out, text)
        except HOLParseError:
            return None
        if len(sub) <= 1:
            return None
        rel = target.proof_offset - text_start
        sub_idx = 0
        for j, s in enumerate(sub):
            if rel >= s.end:
                sub_idx = j + 1
            else:
                break
        base = thm.proof_body_offset + text_start
        info = {
            "step": k, "sub_idx": sub_idx, "sub_total": len(sub),
            "start_line": self._file_line(base),
            "end_line": self._file_line(thm.proof_body_offset + step.end),
            "error": None, "fail_line": None,
        }
        if sub_idx == 0:
            return info
        checks = self._group_entry_checks(text, sub)
        # The planner reports a parenthesised group by its INNER span, so the
        # step's own parentheses are in the body, not in `text`: a group that
        # a THEN combinator applies per goal must itself receive one goal.
        if self._is_then_group(body, text_start):
            checks.add(0)
        step_timeout = self._tactic_timeout or 30
        for j in range(sub_idx):
            if j in checks:
                try:
                    n = len(self._parse_goals_json(
                        await self.session.send('goals_json();', timeout=10)))
                except HOLParseError:
                    n = -1
                if n != 1:
                    # Not the single-goal case: put the entry state back.
                    await self._replay_to_boundary(thm, k, target.total_tactics)
                    return None
            result = await self.session.send(sub[j].cmd, timeout=step_timeout)
            if _is_hol_error(result):
                line = self._file_line(base + step_text_start(sub, j, text))
                info["sub_idx"] = j
                info["fail_line"] = line
                info["error"] = (
                    f"PROOF BROKEN inside opaque step {k} at sub-step {j} "
                    f"(line {line}, {_step_label(sub[j].cmd)}): "
                    f"{result.strip().splitlines()[0] if result.strip() else 'tactic failed'}")
                break
        self._session_dirty = True
        return info

    async def _build_result(
        self, target: _TargetInfo, nav: _NavResult, timings: dict[str, float],
        t0: float, t3: float, inside: dict | None = None,
    ) -> StateAtResult:
        """Fetch goals and assemble final result."""
        timings['replay'] = time.perf_counter() - t3
        timings['strategy'] = nav.strategy

        t4 = time.perf_counter()
        error_msg = nav.error_msg
        if inside and inside.get("error"):
            error_msg = inside["error"]
        goals_output = await self.session.send('goals_json();', timeout=10)
        try:
            goals = self._parse_goals_json(goals_output)
        except HOLParseError as e:
            goals = []
            error_msg = str(e) if not error_msg else f"{error_msg}; {e}"
        timings['goals'] = time.perf_counter() - t4
        timings['total'] = time.perf_counter() - t0

        return StateAtResult(
            goals=goals,
            tactic_idx=target.tactic_idx,
            tactics_replayed=nav.reached_idx,
            tactics_total=target.total_tactics,
            file_hash=self._content_hash,
            error=error_msg,
            timings=timings,
            inside_by=self._detect_inside_by(target.tactic_idx),
            inside_step_idx=None if inside else self._detect_inside_step(target),
            inside_group=inside,
        )

    def _detect_inside_step(self, target: _TargetInfo) -> int | None:
        """Step index when the target offset is strictly INSIDE a step.

        The replay can only land on step boundaries, so a position inside a
        lumped/parenthesized chain shows the chain's ENTRY state. "Inside"
        means strictly past the step's own tactic text start (a target on
        the combinator/whitespace prefix is the same replay position as the
        text start, which is what the user expects). Returns the 0-based
        step index, or None when the target sits on a boundary.
        """
        idx = target.tactic_idx
        if idx >= len(self._step_plan):
            return None
        step = self._step_plan[idx]
        if step.kind not in ("expand", "expand_list"):
            return None
        text_start = step_text_start(
            self._step_plan, idx, target.thm.proof_body or ""
        )
        if text_start < target.proof_offset < step.end:
            return idx
        return None

    async def state_at(self, line: int, col: int = 1,
                       skip_prefix: bool = False) -> StateAtResult:
        """Navigate, and attach the HOL diagnostics the navigation produced.

        HOL emits its most valuable warnings (same-name/different-type
        variables, invented type variables) on the SUCCESS path, where every
        structured channel regenerates its content from terms and the raw
        output is discarded. Harvesting them around the whole navigation is
        the only place they can be caught for a caller that never sees a
        failure.
        """
        sink = getattr(self.session, "diagnostics", None)
        mark = len(sink) if isinstance(sink, list) else None
        result = await self._state_at_traced(line, col, skip_prefix)
        if mark is not None and result.warnings is None:
            fresh: list[str] = []
            for cmd, text in sink[mark:]:
                # `<<HOL message: …>>` is chatty — a cold prefix load emits one
                # per parsed quotation — so keep only those from the caller's
                # own tactics. A `WARNING:` is rare and kept wherever it came
                # from.
                if not text.startswith("WARNING:") and not _REPLAY_CMD_RE.match(cmd):
                    continue
                if text not in fresh:
                    fresh.append(text)
            if fresh:
                result.warnings = fresh[:20]
        return result

    async def _state_at_traced(self, line: int, col: int = 1,
                               skip_prefix: bool = False) -> StateAtResult:
        """Get proof state at file position using prefix-based replay.

        Auto-enters the theorem containing the position if not already active.

        skip_prefix: when True, theorems BEFORE the target are bound via `cheat`
        (statement only) instead of being replayed — instant navigation into a
        target even in a cold, unbuilt theory whose earlier proofs are slow or
        non-terminating. The target theorem itself is still replayed for real.
        Toggling the mode forces a clean reload of the prefix.
        """
        if skip_prefix != self._skip_prefix:
            self._skip_prefix = skip_prefix
            self._skipped_thms = set()
            # A prefix already loaded under the other mode is invalid now —
            # rebuild from deps so the new mode governs every prefix theorem,
            # and drop per-theorem caches keyed to the old prefix (stale
            # checkpoints would otherwise be reused post-reinit and desync).
            if self._loaded_to_line > 0:
                self._needs_session_reinit = True
                self._invalidate_all_checkpoints()
                self._failed_proofs = {}
                self._proof_traces = {}
                self._theorem_oracles = {}

        timings: dict[str, float] = {}
        # Startup accrued before this navigation (a cold init) belongs to the
        # call the user is waiting on: start the clock that much earlier.
        pre_startup = self._startup_seconds
        self._startup_seconds = 0.0
        pre_cause, self._startup_cause = self._startup_cause, None
        self._target_replay_started = None
        t0 = time.perf_counter() - pre_startup

        # Snapshot cache state BEFORE any work — for diagnostics
        timings['pos_before_idx'] = self._pos.tactic_idx
        timings['pos_before_offset'] = -1
        timings['pos_before_init'] = 1 if self._pos.initialized else 0
        timings['pos_hash_match'] = (
            1 if self._pos.content_hash == self._content_hash else 0
        )

        changed = await self._prepare_session(line, col, timings)
        timings['startup'] = pre_startup + self._startup_seconds
        self._startup_seconds = 0.0
        cause, self._startup_cause = self._startup_cause or pre_cause, None
        if cause:
            timings['startup_cause'] = cause
        if isinstance(changed, StateAtResult):
            return changed
        timings['file_changed'] = 1 if changed else 0

        thm = self._active_theorem_info()
        if isinstance(thm, StateAtResult):
            return thm

        target = await self._compute_target(thm, line, col, changed)
        if isinstance(target, StateAtResult):
            return target

        timings['target_idx'] = target.tactic_idx
        timings['target_partial'] = -1
        if target.incremental_update is not None:
            timings['incr_first_diff'] = target.incremental_update[0]
            timings['incr_old_idx'] = target.incremental_update[1]

        t3 = time.perf_counter()
        self._target_replay_started = t3
        nav = await self._navigate_to_target(target)
        self._update_position(target, nav)
        self._note_break_streak(thm.name, nav, changed)
        inside = await self._navigate_inside_group(target, nav)
        return await self._build_result(target, nav, timings, t0, t3, inside)

    LOOP_STREAK = 4

    def _note_break_streak(self, theorem: str, nav: "_NavResult", changed: bool) -> None:
        """Count edit→navigate cycles that break at the same step; from the
        LOOP_STREAK-th on, queue a notice naming the sub-suspend recipe."""
        if nav.error_msg is None:
            self._break_streak = None
            return
        key = (theorem, nav.reached_idx)
        if self._break_streak and self._break_streak[:2] == key:
            if not changed:
                return
            count = self._break_streak[2] + 1
        else:
            count = 1
        self._break_streak = (theorem, nav.reached_idx, count)
        if count >= self.LOOP_STREAK:
            self._session_notices.append(
                f"[Loop: {count} edit→navigate cycles on {theorem} broke at the "
                f"same step {nav.reached_idx}. Stop editing blind: sub-suspend "
                f"the arm — replace it with `>- suspend \"X\"`, add "
                f"`Resume {suspension_base(theorem)}[X]: cheat QED` after the "
                f"parent QED, then "
                f"hol_state_at inside the Resume body to read the real goal]")

    def mark_interrupted(self) -> None:
        """Resync cursor state after the HOL process was SIGINT'd mid-replay.

        An overall-budget timeout aborts a tactic partway, leaving the live
        proofManager goal stack at an unknown point. Discard the cached
        position and flag the session dirty so the next state_at rebuilds the
        goal from scratch instead of trusting a stale checkpoint."""
        self._pos = SessionPosition()
        self._session_dirty = True

    def _parse_goals_json(self, output: str) -> list[dict]:
        """Parse JSON goal output from goals_json().

        Output format: {"ok":[{"asms":[...], "goal":"..."}, ...]} or {"err":"message"}
        Returns: List of goal dicts with 'asms' (list of assumption strings) and 'goal' (conclusion string)
        Raises: HOLParseError if HOL4 returned an error or output is malformed.
        """
        result = _find_json_line(output, "goals_json")

        # goals_json reports what the goal text cannot show (same-name variables
        # of different types); route it to the session's diagnostic sink so
        # state_at attaches it like any other HOL diagnostic.
        sink = getattr(getattr(self, "session", None), "diagnostics", None)
        if isinstance(sink, list):
            for w in result.get('warnings') or []:
                sink.append(("goals_json();", str(w)))

        if 'ok' in result:
            goals = []
            for g in result['ok']:
                if isinstance(g, dict) and 'asms' in g and 'goal' in g:
                    goals.append(g)
                else:
                    # Old format (just goal string) for backwards compat
                    goals.append({"asms": [], "goal": str(g)})
            return goals
        elif 'err' in result:
            raise HOLParseError(f"goals_json: {result['err']}")
        else:
            raise HOLParseError(f"Unexpected JSON structure: {result}")

    @property
    def status(self) -> dict:
        """Get cursor status."""
        try:
            self._reparse_if_changed()
        except FileNotFoundError:
            return {"error": f"File not found: {self.file}"}
        stale = self._check_stale_state()

        return {
            "file": str(self.file),
            "file_hash": self._content_hash,
            "active_theorem": self._active_theorem,
            "active_tactics": len(self._step_plan),
            "loaded_to_line": self._loaded_to_line,
            "stale": stale,
            # An armed reinit makes the next navigation a COLD replay from
            # dependencies. Without saying so, this status is indistinguishable
            # from a cursor that simply has not loaded anything yet.
            **({"pending_work":
                "session restart armed: the next navigation replays the whole "
                "prefix from dependencies (all checkpoints were discarded)"}
               if self._needs_session_reinit else {}),
            "completed": [],
            "theorems": [
                {"name": t.name, "line": t.start_line, "has_cheat": t.has_cheat,
                 **({"proof_failed": True} if t.name in self._failed_proofs else {})}
                for t in self._theorems
            ],
            "cheats": [
                {"theorem": t.name, "line": t.proof_start_line, "col": 1}
                for t in self._theorems if t.has_cheat
            ],
        }

    # =========================================================================
    # Proof Timing
    # =========================================================================

    async def execute_proof_traced(self, theorem_name: str) -> list[TraceEntry]:
        """Execute a proof and return timing trace for each tactic.

        Runs in clean state (deps-only checkpoint) to match holmake behavior.
        Results are cached; cache is invalidated on file changes.

        Args:
            theorem_name: Name of theorem to trace

        Returns:
            List of TraceEntry objects for each tactic
        """
        try:
            self._reparse_if_changed()
        except FileNotFoundError:
            return []

        reinit_error = await self._reinitialize_session_if_needed()
        if reinit_error:
            return []

        if theorem_name in self._proof_traces:
            return self._proof_traces[theorem_name]

        thm = self._get_theorem(theorem_name)
        if not thm:
            return []

        # Navigation to correct theory prefix for holmake-matching verification.
        # Three cases:
        # 1. Cold cursor (_loaded_to_line == 0): restore to deps-only, enter_theorem
        #    does full incremental load.
        # 2. Forward/prefix already loaded (_loaded_to_line <= thm.start_line):
        #    enter_theorem handles incremental delta or is a no-op. No restore needed.
        # 3. Backward (_loaded_to_line > thm.start_line): loaded prefix extends past
        #    target, so later theorems may be in scope. Try loading the nearest
        #    predecessor context checkpoint, which has the correct theory prefix
        #    without later theorems. Fallback to deps-only restore if none exists.
        if self._deps_checkpoint_saved:
            if self._loaded_to_line == 0:
                if await self._rewind_or_reinit(
                        None, "session reinit: the deps checkpoint could not "
                              "be restored for a clean trace"):
                    return []
            elif self._loaded_to_line > thm.start_line:
                if await self._rewind_or_reinit(
                        thm, "session reinit: no context or deps checkpoint "
                             "could be restored for a clean trace"):
                    return []

        # Load context up to theorem
        enter_result = await self.enter_theorem(theorem_name)
        if "error" in enter_result:
            return []

        # Get tactics from step plan
        tactics = [step.cmd for step in self._step_plan if step.cmd.strip()]
        if not tactics:
            return []

        # For Definitions, use the TC goal (which doesn't reference the
        # function constant, so it works even before the Definition is processed).
        # For Resume blocks, extract goal from suspension DB if not already cached
        # (suspension exists because enter_theorem loaded context to theorem start).
        is_resume = thm.kind == "Resume"
        if is_resume:
            if thm.name not in self._resume_goals:
                await self._extract_resume_goal(thm)
            if thm.name not in self._resume_goals:
                return []  # Can't extract goal from suspension
            goal = ""  # unused for Resume; verify_resume_json re-extracts live term
        elif thm.kind == "Definition" and thm.name in self._tc_goals:
            goal = self._tc_goals[thm.name]
        else:
            goal = thm.goal.replace('\n', ' ').strip()
        tactics_sml = "[" + ",".join(
            f'"{escape_sml_string(t)}"' for t in tactics
        ) + "]"
        tactic_timeout = self._tactic_timeout or 60.0
        # Python timeout = per-tactic timeout * num tactics + buffer
        python_timeout = tactic_timeout * len(tactics) + 10
        if is_resume:
            # Resume: let SML re-extract the live goal term from the suspension DB
            # to avoid a lossy term_to_string/Parse.Term round-trip.
            result = await self.session.send(
                f'verify_resume_json "{escape_sml_string(thm.suspension_name or "")}" "{escape_sml_string(thm.label_name or "")}" "{theorem_name}" {tactics_sml} false {tactic_timeout:.1f};',
                timeout=max(30, python_timeout)
            )
        else:
            result = await self.session.send(
                f'verify_theorem_json "{escape_sml_string(goal)}" "{theorem_name}" {tactics_sml} false {tactic_timeout:.1f};',
                timeout=max(30, python_timeout)
            )

        # Parse response into TraceEntry list
        parsed = _try_find_json_line(result)
        trace = []
        steps = [step for step in self._step_plan if step.cmd.strip()]
        if 'ok' in parsed:
            for i, entry in enumerate(parsed['ok'].get('trace', [])):
                cmd = tactics[i] if i < len(tactics) else ""
                start_offset = steps[i - 1].end if i > 0 and i - 1 < len(steps) else 0
                end_offset = steps[i].end if i < len(steps) else None
                goals_before = entry.get('goals_before')
                goals_after = entry.get('goals_after')
                trace.append(TraceEntry(
                    cmd=cmd,
                    real_ms=entry.get('real_ms', 0),
                    usr_ms=0, sys_ms=0,
                    goals_before=goals_before,
                    goals_after=goals_after,
                    error=entry.get('err'),
                    start_offset=start_offset,
                    end_offset=end_offset,
                ))
        elif 'err' in parsed:
            trace.append(TraceEntry(
                cmd="", real_ms=0, usr_ms=0, sys_ms=0,
                goals_before=None, goals_after=None, error=parsed['err']
            ))

        # Track oracle tags (detects cheat cascades via HOL4's tag propagation)
        # An empty list is a clean verdict and must overwrite a stale one.
        if 'ok' in parsed:
            self._theorem_oracles[theorem_name] = parsed['ok'].get('oracles', [])

        self._proof_traces[theorem_name] = trace
        return trace

    async def verify_all_proofs(self) -> dict[str, list[TraceEntry]]:
        """Verify all proofs in clean state, processing in file order.

        Executes each proof exactly once: times tactics, then stores theorem
        so subsequent proofs can use it.

        TODO: Handle local blocks (batch with block) like _load_context_to_line.

        Returns:
            Dict mapping theorem name to trace (empty list for cheats/no tactics)
        """
        try:
            self._reparse_if_changed()
        except FileNotFoundError:
            return {}

        reinit_error = await self._reinitialize_session_if_needed()
        if reinit_error:
            return {}

        results: dict[str, list[TraceEntry]] = {}

        # Restore to clean deps-only state
        if self._deps_checkpoint_saved:
            if await self._rewind_or_reinit(
                    None, "session reinit: the deps checkpoint could not be "
                          "restored for whole-file verification"):
                return {}
        else:
            # No checkpoint - must reload deps manually for clean state
            # This is slower but ensures correctness
            if self.session.is_running:
                await self.session.stop()
            await self.session.start()
            try:
                deps = await get_script_dependencies(self.file)
                budget = dep_load_timeout()
                for dep in deps:
                    result = await self.session.send(f'load "{dep}";', timeout=budget)
                    if _is_hol_error(result) and "Cannot find file" not in result:
                        break  # Stop on real errors
            except (FileNotFoundError, RuntimeError):
                pass  # holdeptool not available or failed (parse error)

        content_lines = self._content.split('\n')
        current_line = 0

        for thm in self._theorems:
            # Load content between previous theorem and this one (definitions, etc.)
            if thm.start_line > current_line + 1:
                pre_content = '\n'.join(content_lines[current_line:thm.start_line - 1])
                if pre_content.strip():
                    await self.session.send(pre_content, timeout=60)

            if thm.has_cheat:
                # Load cheat theorem as-is (stores it with cheat)
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    await self.session.send(thm_content, timeout=60)
                results[thm.name] = []
                current_line = thm.proof_end_line - 1  # 0-indexed: next line to load
                continue

            # Parse step plan
            if thm.proof_body:
                escaped_body = escape_sml_string(thm.proof_body)
                step_result = await self.session.send(
                    f'goalfrag_step_plan_json "{escaped_body}";', timeout=30
                )
                try:
                    step_plan = parse_step_plan_output(step_result, thm.proof_body)
                except HOLParseError:
                    step_plan = []
            else:
                step_plan = []

            if not step_plan:
                # No tactics - load theorem as-is
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    result = await self.session.send(thm_content, timeout=PER_THEOREM_TIMEOUT)
                    # If proof failed, cheat to bind name for later theorems
                    if _is_hol_error(result):
                        if thm.kind == "Definition":
                            # Definition failures can't be cheated; record error
                            results[thm.name] = [TraceEntry(
                                cmd="", real_ms=0, usr_ms=0, sys_ms=0,
                                goals_before=None, goals_after=None,
                                error=f"Definition failed: {result}"
                            )]
                            current_line = thm.proof_end_line - 1
                            continue
                        cheat_err = await self._cheat_failed_theorem(
                            thm, _error_reason(result)
                        )
                        if cheat_err:
                            return {}
                results[thm.name] = []
                current_line = thm.proof_end_line - 1  # 0-indexed: next line to load
                continue

            # For Definitions: extract TC goal, verify with store=false for
            # timing, then load the full block to establish the definition.
            # For Resume: verify_resume_json re-extracts the live goal term
            # from the suspension DB (avoids lossy print/reparse round-trip).
            is_resume = thm.kind == "Resume"
            if is_resume:
                if thm.name not in self._resume_goals:
                    await self._extract_resume_goal(thm)
                if thm.name in self._resume_goals:
                    goal = ""  # unused; SML re-extracts
                else:
                    # Resume goal extraction failed — load as-is
                    thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                    if thm_content.strip():
                        resume_result = await self.session.send(thm_content, timeout=PER_THEOREM_TIMEOUT)
                        if _is_hol_error(resume_result):
                            cheat_err = await self._cheat_failed_theorem(
                                thm, _error_reason(resume_result)
                            )
                            if cheat_err:
                                return {}
                    results[thm.name] = []
                    current_line = thm.proof_end_line - 1
                    continue
            elif thm.kind == "Definition":
                if thm.name not in self._tc_goals:
                    await self._extract_tc_goal(thm)
                tc_goal = self._tc_goals.get(thm.name)
                if tc_goal:
                    goal = tc_goal
                else:
                    # TC extraction failed — load as-is without timing
                    thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                    if thm_content.strip():
                        def_result = await self.session.send(thm_content, timeout=PER_THEOREM_TIMEOUT)
                        if _is_hol_error(def_result):
                            results[thm.name] = [TraceEntry(
                                cmd="", real_ms=0, usr_ms=0, sys_ms=0,
                                goals_before=None, goals_after=None,
                                error=f"Definition failed: {def_result}"
                            )]
                        else:
                            results[thm.name] = []
                    else:
                        results[thm.name] = []
                    current_line = thm.proof_end_line - 1
                    continue
            else:
                goal = thm.goal.replace('\n', ' ').strip()
            tactics = [step.cmd for step in step_plan if step.cmd.strip()]

            # Build SML list literal: ["tac1", "tac2", ...]
            tactics_sml = "[" + ",".join(
                f'"{escape_sml_string(t)}"' for t in tactics
            ) + "]"

            # Single call: sets goal, runs tactics with timing, stores if OK
            # For Definitions/Resume, store=false (can't save TC/Resume proof as definition)
            store = "false" if thm.kind in ("Definition", "Resume") else "true"
            tactic_timeout = self._tactic_timeout or 60.0
            python_timeout = tactic_timeout * len(tactics) + 10
            if is_resume:
                # File replay MUST use the canonical markerLib.resume path so
                # any sub-suspends issued inside the Resume body are recorded
                # as resumption deltas — otherwise downstream Resume blocks
                # looking up those sub-labels fail with "No such label".
                # Trade-off: per-tactic timing is collapsed into a single
                # trace entry; for per-tactic timing on a single Resume body,
                # use execute_proof_traced (hol_check_proof) which still uses
                # verify_resume_json.
                #
                # markerLib.resume takes a single tactic, so we pass the raw
                # proof_body (NOT the ef()-wrapped step plan, which produces
                # `unit` values rather than tactics).
                resume_body_sml = f'"{escape_sml_string(thm.proof_body)}"'
                result = await self.session.send(
                    f'run_resume_canonical_json "{escape_sml_string(thm.suspension_name or "")}" "{escape_sml_string(thm.label_name or "")}" "{thm.name}" [{resume_body_sml}] {store} {tactic_timeout:.1f};',
                    timeout=max(30, python_timeout)
                )
            else:
                result = await self.session.send(
                    f'verify_theorem_json "{escape_sml_string(goal)}" "{thm.name}" {tactics_sml} {store} {tactic_timeout:.1f};',
                    timeout=max(30, python_timeout)
                )

            # Parse response and convert to TraceEntry list
            parsed = _try_find_json_line(result)
            trace = []
            steps = [step for step in step_plan if step.cmd.strip()]
            if 'ok' in parsed:
                for i, entry in enumerate(parsed['ok'].get('trace', [])):
                    cmd = tactics[i] if i < len(tactics) else ""
                    start_offset = steps[i - 1].end if i > 0 and i - 1 < len(steps) else 0
                    end_offset = steps[i].end if i < len(steps) else None
                    goals_before = entry.get('goals_before')
                    goals_after = entry.get('goals_after')
                    trace.append(TraceEntry(
                        cmd=cmd,
                        real_ms=entry.get('real_ms', 0),
                        usr_ms=0, sys_ms=0,
                        goals_before=goals_before,
                        goals_after=goals_after,
                        error=entry.get('err'),
                        start_offset=start_offset,
                        end_offset=end_offset,
                    ))
            elif 'err' in parsed:
                # Goal setup failed - record single error entry
                trace.append(TraceEntry(
                    cmd="", real_ms=0, usr_ms=0, sys_ms=0,
                    goals_before=None, goals_after=None, error=parsed['err']
                ))

            # Did verify_theorem_json store the theorem?
            # stored=true only when proof_ok AND store=true.
            stored = (
                'ok' in parsed
                and parsed['ok'].get('stored', False)
            )

            # Track oracle tags (detects cheat cascades via HOL4's tag propagation)
            # An empty list is a clean verdict and must overwrite a stale one.
            if 'ok' in parsed:
                self._theorem_oracles[thm.name] = parsed['ok'].get('oracles', [])

            # For Definitions/Resume: always re-send the full block.
            # Definitions: create the constant and store def/ind theorems.
            # Resume: finalise the suspended subgoal.
            # For Theorems: re-send if attributes need registration.
            if thm.kind == "Resume":
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    resume_result = await self.session.send(thm_content, timeout=60)
                    if _is_hol_error(resume_result):
                        cheat_err = await self._cheat_failed_theorem(
                            thm, _error_reason(resume_result)
                        )
                        if cheat_err:
                            return {}
            elif thm.kind == "Definition":
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    def_result = await self.session.send(thm_content, timeout=60)
                    if _is_hol_error(def_result):
                        # Definition block failed — record error in trace
                        trace.append(TraceEntry(
                            cmd="", real_ms=0, usr_ms=0, sys_ms=0,
                            goals_before=None, goals_after=None,
                            error=f"Definition failed: {def_result}"
                        ))
            elif stored and thm.attributes:
                # Re-send to register attributes (e.g. [simp])
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    await self.session.send(thm_content, timeout=60)
            elif not stored:
                # Proof failed/incomplete and name is unbound.
                # Cheat to bind the name so later theorems can reference it.
                cheat_err = await self._cheat_failed_theorem(
                    thm, _trace_reason(trace)
                )
                if cheat_err:
                    return {}

            results[thm.name] = trace
            current_line = thm.proof_end_line - 1  # 0-indexed: next line to load

        # Update loaded state tracking so subsequent state_at doesn't
        # re-send all content (which would cause duplicate definition errors)
        last_thm = self._theorems[-1] if self._theorems else None
        if last_thm:
            self._loaded_to_line = last_thm.proof_end_line
            self._loaded_content_hash = self._content_hash

        return results

    async def diagnose_resume_failure(self, name: str) -> str | None:
        """Diagnose a Resume whose suspension label could not be found.

        The usual cause: the dispatcher theorem or an earlier Resume of the
        same suspension failed during loading (and was auto-cheated), so the
        suspension delta carrying this label was never recorded.

        Reports the ancestor chain (dispatcher + intervening Resumes of the
        same suspension, in file order), marks members already known broken
        (from _failed_proofs, with reasons), and — when none is known broken —
        replays each ancestor in file order until the first failure.

        Returns a multi-line diagnosis string, or None if not applicable.
        """
        thm = self._get_theorem(name)
        if not thm or thm.kind != "Resume" or not thm.suspension_name:
            return None
        susp = thm.suspension_name
        ancestors = [
            t for t in self._theorems
            if t.start_line < thm.start_line
            and (t.name == susp
                 or (t.kind == "Resume" and t.suspension_name == susp))
        ]
        if not ancestors:
            return (
                f"No dispatcher theorem or earlier Resume for suspension "
                f"'{susp}' appears in this file before line {thm.start_line} "
                f"— the suspension was never created here."
            )

        out = [f"Ancestor chain for suspension '{susp}' (file order):"]
        first_broken: TheoremInfo | None = None
        for t in ancestors:
            if t.name in self._failed_proofs:
                out.append(
                    f"  ✗ {t.kind} {t.name} (line {t.start_line}) — "
                    f"failed at load: {self._failed_proofs[t.name]}"
                )
                if first_broken is None:
                    first_broken = t
            else:
                out.append(f"  • {t.kind} {t.name} (line {t.start_line})")

        if first_broken is not None:
            out.append(
                f"first broken ancestor: {first_broken.kind} "
                f"{first_broken.name} (line {first_broken.start_line}) — the "
                f"suspend/Resume that records this label never ran. Fix it "
                f"and retry."
            )
            return "\n".join(out)

        # No ancestor known broken — replay each in file order to find the
        # first failure (bounded to this suspension's chain).
        for t in ancestors:
            trace = await self.execute_proof_traced(t.name)
            if not trace and t.kind == "Resume":
                out.append(
                    f"first broken ancestor: Resume {t.name} (line "
                    f"{t.start_line}) — its own suspension goal could not be "
                    f"extracted (label missing for it too); the break is at "
                    f"or before it."
                )
                return "\n".join(out)
            err = next(
                ((i, e) for i, e in enumerate(trace) if e.error), None
            )
            if err is not None:
                i, e = err
                out.append(
                    f"first broken ancestor: {t.kind} {t.name} (line "
                    f"{t.start_line}) — step {i + 1}: {e.error[:200]}"
                )
                return "\n".join(out)
            if trace and trace[-1].goals_after not in (0, None):
                out.append(
                    f"first broken ancestor: {t.kind} {t.name} (line "
                    f"{t.start_line}) — proof incomplete "
                    f"({trace[-1].goals_after} goals remaining)"
                )
                return "\n".join(out)
        out.append(
            "All ancestors replay OK individually — the label may be "
            "misspelled, or it is consumed/renamed by an intervening Resume."
        )
        return "\n".join(out)
