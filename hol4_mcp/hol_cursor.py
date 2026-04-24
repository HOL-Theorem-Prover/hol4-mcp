"""Proof cursor for navigating through theorems without reloading."""

import asyncio
import hashlib
import re
import time
from dataclasses import dataclass, field
from pathlib import Path

from .hol_file_parser import (
    TheoremInfo, parse_theorems, LocalBlock, parse_local_blocks,
    build_line_starts, line_col_to_offset, HOLParseError,
    parse_step_plan_output, StepPlan,
    parse_prefix_commands_output,
    _find_json_line, _frag_to_cmd,
)
from .hol_session import HOLSession, HOLDIR, escape_sml_string


@dataclass(frozen=True)
class SessionPosition:
    """Immutable snapshot of where the HOL session is within the active theorem.

    Updated atomically — only state_at sets this. All other methods
    read from it but never mutate it. This prevents the tracking state
    from getting out of sync (which silently killed incremental/reuse paths).
    """
    tactic_idx: int = 0          # Step index (0 = before any tactic)
    proof_offset: int | None = None  # None = at step boundary; int = partial offset
    content_hash: str = ""       # File hash when this position was established
    initialized: bool = False     # True after goal setup + successful replay

    def can_reuse(self, current_hash: str) -> bool:
        """Can we reuse this position without any replay?"""
        return self.initialized and self.content_hash == current_hash

    def at_step(self, idx: int, hash_: str) -> 'SessionPosition':
        """New position at a step boundary."""
        return SessionPosition(tactic_idx=idx, proof_offset=None,
                               content_hash=hash_, initialized=True)

    def at_partial(self, idx: int, offset: int, hash_: str) -> 'SessionPosition':
        """New position inside a step (partial offset)."""
        return SessionPosition(tactic_idx=idx, proof_offset=offset,
                               content_hash=hash_, initialized=True)


def _try_find_json_line(output: str, context: str = "") -> dict:
    """Best-effort JSON parse from HOL output. Returns {} on failure."""
    try:
        return _find_json_line(output, context)
    except HOLParseError:
        return {}


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
                f"    2) hol_setenv(env={{\"{var}\": \"/abs/path\"}})\n"
                f"    3) hol_restart(session=...)"
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

    # Generic: truncate raw output
    return output[:300]


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
    tactics_replayed: int     # Number of tactics replayed to reach this state
    tactics_total: int        # Total tactics in proof
    file_hash: str            # Content hash when this state was computed
    error: str | None = None  # Error message if replay failed
    timings: dict[str, float] | None = None  # Timing breakdown (ms)
    inside_by: bool = False   # Position is inside a decomposed by/>- subproof (between open/close)


@dataclass
class _TargetInfo:
    """Intermediate: parsed theorem + target position within it."""
    thm: TheoremInfo
    tactic_idx: int           # Step boundary at/before cursor
    total_tactics: int        # Total steps in step_plan
    need_partial: bool        # True when cursor is inside a step (not at boundary)
    proof_body_offset: int    # Offset into proof body
    incremental_update: tuple[int, int] | None  # (first_diff, old_tactic_idx) or None
    changed: bool             # Whether file content changed


@dataclass
class _NavResult:
    """Result of navigation strategy dispatch."""
    actual_replayed: int
    error_msg: str | None
    strategy: str             # "reused" | "incremental" | "prefix" | "checkpoint" | "replay"


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
    content_hash: str = ""        # File hash when checkpoint was saved


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
        # Extracted during _load_remaining_content BEFORE each Definition
        # block is processed (required because Hol_defn can't be re-called
        # after the constant exists without corrupting theory state).
        self._tc_goals: dict[str, str] = {}

        # Theorems whose proofs failed during content loading and were
        # auto-cheated to prevent cascading compile errors. Cleared on file change.
        self._failed_proofs: set[str] = set()

        # Oracle tags per theorem from verify_all_proofs.
        # e.g. {"thm_c": ["cheat"]} means thm_c transitively depends on a cheat.
        self._theorem_oracles: dict[str, list[str]] = {}

        # Resume goals: name -> {"asms": [...], "goal": "..."}
        # Extracted during _load_remaining_content BEFORE each Resume block
        self._resume_goals: dict[str, dict] = {}

        # True when pre-theorem context changed (e.g., open/Theory/Ancestors).
        # Such changes require rebuilding HOL session context from scratch.
        self._needs_session_reinit: bool = False

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

    def _reparse_if_changed(self) -> bool:
        """Re-read and parse file if content changed. Returns True if changed.
        
        Raises FileNotFoundError if file was deleted.
        """
        content = self.file.read_text()  # Let FileNotFoundError propagate
        content_hash = self._compute_hash(content)

        if content_hash == self._content_hash:
            return False

        # Find first changed line before updating
        old_content = self._content
        first_changed = self._first_changed_line(old_content, content)

        self._content = content
        self._content_hash = content_hash
        self._line_starts = build_line_starts(content)
        self._theorems = parse_theorems(content)
        self._local_blocks = parse_local_blocks(content)

        # Invalidate checkpoints and traces for theorems at or after the change
        if first_changed is not None:
            self._invalidate_from_line(first_changed)
            # Also reset loaded context tracking - can't trust context after change point
            if first_changed <= self._loaded_to_line:
                self._loaded_to_line = max(0, first_changed - 1)
                self._loaded_content_hash = ""  # Empty string = needs recompute

            # If change is before first theorem, pre-theorem context may have changed
            # (e.g., open/Theory/Ancestors). Rebuild HOL session on next query.
            first_thm_line = self._theorems[0].start_line if self._theorems else None
            if first_thm_line and first_changed < first_thm_line:
                self._needs_session_reinit = True
                self._loaded_to_line = 0
                self._loaded_content_hash = ""
                self._pos = SessionPosition()
                self._active_theorem = None

                # Invalidate all caches/checkpoints that depend on old context
                self._invalidate_all_checkpoints()
                self._proof_traces.clear()
                self._tc_goals.clear()
                self._resume_goals.clear()
                self._failed_proofs.clear()
                self._theorem_oracles.clear()

                # Invalidate saved base/deps checkpoints (stale imports/ancestors)
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
        if init_result.get("error"):
            self._needs_session_reinit = True
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

    async def _get_hierarchy_depth(self) -> int:
        """Get current PolyML SaveState hierarchy length.
        
        The hierarchy is a list of parent states. saveChild(path, N) saves as
        child of entry at index N-1. To save as child of the current state,
        use N = hierarchy length.
        """
        depth_result = await self.session.send(
            'length (PolyML.SaveState.showHierarchy());', timeout=5
        )
        depth_match = re.search(r'val it = (\d+)', depth_result)
        return int(depth_match.group(1)) if depth_match else 3  # Default for HOL4

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

    def _is_checkpoint_valid(self, theorem_name: str) -> bool:
        """Check if end_of_proof checkpoint exists and is valid."""
        ckpt = self._checkpoints.get(theorem_name)
        if ckpt is None:
            return False
        if ckpt.end_of_proof_path is None or not ckpt.end_of_proof_path.exists():
            return False
        if ckpt.content_hash != "" and ckpt.content_hash != self._content_hash:
            return False
        return True

    def _is_context_checkpoint_valid(self, theorem_name: str) -> bool:
        """Check if context checkpoint exists and is valid."""
        ckpt = self._checkpoints.get(theorem_name)
        if ckpt is None:
            return False
        if ckpt.context_path is None or not ckpt.context_path.exists():
            return False
        if ckpt.content_hash != "" and ckpt.content_hash != self._content_hash:
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
        ckpt_path = self._get_checkpoint_path(theorem_name, "end_of_proof")
        ckpt_path_str = escape_sml_string(str(ckpt_path))

        depth = await self._get_hierarchy_depth()
        # Save checkpoint directly from current state
        result = await self.session.send(
            f'PolyML.SaveState.saveChild ("{ckpt_path_str}", {depth});', timeout=30
        )
        if _is_hol_error(result):
            return False

        # Merge with existing entry (may already have context_path)
        if theorem_name in self._checkpoints:
            self._checkpoints[theorem_name].end_of_proof_path = ckpt_path
            self._checkpoints[theorem_name].tactics_count = tactics_count
        else:
            self._checkpoints[theorem_name] = TheoremCheckpoint(
                theorem_name=theorem_name,
                tactics_count=tactics_count,
                end_of_proof_path=ckpt_path,
                content_hash=self._content_hash,
            )
        return True

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
        ckpt_path = self._get_checkpoint_path(theorem_name, "context")
        ckpt_path_str = escape_sml_string(str(ckpt_path))

        depth = await self._get_hierarchy_depth()
        result = await self.session.send(
            f'PolyML.SaveState.saveChild ("{ckpt_path_str}", {depth});', timeout=60
        )
        if _is_hol_error(result):
            return

        # Update checkpoint dict (merge with any existing end_of_proof entry)
        if theorem_name in self._checkpoints:
            self._checkpoints[theorem_name].context_path = ckpt_path
        else:
            self._checkpoints[theorem_name] = TheoremCheckpoint(
                theorem_name=theorem_name,
                tactics_count=0,
                context_path=ckpt_path,
                content_hash=self._content_hash,
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

        # Invalidate checkpoints/traces/tc_goals/resume_goals for theorems at or after change point
        for thm in self._theorems:
            if thm.proof_end_line >= start_line:
                self._invalidate_checkpoint(thm.name)
                if thm.name in self._proof_traces:
                    del self._proof_traces[thm.name]
                if thm.name in self._tc_goals:
                    del self._tc_goals[thm.name]
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

    async def init(self) -> dict:
        """Initialize cursor - parse file and load deps.

        Does NOT verify theorems - that happens lazily via state_at/trace_proof.

        Returns:
            dict with:
              - theorems: list of {name, line, has_cheat}
              - cheats: list of cheat locations
              - error: error message if init failed
        """
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
        # Skip "Cannot find file" errors (build-time deps like HolKernel, or holmake not run)
        # but report other errors (actual load failures)
        try:
            deps = await get_script_dependencies(self.file)
            for dep in deps:
                result = await self.session.send(f'load "{dep}";', timeout=60)
                if _is_hol_error(result):
                    # "Cannot find file X.ui" means build-time dep or holmake not run - skip
                    if "Cannot find file" in result:
                        continue
                    return {
                        "theorems": [],
                        "cheats": [],
                        "error": f"Failed to load dependency {dep}: {result}",
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

        Calls extract_tc_goal_json which temporarily creates the defn via
        Hol_defn inside try_grammar_extension + try_theory_extension,
        extracts the TC goal string, then rolls back all changes.

        MUST be called BEFORE the Definition block is processed (before
        the function constant exists in the theory).

        Results are cached in self._tc_goals[thm.name].
        """
        goal_body = thm.goal.replace('\n', ' ').strip()
        escaped = escape_sml_string(goal_body)
        tc_result = await self.session.send(
            f'extract_tc_goal_json "{escaped}";', timeout=30
        )
        tc_data = _try_find_json_line(tc_result)
        if 'ok' in tc_data and tc_data['ok']:
            self._tc_goals[thm.name] = tc_data['ok']

    async def _extract_resume_goal(self, thm: TheoremInfo) -> None:
        """Extract goal for a Resume block from the suspension DB.
        
        Must be called AFTER the original Theorem with suspend has been loaded,
        but BEFORE the Resume block itself is loaded.
        
        Results are cached in self._resume_goals[thm.name].
        """
        if not thm.suspension_name or thm.label_name is None:
            return
        escaped_susp = escape_sml_string(thm.suspension_name)
        escaped_label = escape_sml_string(thm.label_name)
        result = await self.session.send(
            f'extract_resume_goal_json "{escaped_susp}" "{escaped_label}";',
            timeout=30
        )
        data = _try_find_json_line(result)
        if 'ok' in data:
            self._resume_goals[thm.name] = data['ok']

    async def _cheat_failed_theorem(self, thm: TheoremInfo) -> str | None:
        """After a proof failure, re-send the theorem with cheat to bind its name.

        Without this, later theorems that reference the failed one get a fatal
        Poly/ML compile error ("Value or constructor not declared").

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
            self._failed_proofs.add(thm.name)
            return None

        attrs = f"[{','.join(thm.attributes)}]" if thm.attributes else ""
        cheat_block = f'Theorem {thm.name}{attrs}:\n{thm.goal}\nProof\n  cheat\nQED'
        # Drain extra residual output from the failed proof before cheating
        await asyncio.sleep(0.1)
        await self.session._drain_pipe()
        result = await self.session.send(cheat_block, timeout=30)
        # Check for success: val <name> = ... : thm in output
        # (residual output from the original failed proof can pollute the result,
        # so checking for errors is unreliable — check for success instead)
        if f"val {thm.name}" in result:
            self._failed_proofs.add(thm.name)
            return None
        if _is_hol_error(result):
            return (
                f"Proof of '{thm.name}' failed (line {thm.start_line}) "
                f"and could not be cheated: {result[-500:]}"
            )
        self._failed_proofs.add(thm.name)
        return None

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

    async def _send_and_check(self, content: str, timeout: float) -> str | None:
        """Send content to HOL, return error string on fatal error, else None."""
        if not content.strip():
            return None
        result = await self.session.send(content, timeout=timeout)
        if _is_fatal_hol_error(result):
            return f"Error executing file content: {_format_context_error(result)}"
        return None

    async def _handle_theorem_error(self, thm: TheoremInfo, result: str) -> str | None:
        """Handle HOL error from a theorem send. Returns error string or None."""
        if thm.kind == "Definition":
            return f"Definition '{thm.name}' failed (line {thm.start_line}): {result}"
        return await self._cheat_failed_theorem(thm)

    async def _extract_goals_for(self, theorems: list[TheoremInfo]) -> None:
        """Extract Definition/Resume goals before theorems are processed."""
        for thm in theorems:
            if thm.kind == "Definition" and thm.proof_body and thm.name not in self._tc_goals:
                await self._extract_tc_goal(thm)
            if thm.kind == "Resume" and thm.name not in self._resume_goals:
                await self._extract_resume_goal(thm)

    async def _load_remaining_content(self) -> str | None:
        """Load remaining file content, theorem-by-theorem.

        When theorems fall inside SML `local ... in ... end` blocks, the entire
        block is sent as one chunk because Poly/ML requires the complete local
        declaration as a syntactic unit.

        Returns:
            Error message if a fatal load error occurs, else None.
        """
        content_lines = self._content.split('\n')
        remaining_thms = [t for t in self._theorems if t.proof_end_line > self._loaded_to_line]

        i = 0
        while i < len(remaining_thms):
            thm = remaining_thms[i]
            # Check if either the theorem or the pre-content (gap before it)
            # falls inside a local block.
            local_block = self._local_block_at(thm.start_line)
            if local_block is None and self._loaded_to_line < thm.start_line:
                local_block = self._local_block_overlapping(self._loaded_to_line, thm.start_line - 1)

            if local_block is None:
                # Normal theorem
                if thm.start_line > self._loaded_to_line:
                    err = await self._send_and_check(
                        '\n'.join(content_lines[self._line_to_idx(self._loaded_to_line):self._line_to_idx(thm.start_line)]),
                        timeout=60)
                    if err:
                        return err
                    self._loaded_to_line = thm.start_line

                await self._extract_goals_for([thm])

                thm_content = '\n'.join(content_lines[self._line_to_idx(thm.start_line):self._line_to_idx(thm.proof_end_line)])
                if thm_content.strip():
                    result = await self.session.send(thm_content, timeout=60)
                    if result.startswith("TIMEOUT") and thm.kind != "Definition":
                        self.session.interrupt()
                        await asyncio.sleep(0.5)
                        err = await self._cheat_failed_theorem(thm)
                        if err:
                            return f"Error executing file content: {_format_context_error(result)}"
                    elif _is_fatal_hol_error(result):
                        return f"Error executing file content: {_format_context_error(result)}"
                    elif _is_hol_error(result):
                        err = await self._handle_theorem_error(thm, result)
                        if err:
                            return err
                self._loaded_to_line = thm.proof_end_line
                i += 1
            else:
                # Local block: collect all theorems inside, send as one chunk
                lb = local_block
                block_thms = []
                while i < len(remaining_thms) and lb.local_line <= remaining_thms[i].start_line <= lb.end_line:
                    block_thms.append(remaining_thms[i])
                    i += 1

                await self._extract_goals_for(block_thms)

                block_end = lb.end_line + 1  # line after 'end'
                if block_end > self._loaded_to_line:
                    block_content = '\n'.join(content_lines[self._line_to_idx(self._loaded_to_line):self._line_to_idx(block_end)])
                    if block_content.strip():
                        result = await self.session.send(block_content, timeout=60)
                        if _is_fatal_hol_error(result):
                            return f"Error executing file content: {_format_context_error(result)}"
                        if _is_hol_error(result):
                            for bt in block_thms:
                                err = await self._handle_theorem_error(bt, result)
                                if err:
                                    return err
                    self._loaded_to_line = block_end

        # Trailing content after last theorem
        if self._theorems:
            total_lines = len(content_lines)
            if self._loaded_to_line <= total_lines:
                trailing_start = self._loaded_to_line + 1
                lb = self._local_block_overlapping(trailing_start, total_lines)
                if lb:
                    total_lines = max(total_lines, lb.end_line)
                trailing = '\n'.join(content_lines[self._line_to_idx(self._loaded_to_line):total_lines])
                err = await self._send_and_check(trailing, timeout=60)
                if err:
                    return err
                self._loaded_to_line = total_lines + 1

        self._loaded_content_hash = self._content_hash
        return None

    async def _load_context_to_line(self, target_line: int, timeout: float = 300) -> str | None:
        """Load file content up to target_line into HOL session.
        
        Loads content granularly - theorem by theorem - so that a broken proof
        in one theorem doesn't prevent loading of subsequent content.

        When theorems fall inside SML `local ... in ... end` blocks, the entire
        block is sent as one chunk because Poly/ML requires the complete local
        declaration as a syntactic unit.
        
        Args:
            target_line: 1-indexed line to load up to (exclusive)
            timeout: Timeout for HOL send (default 300s for large files)
            
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
            err = await self._send_and_check(to_load, timeout)
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
                        err = await self._send_and_check(pre, timeout)
                        if err:
                            return err

                    await self._extract_goals_for([thm])

                    thm_content = '\n'.join(content_lines[self._line_to_idx(thm.start_line):self._line_to_idx(thm.proof_end_line)])
                    if thm_content.strip():
                        result = await self.session.send(thm_content, timeout=timeout)
                        if _is_fatal_hol_error(result):
                            return f"Error executing file content: {_format_context_error(result)}"
                        if _is_hol_error(result):
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
                            result = await self.session.send(block_content, timeout=timeout)
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
                err = await self._send_and_check(remaining, timeout)
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

        # Parse step plan from proof body using TacticParse
        if thm.proof_body:
            escaped_body = escape_sml_string(thm.proof_body)
            step_result = await self.session.send(
                f'goalfrag_step_plan_json "{escaped_body}";', timeout=30
            )
            try:
                self._step_plan = parse_step_plan_output(step_result)
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
            if thm.name not in self._resume_goals:
                return f"Failed to extract Resume goal for '{thm.name}'"
            rg = self._resume_goals[thm.name]
            asms = rg.get('asms', [])
            goal_str = rg.get('goal', '')
            if asms:
                asm_terms = ", ".join(
                    f'Parse.Term [QUOTE "{escape_sml_string(a)}"]' for a in asms
                )
                gt_result = await self.session.send(
                    f'proofManagerLib.set_goalfrag([{asm_terms}], '
                    f'Parse.Term [QUOTE "{escape_sml_string(goal_str)}"]);',
                    timeout=30
                )
            else:
                gt_result = await self.session.send(f'gf `{goal_str}`;', timeout=30)
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

    async def _try_prefix_at(self, thm_name: str, offset: int) -> tuple[bool, str | None]:
        """Reset goal and try prefix replay up to offset in proof body.

        Sets up a fresh goal, generates prefix commands via sliceTacticBlock,
        and executes them. Returns (success, error_message).
        """
        thm = self._get_theorem(thm_name)
        if not thm or not thm.proof_body:
            return False, "No proof body"

        setup_err = await self._setup_proof_goal(thm_name)
        if setup_err:
            return False, setup_err

        escaped_body = escape_sml_string(thm.proof_body)
        prefix_result = await self.session.send(
            f'goalfrag_prefix_commands_json "{escaped_body}" {offset};',
            timeout=30
        )
        try:
            prefix_frags = parse_prefix_commands_output(prefix_result)
        except HOLParseError as e:
            return False, f"Failed to get prefix commands: {e}"

        if not prefix_frags:
            return True, None

        # Wrap each fragment with ef(goalFrag.*()) and send as one batch
        prefix_cmd = '\n'.join(_frag_to_cmd(t, x) for t, x in prefix_frags)
        result = await self.session.send(
            prefix_cmd, timeout=self._tactic_timeout or 30
        )
        if _is_hol_error(result):
            return False, result
        return True, None

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
        self, tactic_idx: int, need_partial: bool, proof_body_offset: int
    ) -> bool:
        """Try to reuse current session state for target position.

        Handles:
        - Exact match: same step boundary or partial offset → no replay
        - Forward: advance through delta steps → partial replay

        Returns True if session is now at target position.
        """
        if not self._pos.can_reuse(self._content_hash):
            return False

        at_step_boundary = self._pos.proof_offset is None

        if need_partial:
            # Partial position: only exact offset match works
            return (self._pos.proof_offset == proof_body_offset
                    and self._pos.tactic_idx == tactic_idx)

        # Step boundary reuse
        if not at_step_boundary:
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

        # Batch failed: recover last good state by replaying step-by-step.
        setup_err = await self._setup_proof_goal(thm_name)
        if setup_err:
            return 0, setup_err

        replayed = 0
        step_timeout = self._tactic_timeout or 30
        for cmd in cmds:
            step_result = await self.session.send(cmd, timeout=step_timeout)
            if _is_hol_error(step_result):
                if step_result.startswith("TIMEOUT"):
                    return replayed, f"Tactic replay timed out (>{step_timeout}s)"
                return replayed, f"Tactic replay failed: {step_result}"
            replayed += 1

        # Shouldn't happen: fallback fully succeeded but batch didn't?
        return replayed, f"Tactic replay failed: {result}"

    async def _replay_to_boundary(
        self, thm: TheoremInfo, tactic_idx: int, total_tactics: int
    ) -> tuple[bool, int, str | None, bool]:
        """Replay to a step boundary using checkpoint or full replay.

        Try O(1) checkpoint path first, then fall back to full replay with
        step-by-step fallback on batch failure.

        Returns (success, actual_replayed, error_msg, used_checkpoint).
        """
        # Try checkpoint path
        if self._is_checkpoint_valid(thm.name) and thm.proof_body:
            if await self._load_checkpoint_and_backup(thm.name, tactic_idx):
                return True, tactic_idx, None, True

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
                error=f"Position ({line}, {col}) is not within any theorem"
            )

        t1 = time.perf_counter()
        if self._active_theorem != thm_at_pos.name:
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
        need_partial = self._is_partial_position(
            proof_body_offset, tactic_idx, total_tactics, thm.proof_body or ""
        )

        return _TargetInfo(
            thm=thm, tactic_idx=tactic_idx, total_tactics=total_tactics,
            need_partial=need_partial, proof_body_offset=proof_body_offset,
            incremental_update=incremental_update, changed=changed,
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

    def _is_partial_position(
        self, proof_body_offset: int, tactic_idx: int, total_tactics: int,
        proof_body: str
    ) -> bool:
        """Is the offset inside a step (not at a step boundary)?"""
        step_before_end = self._step_plan[tactic_idx - 1].end if tactic_idx > 0 else 0
        current_step_end = (
            self._step_plan[tactic_idx].end if tactic_idx < total_tactics
            else len(proof_body)
        )
        return step_before_end < proof_body_offset < current_step_end

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
                self._step_plan = parse_step_plan_output(step_result)
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

        Priority chain: reuse → incremental → prefix → checkpoint → full replay.
        """
        # Strategy 1: Reuse current session state (file unchanged)
        if not target.changed and await self._try_reuse_state(
            target.tactic_idx, target.need_partial, target.proof_body_offset
        ):
            return _NavResult(actual_replayed=target.tactic_idx, error_msg=None, strategy="reused")

        # Strategy 2: Incremental update (file changed, common prefix available)
        if target.incremental_update is not None and await self._try_incremental_navigate(
            target.incremental_update[0], target.incremental_update[1], target.tactic_idx
        ):
            return _NavResult(actual_replayed=target.tactic_idx, error_msg=None, strategy="incremental")

        # Strategy 3: Partial position via prefix replay
        if target.need_partial and target.thm.proof_body:
            return await self._navigate_partial_target(target)

        # Strategy 4: Checkpoint or full replay (step boundary)
        return await self._navigate_step_boundary(target)

    async def _navigate_partial_target(self, target: _TargetInfo) -> _NavResult:
        """Navigate to a partial position inside a step via prefix replay."""
        ok, prefix_err = await self._try_prefix_at(
            target.thm.name, target.proof_body_offset
        )
        if ok:
            return _NavResult(
                actual_replayed=target.tactic_idx, error_msg=None, strategy="prefix"
            )

        # Best-effort: replay to nearest step boundary
        if target.tactic_idx > 0 and target.thm.proof_body:
            cmds = [step.cmd for step in self._step_plan[:target.tactic_idx]]
            batch_timeout = self._batch_timeout_for(target.tactic_idx)
            replayed, replay_error = await self._replay_steps_with_fallback(
                target.thm.name, cmds, batch_timeout
            )
            error_msg = replay_error or (
                f"Prefix replay failed at requested position: {prefix_err}; "
                f"showing nearest step boundary (tactic {target.tactic_idx}/{target.total_tactics})."
            )
            return _NavResult(actual_replayed=replayed, error_msg=error_msg, strategy="prefix")

        return _NavResult(
            actual_replayed=0, error_msg=f"Prefix replay failed: {prefix_err}", strategy="prefix"
        )

    async def _navigate_step_boundary(self, target: _TargetInfo) -> _NavResult:
        """Navigate to a step boundary via checkpoint or full replay."""
        success, replayed, replay_error, used_checkpoint = (
            await self._replay_to_boundary(
                target.thm, target.tactic_idx, target.total_tactics
            )
        )
        strategy = "checkpoint" if used_checkpoint else "replay"
        return _NavResult(actual_replayed=replayed, error_msg=replay_error, strategy=strategy)

    def _update_position(self, target: _TargetInfo, nav: _NavResult) -> None:
        """Update session position tracking after successful navigation."""
        if nav.error_msg is not None:
            return
        if target.need_partial:
            self._pos = self._pos.at_partial(
                target.tactic_idx, target.proof_body_offset, self._content_hash
            )
        else:
            self._pos = self._pos.at_step(target.tactic_idx, self._content_hash)

    async def _build_result(
        self, target: _TargetInfo, nav: _NavResult, timings: dict[str, float],
        t0: float, t3: float
    ) -> StateAtResult:
        """Fetch goals and assemble final result."""
        timings['replay'] = time.perf_counter() - t3
        timings['strategy'] = nav.strategy

        t4 = time.perf_counter()
        error_msg = nav.error_msg
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
            tactics_replayed=nav.actual_replayed,
            tactics_total=target.total_tactics,
            file_hash=self._content_hash,
            error=error_msg,
            timings=timings,
            inside_by=self._detect_inside_by(target.tactic_idx),
        )

    async def state_at(self, line: int, col: int = 1) -> StateAtResult:
        """Get proof state at file position using prefix-based replay.

        Auto-enters the theorem containing the position if not already active.
        """
        timings: dict[str, float] = {}
        t0 = time.perf_counter()

        changed = await self._prepare_session(line, col, timings)
        if isinstance(changed, StateAtResult):
            return changed

        thm = self._active_theorem_info()
        if isinstance(thm, StateAtResult):
            return thm

        target = await self._compute_target(thm, line, col, changed)
        if isinstance(target, StateAtResult):
            return target

        t3 = time.perf_counter()
        nav = await self._navigate_to_target(target)
        self._update_position(target, nav)
        return await self._build_result(target, nav, timings, t0, t3)

    def _parse_goals_json(self, output: str) -> list[dict]:
        """Parse JSON goal output from goals_json().

        Output format: {"ok":[{"asms":[...], "goal":"..."}, ...]} or {"err":"message"}
        Returns: List of goal dicts with 'asms' (list of assumption strings) and 'goal' (conclusion string)
        Raises: HOLParseError if HOL4 returned an error or output is malformed.
        """
        result = _find_json_line(output, "goals_json")

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
                await self._restore_to_deps()
            elif self._loaded_to_line > thm.start_line:
                predecessor = self._find_predecessor_checkpoint(thm)
                if predecessor is not None:
                    if not await self._load_context_checkpoint(predecessor.name):
                        await self._restore_to_deps()
                else:
                    await self._restore_to_deps()

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
        if 'ok' in parsed:
            oracles = parsed['ok'].get('oracles', [])
            if oracles:
                self._theorem_oracles[theorem_name] = oracles

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
            await self._restore_to_deps()
        else:
            # No checkpoint - must reload deps manually for clean state
            # This is slower but ensures correctness
            if self.session.is_running:
                await self.session.stop()
            await self.session.start()
            try:
                deps = await get_script_dependencies(self.file)
                for dep in deps:
                    result = await self.session.send(f'load "{dep}";', timeout=60)
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
                    step_plan = parse_step_plan_output(step_result)
                except HOLParseError:
                    step_plan = []
            else:
                step_plan = []

            if not step_plan:
                # No tactics - load theorem as-is
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    result = await self.session.send(thm_content, timeout=60)
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
                        cheat_err = await self._cheat_failed_theorem(thm)
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
                        resume_result = await self.session.send(thm_content, timeout=60)
                        if _is_hol_error(resume_result):
                            cheat_err = await self._cheat_failed_theorem(thm)
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
                        def_result = await self.session.send(thm_content, timeout=60)
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
                result = await self.session.send(
                    f'verify_resume_json "{escape_sml_string(thm.suspension_name or "")}" "{escape_sml_string(thm.label_name or "")}" "{thm.name}" {tactics_sml} {store} {tactic_timeout:.1f};',
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
            if 'ok' in parsed:
                oracles = parsed['ok'].get('oracles', [])
                if oracles:
                    self._theorem_oracles[thm.name] = oracles

            # For Definitions/Resume: always re-send the full block.
            # Definitions: create the constant and store def/ind theorems.
            # Resume: finalise the suspended subgoal.
            # For Theorems: re-send if attributes need registration.
            if thm.kind == "Resume":
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    resume_result = await self.session.send(thm_content, timeout=60)
                    if _is_hol_error(resume_result):
                        cheat_err = await self._cheat_failed_theorem(thm)
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
                cheat_err = await self._cheat_failed_theorem(thm)
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
