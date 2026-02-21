"""Proof cursor for navigating through theorems without reloading."""

import asyncio
import hashlib
import json
import re
import time
from dataclasses import dataclass, field
from pathlib import Path

from .hol_file_parser import (
    TheoremInfo, parse_theorems,
    build_line_starts, line_col_to_offset, HOLParseError,
    parse_step_plan_output, StepPlan,
    parse_prefix_commands_output,
    parse_step_positions_output,
)
from .hol_session import HOLSession, HOLDIR, escape_sml_string


def _find_json_line(output: str, prefix: str = "") -> dict:
    """Find and parse a JSON line from HOL output.

    Looks for {"ok":...} or {"err":...} patterns, either at the start of a line
    or embedded after other output (e.g., "metis: {"ok":...}").
    If prefix is provided, only looks for lines after that prefix.
    """
    for line in output.split('\n'):
        line = line.strip()
        # First try exact line match (most common case)
        if line.startswith('{"ok":') or line.startswith('{"err":'):
            try:
                return json.loads(line)
            except json.JSONDecodeError:
                pass
        # Then try to find embedded JSON (e.g., after metis progress output)
        # Look for {"ok": or {"err": anywhere in line
        for marker in ['{"ok":', '{"err":']:
            idx = line.find(marker)
            if idx >= 0:
                # Try to parse JSON starting from this position
                candidate = line[idx:]
                try:
                    return json.loads(candidate)
                except json.JSONDecodeError:
                    # JSON might be truncated or malformed, continue
                    pass
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
        return "Timeout loading context\n  Hint: check for infinite loops or increase timeout"

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
        raise RuntimeError(f"holdeptool.exe failed: {stderr.decode()}")

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


@dataclass
class TraceEntry:
    """Single entry in a proof timing trace."""
    cmd: str                    # Command that was executed
    real_ms: int                # Real time in milliseconds
    usr_ms: int                 # User CPU time in milliseconds
    sys_ms: int                 # System CPU time in milliseconds
    goals_before: int           # Number of goals before execution
    goals_after: int            # Number of goals after execution
    error: str | None = None    # Error message if tactic failed
    start_offset: int | None = None  # Start offset in theorem proof_body
    end_offset: int | None = None    # End offset in theorem proof_body


@dataclass
class TheoremCheckpoint:
    """Checkpoint state for a theorem."""
    theorem_name: str
    tactics_count: int            # Number of tactics when checkpoint saved
    end_of_proof_path: Path | None = None   # Checkpoint after all tactics (for state_at)
    last_accessed: float = field(default_factory=time.time)  # For LRU eviction
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
                 tactic_timeout: float = 5.0, max_checkpoints: int = 100):
        """Initialize file proof cursor.

        Args:
            source_file: Path to the SML script
            session: HOL session to use
            checkpoint_dir: Where to store checkpoints (default: .hol/cursor_checkpoints/)
            tactic_timeout: Max seconds per tactic (default 5.0, None=unlimited)
            max_checkpoints: Max theorem checkpoints to keep (default 100, LRU eviction)
        """
        self.file = source_file
        self.session = session

        # Always use goalstack mode - goaltree doesn't support eall() needed for replay
        
        # Tactic timeout for build discipline
        self._tactic_timeout = tactic_timeout
        
        # Checkpoint limit for disk space management (LRU eviction)
        self._max_checkpoints = max_checkpoints

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

        # Active theorem state
        self._active_theorem: str | None = None
        self._step_plan: list[StepPlan] = []  # Step boundaries aligned with e() commands
        self._current_tactic_idx: int = 0  # Current position in proof (for backup optimization)
        self._proof_initialized: bool = False  # Whether g/gt has been called for current theorem

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
                self._proof_initialized = False
                self._current_tactic_idx = 0
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
        self._proof_initialized = False
        self._current_tactic_idx = 0
        self._active_theorem = None
        self._step_plan = []
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
        """Check if cached checkpoint exists and file is present."""
        ckpt = self._checkpoints.get(theorem_name)
        if not ckpt:
            return False
        if not ckpt.end_of_proof_path or not ckpt.end_of_proof_path.exists():
            return False
        # Check content_hash matches current file (checkpoint may be stale after edit)
        if ckpt.content_hash and ckpt.content_hash != self._content_hash:
            return False
        return True

    async def _save_end_of_proof_checkpoint(self, theorem_name: str, tactics_count: int) -> bool:
        """Save checkpoint after all tactics have been replayed.

        Call this when goaltree has all tactics applied. The checkpoint
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

        self._checkpoints[theorem_name] = TheoremCheckpoint(
            theorem_name=theorem_name,
            tactics_count=tactics_count,
            end_of_proof_path=ckpt_path,
            last_accessed=time.time(),
            content_hash=self._content_hash,
        )
        # Evict old checkpoints if over limit
        self._evict_lru_checkpoints()
        return True

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
        if not ckpt or not self._is_checkpoint_valid(theorem_name):
            return False

        # Update access time for LRU
        ckpt.last_accessed = time.time()

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
            self._proof_initialized = False
            return False
        
        # Checkpoint (child of base) has all file content, mark as fully loaded
        # Restore the hash from when checkpoint was saved for correct staleness detection
        last_thm = self._theorems[-1] if self._theorems else None
        self._loaded_to_line = last_thm.proof_end_line if last_thm else 0
        self._loaded_content_hash = ckpt.content_hash

        # Backup to target position (~11ms for any N)
        backups_needed = ckpt.tactics_count - target_tactic_idx
        if backups_needed > 0:
            result = await self.session.send(f'backup_n {backups_needed};', timeout=30)
            if _is_hol_error(result):
                return False

        self._current_tactic_idx = target_tactic_idx
        self._proof_initialized = True
        return True

    def _invalidate_checkpoint(self, theorem_name: str) -> None:
        """Invalidate and delete checkpoint for a theorem."""
        ckpt = self._checkpoints.pop(theorem_name, None)
        if ckpt and ckpt.end_of_proof_path and ckpt.end_of_proof_path.exists():
            ckpt.end_of_proof_path.unlink()

    def _invalidate_all_checkpoints(self) -> None:
        """Invalidate all checkpoints (e.g., when file changes significantly)."""
        for name in list(self._checkpoints.keys()):
            self._invalidate_checkpoint(name)

    def _invalidate_from_line(self, start_line: int) -> None:
        """Invalidate checkpoints and traces for theorems at or after start_line.

        When content changes at line N, all theorems starting at N or later,
        OR containing line N, have invalid checkpoints/traces.
        Also invalidates for deleted theorems (not in new parse).
        """
        current_thm_names = {thm.name for thm in self._theorems}
        
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
                if thm.name in self._resume_goals:
                    del self._resume_goals[thm.name]

    def _evict_lru_checkpoints(self) -> None:
        """Evict oldest checkpoints if over limit.
        
        Uses last_accessed timestamp for LRU ordering.
        Keeps at most _max_checkpoints theorem checkpoints.
        """
        if len(self._checkpoints) <= self._max_checkpoints:
            return
        
        # Sort by last_accessed (oldest first)
        sorted_names = sorted(
            self._checkpoints.keys(),
            key=lambda n: self._checkpoints[n].last_accessed
        )
        
        # Evict oldest until under limit
        to_evict = len(self._checkpoints) - self._max_checkpoints
        for name in sorted_names[:to_evict]:
            self._invalidate_checkpoint(name)

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
                        "error": f"Failed to load dependency {dep}: {result[:200]}",
                    }
        except FileNotFoundError:
            pass  # holdeptool not available, skip dep loading

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
        tc_data = _find_json_line(tc_result)
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
        data = _find_json_line(result)
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
                    f"and could not be cheated: {result[:200]}"
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

    async def _load_remaining_content(self) -> str | None:
        """Load remaining file content, theorem-by-theorem.

        Returns:
            Error message if a fatal load error occurs, else None.
        """
        content_lines = self._content.split('\n')

        # Find theorems we haven't loaded yet
        remaining_thms = [t for t in self._theorems if t.proof_end_line > self._loaded_to_line]

        for thm in remaining_thms:
            # Load any content between current position and theorem start
            if thm.start_line > self._loaded_to_line:
                # _loaded_to_line is 1-indexed (first unloaded line), convert to 0-index
                start_idx = self._loaded_to_line - 1 if self._loaded_to_line > 0 else 0
                to_load = '\n'.join(content_lines[start_idx:thm.start_line - 1])
                if to_load.strip():
                    result = await self.session.send(to_load, timeout=60)
                    if _is_fatal_hol_error(result):
                        return f"Failed to load context: {_format_context_error(result)}"
                self._loaded_to_line = thm.start_line

            # For Definition blocks with Termination: extract TC goal BEFORE
            # processing the block. Hol_defn is called inside try_grammar_extension
            # + try_theory_extension so all theory/grammar changes are rolled back.
            # Must happen before the constant exists (rollback won't undo replacement).
            if thm.kind == "Definition" and thm.proof_body:
                await self._extract_tc_goal(thm)

            # For Resume blocks: extract goal from suspension BEFORE loading
            # (loading resolves the suspension label)
            if thm.kind == "Resume":
                await self._extract_resume_goal(thm)

            # Load the theorem (header through QED/End)
            thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
            if thm_content.strip():
                result = await self.session.send(thm_content, timeout=60)
                # Timeout during theorem proof: interrupt and auto-cheat
                # (the HOL process is still computing, must interrupt first)
                if result.startswith("TIMEOUT") and thm.kind not in ("Definition",):
                    self.session.interrupt()
                    # Small delay for HOL to process the interrupt
                    await asyncio.sleep(0.5)
                    cheat_err = await self._cheat_failed_theorem(thm)
                    if cheat_err:
                        return f"Failed to load context: {_format_context_error(result)}"
                elif _is_fatal_hol_error(result):
                    return f"Failed to load context: {_format_context_error(result)}"
                # On proof failure, cheat the theorem so its name is bound.
                # Without this, later theorems that reference it get a fatal
                # Poly/ML compile error ("Value or constructor not declared").
                elif _is_hol_error(result):
                    if thm.kind == "Definition":
                        # Definition failures are fatal — they create constants
                        # and can't be cheated. Report clearly.
                        return (
                            f"Definition '{thm.name}' failed (line {thm.start_line}): "
                            f"{result[:300]}"
                        )
                    cheat_err = await self._cheat_failed_theorem(thm)
                    if cheat_err:
                        return cheat_err
            # proof_end_line is "line after QED/End" (1-indexed); we loaded through it
            self._loaded_to_line = thm.proof_end_line

        # Load any trailing content after last theorem
        last_thm = self._theorems[-1] if self._theorems else None
        if last_thm:
            total_lines = len(content_lines)
            if self._loaded_to_line <= total_lines:
                start_idx = self._loaded_to_line - 1 if self._loaded_to_line > 0 else 0
                trailing = '\n'.join(content_lines[start_idx:])
                if trailing.strip():
                    result = await self.session.send(trailing, timeout=60)
                    if _is_fatal_hol_error(result):
                        return f"Failed to load context: {_format_context_error(result)}"
                self._loaded_to_line = total_lines + 1

        # Track content hash so _check_stale_state works correctly
        self._loaded_content_hash = self._content_hash
        return None

    async def _load_context_to_line(self, target_line: int, timeout: float = 300) -> str | None:
        """Load file content up to target_line into HOL session.
        
        Loads content granularly - theorem by theorem - so that a broken proof
        in one theorem doesn't prevent loading of subsequent content.
        
        Args:
            target_line: 1-indexed line to load up to (exclusive)
            timeout: Timeout for HOL send (default 300s for large files)
            
        Returns:
            Error message if failed, None if success.
        """
        if target_line <= self._loaded_to_line:
            return None  # Already loaded
            
        content_lines = self._content.split('\n')
        
        # Find theorems that are in the range we need to load
        # These need special handling because broken proofs can stop HOL processing
        theorems_in_range = [
            t for t in self._theorems
            if self._loaded_to_line < t.proof_end_line <= target_line
        ]
        
        if not theorems_in_range:
            # No theorems in range - simple case, load everything at once
            start_idx = max(0, self._loaded_to_line - 1) if self._loaded_to_line > 0 else 0
            to_load = '\n'.join(content_lines[start_idx:target_line - 1])
            if to_load.strip():
                result = await self.session.send(to_load, timeout=timeout)
                if _is_fatal_hol_error(result):
                    return f"Failed to load context: {_format_context_error(result)}"
        else:
            # Theorems in range - load piece by piece to isolate failures
            current_line = self._loaded_to_line
            
            for thm in theorems_in_range:
                # Load content before this theorem
                if thm.start_line > current_line:
                    start_idx = current_line - 1 if current_line > 0 else 0
                    pre_content = '\n'.join(content_lines[start_idx:thm.start_line - 1])
                    if pre_content.strip():
                        result = await self.session.send(pre_content, timeout=timeout)
                        if _is_fatal_hol_error(result):
                            return f"Failed to load context: {_format_context_error(result)}"
                
                # For Definition blocks: extract TC goal before processing
                if thm.kind == "Definition" and thm.proof_body and thm.name not in self._tc_goals:
                    await self._extract_tc_goal(thm)

                # For Resume blocks: extract goal before loading
                if thm.kind == "Resume" and thm.name not in self._resume_goals:
                    await self._extract_resume_goal(thm)

                # Load the theorem
                thm_content = '\n'.join(content_lines[thm.start_line - 1:thm.proof_end_line - 1])
                if thm_content.strip():
                    result = await self.session.send(thm_content, timeout=timeout)
                    if _is_fatal_hol_error(result):
                        return f"Failed to load context: {_format_context_error(result)}"
                    # On proof failure, cheat so later theorems can reference it
                    if _is_hol_error(result):
                        if thm.kind == "Definition":
                            return (
                                f"Definition '{thm.name}' failed (line {thm.start_line}): "
                                f"{result[:300]}"
                            )
                        cheat_err = await self._cheat_failed_theorem(thm)
                        if cheat_err:
                            return cheat_err
                
                # proof_end_line is "line after QED/End" (1-indexed); we loaded through it
                current_line = thm.proof_end_line
            
            # Load remaining content after last theorem (up to target_line)
            if current_line < target_line:
                start_idx = current_line - 1
                remaining = '\n'.join(content_lines[start_idx:target_line - 1])
                if remaining.strip():
                    result = await self.session.send(remaining, timeout=timeout)
                    if _is_fatal_hol_error(result):
                        return f"Failed to load context: {_format_context_error(result)}"
        
        # Update tracking
        loaded_content = '\n'.join(content_lines[:target_line - 1])
        self._loaded_to_line = target_line
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

        # Lazily save base checkpoint after first context load
        if not self._base_checkpoint_saved:
            await self.session.send('(drop_all(); PolyML.fullGC());', timeout=10)
            await self._save_base_checkpoint()

        # Parse step plan from proof body using TacticParse
        if thm.proof_body:
            escaped_body = escape_sml_string(thm.proof_body)
            step_result = await self.session.send(
                f'step_plan_json "{escaped_body}";', timeout=30
            )
            try:
                self._step_plan = parse_step_plan_output(step_result)
            except HOLParseError as e:
                return {"error": f"Failed to parse step plan: {e}"}
        else:
            self._step_plan = []

        self._active_theorem = name
        self._current_tactic_idx = 0  # Reset position for new theorem
        self._proof_initialized = False  # Will be set on first state_at

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
        Returns error string on failure, None on success.
        """
        thm = self._get_theorem(thm_name)
        if not thm:
            return f"Theorem '{thm_name}' not found"

        await self.session.send('drop_all();', timeout=5)

        if thm.kind == "Resume" and thm.name in self._resume_goals:
            rg = self._resume_goals[thm.name]
            asms = rg.get('asms', [])
            goal_str = rg.get('goal', '')
            if asms:
                asm_terms = ", ".join(
                    f'Parse.Term [QUOTE "{escape_sml_string(a)}"]' for a in asms
                )
                gt_result = await self.session.send(
                    f'proofManagerLib.set_goal([{asm_terms}], '
                    f'Parse.Term [QUOTE "{escape_sml_string(goal_str)}"]);',
                    timeout=30
                )
            else:
                gt_result = await self.session.send(f'g `{goal_str}`;', timeout=30)
        elif thm.kind == "Definition" and thm.name in self._tc_goals:
            tc_goal = self._tc_goals[thm.name]
            gt_result = await self.session.send(f'g `{tc_goal}`;', timeout=30)
        else:
            goal = thm.goal.replace('\n', ' ').strip()
            gt_result = await self.session.send(f'g `{goal}`;', timeout=30)

        if _is_hol_error(gt_result):
            self._proof_initialized = False
            return f"Failed to set up goal: {gt_result[:300]}"
        self._proof_initialized = True
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
            f'prefix_commands_json "{escaped_body}" {offset};',
            timeout=30
        )
        try:
            prefix_cmd = parse_prefix_commands_output(prefix_result)
        except HOLParseError as e:
            return False, f"Failed to get prefix commands: {e}"

        if not prefix_cmd.strip():
            return True, None

        result = await self.session.send(
            prefix_cmd, timeout=self._tactic_timeout or 30
        )
        if _is_hol_error(result):
            return False, result[:200]
        return True, None

    async def find_failing_substep(
        self, thm_name: str, failed_step_idx: int
    ) -> dict | None:
        """Binary search within a coarse step to pinpoint the failing substep.

        Uses step_positions for fine-grained boundaries within the failing step,
        then binary searches with prefix replay to find the exact failing substep.

        Args:
            thm_name: Theorem name (must be the active theorem with step_plan set)
            failed_step_idx: 0-based index of the failing step in step_plan

        Returns:
            Dict with {start_offset, end_offset, idx, count} or None if no refinement.
        """
        thm = self._get_theorem(thm_name)
        if not thm or not thm.proof_body:
            return None
        if failed_step_idx < 0 or failed_step_idx >= len(self._step_plan):
            return None

        # Get fine-grained positions within the proof body
        escaped_body = escape_sml_string(thm.proof_body)
        try:
            pos_result = await self.session.send(
                f'step_positions_json "{escaped_body}";', timeout=10
            )
            all_positions = parse_step_positions_output(pos_result)
        except (HOLParseError, Exception):
            return None

        # Filter to positions inside the failing step's range
        step_start = self._step_plan[failed_step_idx - 1].end if failed_step_idx > 0 else 0
        step_end = self._step_plan[failed_step_idx].end
        candidates = [p for p in all_positions if step_start < p <= step_end]
        if len(candidates) <= 1:
            return None

        # Build (start, end) offset pairs for each substep
        substeps = []
        prev = step_start
        for pos in candidates:
            substeps.append((prev, pos))
            prev = pos

        # Binary search on substep end offsets
        low = -1  # before first substep (nothing replayed)
        high = len(substeps) - 1  # whole step fails, so some substep fails

        # Quick check: does prefix up to first substep succeed?
        first_ok, _ = await self._try_prefix_at(thm_name, substeps[0][1])
        if not first_ok:
            high = 0
        else:
            low = 0
            while high - low > 1:
                mid = (low + high) // 2
                mid_ok, _ = await self._try_prefix_at(thm_name, substeps[mid][1])
                if mid_ok:
                    low = mid
                else:
                    high = mid

        ss, se = substeps[high]
        return {
            'start_offset': ss,
            'end_offset': se,
            'idx': high,
            'count': len(substeps),
        }

    async def state_at(self, line: int, col: int = 1) -> StateAtResult:
        """Get proof state at file position using prefix-based replay.

        Uses HOL's TacticParse.sliceTacticBlock to generate a valid prefix
        for any position, then executes it with a single e() call.

        Auto-enters the theorem containing the position if not already active.

        Args:
            line: 1-indexed line number
            col: 1-indexed column number (default 1)

        Returns:
            StateAtResult with goals, tactic index, etc.
        """
        timings: dict[str, float] = {}
        t0 = time.perf_counter()

        # Reparse if file changed
        try:
            changed = self._reparse_if_changed()
        except FileNotFoundError:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash="",
                error=f"File not found: {self.file}"
            )
        timings['reparse'] = time.perf_counter() - t0

        # Rebuild session/context when pre-theorem header changed
        reinit_error = await self._reinitialize_session_if_needed()
        if reinit_error:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash, error=reinit_error
            )

        # Find theorem at position and auto-enter if needed
        thm_at_pos = self._get_theorem_at_position(line)
        if not thm_at_pos:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash,
                error=f"Position ({line}, {col}) is not within any theorem"
            )

        # Auto-enter theorem if different from active
        t1 = time.perf_counter()
        if self._active_theorem != thm_at_pos.name:
            enter_result = await self.enter_theorem(thm_at_pos.name)
            if "error" in enter_result:
                return StateAtResult(
                    goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                    file_hash=self._content_hash, error=enter_result["error"]
                )
            # Note: enter_theorem already parses step_plan, so no need to set changed=True
            # Checkpoint invalidation only on actual file changes (handled by _reparse_if_changed)
        timings['enter_theorem'] = time.perf_counter() - t1

        thm = self._get_theorem(self._active_theorem)
        if not thm:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash, error=f"Theorem '{self._active_theorem}' no longer exists"
            )

        # If file changed, invalidate checkpoint and re-parse step positions
        t2 = time.perf_counter()
        if changed:
            self._invalidate_checkpoint(self._active_theorem)
            if thm.proof_body:
                escaped_body = escape_sml_string(thm.proof_body)
                step_result = await self.session.send(
                    f'step_plan_json "{escaped_body}";', timeout=30
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
        timings['parse_steps'] = time.perf_counter() - t2

        # Check if position is within theorem bounds (include QED line)
        # proof_end_line is "line after QED", so QED is at proof_end_line - 1
        proof_keyword_line = thm.proof_start_line - 1
        qed_line = thm.proof_end_line - 1
        if line < proof_keyword_line or line > qed_line:
            return StateAtResult(
                goals=[], tactic_idx=0, tactics_replayed=0, tactics_total=0,
                file_hash=self._content_hash,
                error=f"Position ({line}, {col}) not in theorem '{self._active_theorem}' "
                      f"(valid lines {proof_keyword_line}-{qed_line})"
            )

        # Convert (line, col) to proof body offset
        if line == qed_line:
            # On QED line: we want ALL tactics executed
            # Use end of proof body
            proof_body_offset = len(thm.proof_body) if thm.proof_body else 0
        else:
            file_offset = line_col_to_offset(line, col, self._line_starts)
            proof_body_offset = max(0, file_offset - thm.proof_body_offset)

        # Find tactic index for reporting (which step boundary we're at/past)
        # Uses step_plan ends which are aligned with executable e() commands
        tactic_idx = 0
        for i, step in enumerate(self._step_plan):
            if proof_body_offset >= step.end:
                tactic_idx = i + 1
            else:
                break

        total_tactics = len(self._step_plan)
        error_msg = None
        t3 = time.perf_counter()

        # Calculate step boundary info for O(1) access
        # step_before_end: end offset of last complete step (0 if none)
        step_before_end = self._step_plan[tactic_idx - 1].end if tactic_idx > 0 else 0
        # Current step end (for detecting if we're inside a step)
        current_step_end = self._step_plan[tactic_idx].end if tactic_idx < total_tactics else (len(thm.proof_body) if thm.proof_body else 0)
        # Need partial replay if we're inside a step (not at a boundary)
        # This enables fine-grained navigation within atomic ThenLT steps
        need_partial = proof_body_offset > step_before_end and proof_body_offset < current_step_end
        actual_replayed = 0

        # Two paths for navigation:
        # 1. Checkpoint path: O(1) to step boundaries via checkpoint + backup_n
        # 2. Prefix/targeted replay path for fine-grained positions or broken proofs
        #
        # For fine-grained positions (need_partial=true), use prefix replay directly.
        # For step boundaries without a checkpoint, replay only up to requested step
        # (not the full proof) so later broken tactics don't corrupt earlier states.

        async def _replay_with_fallback(cmds: list[str], batch_timeout: int) -> tuple[int, str | None]:
            """Replay commands; on batch failure, replay one-by-one to recover progress."""
            if not cmds:
                return 0, None

            batch_cmds = "".join(cmds)
            if not batch_cmds.strip():
                return 0, None

            result = await self.session.send(batch_cmds, timeout=batch_timeout)
            if not _is_hol_error(result):
                return len(cmds), None

            # Batch failed: recover last good state by replaying step-by-step.
            # This keeps hol_state_at useful on broken proofs.
            setup_err = await self._setup_proof_goal(thm.name)
            if setup_err:
                return 0, setup_err

            replayed = 0
            step_timeout = self._tactic_timeout or 30
            for cmd in cmds:
                step_result = await self.session.send(cmd, timeout=step_timeout)
                if _is_hol_error(step_result):
                    if step_result.startswith("TIMEOUT"):
                        return replayed, f"Tactic replay timed out (>{step_timeout}s)"
                    return replayed, f"Tactic replay failed: {step_result[:200]}"
                replayed += 1

            # Shouldn't happen, but keep original batch error if fallback fully succeeds.
            return replayed, f"Tactic replay failed: {result[:200]}"

        used_checkpoint = False

        if need_partial and thm.proof_body:
            # Fine-grained position: use prefix replay from theorem start
            # This correctly handles ThenLT semantics via sliceTacticBlock.
            ok, prefix_err = await self._try_prefix_at(thm.name, proof_body_offset)
            if ok:
                actual_replayed = tactic_idx
            else:
                error_msg = f"Prefix replay failed: {prefix_err}"

                # Best-effort recovery for broken proofs: find nearest earlier
                # prefix that still executes, then keep that state/goals.
                low = step_before_end
                high = proof_body_offset
                best = step_before_end
                attempts = 0
                while high - low > 1 and attempts < 12:
                    mid = (low + high) // 2
                    mid_ok, _ = await self._try_prefix_at(thm.name, mid)
                    if mid_ok:
                        best = mid
                        low = mid
                    else:
                        high = mid
                    attempts += 1

                if best > step_before_end:
                    best_ok, best_err = await self._try_prefix_at(thm.name, best)
                    if best_ok:
                        actual_replayed = sum(1 for step in self._step_plan if step.end <= best)
                        error_msg = (
                            f"Prefix replay failed at requested position: {prefix_err}; "
                            f"using nearest valid prefix at offset {best}."
                        )
                    elif best_err and not error_msg:
                        error_msg = f"Prefix replay failed: {best_err}"
                else:
                    # Binary search didn't find a better offset within this step.
                    # Fall back to the step boundary so goals reflect completed steps.
                    boundary_ok, _ = await self._try_prefix_at(thm.name, step_before_end)
                    if boundary_ok:
                        actual_replayed = tactic_idx
        else:
            # Step boundary: try O(1) checkpoint path
            if self._is_checkpoint_valid(self._active_theorem) and thm.proof_body:
                # Load checkpoint (at proof end) and backup to target step
                if await self._load_checkpoint_and_backup(self._active_theorem, tactic_idx):
                    used_checkpoint = True
                    actual_replayed = tactic_idx

            if not used_checkpoint:
                setup_err = await self._setup_proof_goal(thm.name)
                if setup_err:
                    return StateAtResult(
                        goals=[], tactic_idx=tactic_idx, tactics_replayed=0,
                        tactics_total=total_tactics, file_hash=self._content_hash,
                        error=setup_err
                    )

                if thm.proof_body and total_tactics > 0:
                    # If user asks for proof end, replay full theorem and checkpoint on success.
                    # Otherwise replay only requested prefix to avoid failures in later tactics.
                    if tactic_idx == total_tactics:
                        cmds = [step.cmd for step in self._step_plan]
                        batch_timeout = max(30, int(self._tactic_timeout * total_tactics)) if self._tactic_timeout else 300
                        replayed, replay_error = await _replay_with_fallback(cmds, batch_timeout)
                        actual_replayed = replayed
                        error_msg = replay_error

                        if replay_error is None:
                            # Save checkpoint at proof end for O(1) future access
                            await self._save_end_of_proof_checkpoint(self._active_theorem, total_tactics)
                    else:
                        cmds = [step.cmd for step in self._step_plan[:tactic_idx]]
                        # Prefix replay timeout scales with commands actually replayed
                        replay_steps = max(1, tactic_idx)
                        batch_timeout = max(30, int(self._tactic_timeout * replay_steps)) if self._tactic_timeout else 300
                        replayed, replay_error = await _replay_with_fallback(cmds, batch_timeout)
                        actual_replayed = replayed
                        error_msg = replay_error

        timings['replay'] = time.perf_counter() - t3
        timings['used_checkpoint'] = 1.0 if used_checkpoint else 0.0

        # Get current goals as JSON
        t4 = time.perf_counter()
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
            tactic_idx=tactic_idx,
            tactics_replayed=actual_replayed,
            tactics_total=total_tactics,
            file_hash=self._content_hash,
            error=error_msg,
            timings=timings,
        )

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

        # Restore to deps-only state for holmake-matching verification
        if self._deps_checkpoint_saved:
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
        if thm.kind == "Resume":
            if thm.name not in self._resume_goals:
                await self._extract_resume_goal(thm)
            rg = self._resume_goals.get(thm.name)
            if not rg:
                return []  # Can't extract goal from suspension
            goal = rg.get('goal', '')
            asms = rg.get('asms', [])
        elif thm.kind == "Definition" and thm.name in self._tc_goals:
            goal = self._tc_goals[thm.name]
            asms = []
        else:
            goal = thm.goal.replace('\n', ' ').strip()
            asms = []
        tactics_sml = "[" + ",".join(
            f'"{escape_sml_string(t)}"' for t in tactics
        ) + "]"
        tactic_timeout = self._tactic_timeout or 60.0
        # Python timeout = per-tactic timeout * num tactics + buffer
        python_timeout = tactic_timeout * len(tactics) + 10
        if asms:
            asms_sml = "[" + ",".join(
                f'"{escape_sml_string(a)}"' for a in asms
            ) + "]"
            result = await self.session.send(
                f'verify_theorem_with_asms_json "{escape_sml_string(goal)}" {asms_sml} "{theorem_name}" {tactics_sml} false {tactic_timeout:.1f};',
                timeout=max(30, python_timeout)
            )
        else:
            result = await self.session.send(
                f'verify_theorem_json "{escape_sml_string(goal)}" "{theorem_name}" {tactics_sml} false {tactic_timeout:.1f};',
                timeout=max(30, python_timeout)
            )

        # Parse response into TraceEntry list
        parsed = _find_json_line(result)
        trace = []
        steps = [step for step in self._step_plan if step.cmd.strip()]
        if 'ok' in parsed:
            for i, entry in enumerate(parsed['ok'].get('trace', [])):
                cmd = tactics[i] if i < len(tactics) else ""
                start_offset = steps[i - 1].end if i > 0 and i - 1 < len(steps) else 0
                end_offset = steps[i].end if i < len(steps) else None
                trace.append(TraceEntry(
                    cmd=cmd,
                    real_ms=entry.get('real_ms', 0),
                    usr_ms=0, sys_ms=0,
                    goals_before=entry.get('goals_before', 0),
                    goals_after=entry.get('goals_after', 0),
                    error=entry.get('err'),
                    start_offset=start_offset,
                    end_offset=end_offset,
                ))
        elif 'err' in parsed:
            trace.append(TraceEntry(
                cmd="", real_ms=0, usr_ms=0, sys_ms=0,
                goals_before=0, goals_after=0, error=parsed['err']
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
            except FileNotFoundError:
                pass  # holdeptool not available

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
                    f'step_plan_json "{escaped_body}";', timeout=30
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
                                goals_before=0, goals_after=0,
                                error=f"Definition failed: {result[:200]}"
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
            # For Resume: extract goal from suspension DB.
            asms = []
            if thm.kind == "Resume":
                if thm.name not in self._resume_goals:
                    await self._extract_resume_goal(thm)
                rg = self._resume_goals.get(thm.name)
                if rg:
                    goal = rg.get('goal', '')
                    asms = rg.get('asms', [])
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
                                goals_before=0, goals_after=0,
                                error=f"Definition failed: {def_result[:200]}"
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
            if asms:
                asms_sml = "[" + ",".join(
                    f'"{escape_sml_string(a)}"' for a in asms
                ) + "]"
                result = await self.session.send(
                    f'verify_theorem_with_asms_json "{escape_sml_string(goal)}" {asms_sml} "{thm.name}" {tactics_sml} {store} {tactic_timeout:.1f};',
                    timeout=max(30, python_timeout)
                )
            else:
                result = await self.session.send(
                    f'verify_theorem_json "{escape_sml_string(goal)}" "{thm.name}" {tactics_sml} {store} {tactic_timeout:.1f};',
                    timeout=max(30, python_timeout)
                )

            # Parse response and convert to TraceEntry list
            parsed = _find_json_line(result)
            trace = []
            steps = [step for step in step_plan if step.cmd.strip()]
            if 'ok' in parsed:
                for i, entry in enumerate(parsed['ok'].get('trace', [])):
                    cmd = tactics[i] if i < len(tactics) else ""
                    start_offset = steps[i - 1].end if i > 0 and i - 1 < len(steps) else 0
                    end_offset = steps[i].end if i < len(steps) else None
                    trace.append(TraceEntry(
                        cmd=cmd,
                        real_ms=entry.get('real_ms', 0),
                        usr_ms=0, sys_ms=0,
                        goals_before=entry.get('goals_before', 0),
                        goals_after=entry.get('goals_after', 0),
                        error=entry.get('err'),
                        start_offset=start_offset,
                        end_offset=end_offset,
                    ))
            elif 'err' in parsed:
                # Goal setup failed - record single error entry
                trace.append(TraceEntry(
                    cmd="", real_ms=0, usr_ms=0, sys_ms=0,
                    goals_before=0, goals_after=0, error=parsed['err']
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
                            goals_before=0, goals_after=0,
                            error=f"Definition failed: {def_result[:200]}"
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
