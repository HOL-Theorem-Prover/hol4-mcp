"""Regression tests for checkpoint invalidation, replay cost, and the
per-theorem load budget.

Each test asserts the CORRECT behaviour; they were written red under
``xfail(strict=True)`` and the markers came off when the fixes landed.

Covered findings:

  #9  Checkpoint ``content_hash`` is the hash of the WHOLE file, so an edit
      anywhere invalidates every checkpoint — including those of theorems
      entirely before the change, which ``_invalidate_from_line`` deliberately
      RETAINS.  The two merge branches of the save path
      (``_save_context_checkpoint`` / ``_save_end_of_proof_checkpoint``) update
      the path but not the hash, so a checkpoint re-saved under the current file
      content is judged invalid the moment it is written.

  A-4 (field observation) A theorem with 17 ``Resume`` bodies navigated in 4.2s
      (``hash=match``, ``replayed=0/2``); editing ONE ``Resume`` body forced a
      182s full replay (``pos_before=(idx=0,init,hash=miss)``) even though the
      main proof and the earlier ``Resume`` bodies were untouched.  Same root
      cause as #9, in the shape that costs the most in practice: the whole
      chain prefix is discarded for an edit confined to its last block.

  #14 The documented per-theorem 120s auto-cheat budget (``PER_THEOREM_TIMEOUT``)
      only exists in ``_load_remaining_content``, which nothing calls.  The live
      loader ``_load_context_to_line`` sends each prefix theorem with the
      caller's timeout (300s by default) and treats a TIMEOUT as FATAL, so a
      slow prefix theorem aborts navigation instead of being cheated-and-reported
      at 120s.

  A-5 (field observation) An edit landing in a currently BROKEN suspend/Resume
      chain forces ``_needs_session_reinit``, ``_loaded_to_line = 0`` and
      ``_invalidate_all_checkpoints()``.  That reinit is DELIBERATE (the
      suspension store is append/consume-only and cannot be partially rolled
      back) and is NOT what is tested here.  What is tested: the caller is never
      told that the next navigation now costs a cold replay from dependencies —
      490s in the field, with ``status`` reporting nothing at all.

All of these are pure over parsed file state and the save/load bookkeeping, so
they run against a stubbed session — no HOL process, no wall-clock assertions.
"""

import re
from pathlib import Path

import pytest

from hol4_mcp.hol_cursor import (
    PER_THEOREM_TIMEOUT,
    FileProofCursor,
    TheoremCheckpoint,
)


# ---------------------------------------------------------------------------
# Session stubs
# ---------------------------------------------------------------------------

class _SaveStateSession:
    """Stub session that emulates the Poly/ML SaveState calls the checkpoint
    code makes: ``showHierarchy`` returns a depth or a three-entry hierarchy,
    ``saveChild`` creates the checkpoint file so existence checks see a real
    save."""

    def __init__(self):
        self.sent: list[tuple[str, float | None]] = []

    async def send(self, command: str, timeout: float | None = None) -> str:
        self.sent.append((command, timeout))
        if "length (PolyML.SaveState.showHierarchy" in command:
            return "> val it = 3 : int"
        if "showHierarchy" in command:
            return '> val it = ["state0", "heap", "base"] : string list'
        m = re.search(r'saveChild\s*\("([^"]+)"', command)
        if m:
            Path(m.group(1)).write_text("stub checkpoint")
        return "> val it = () : unit"


class _NoOverwriteSaveStateSession(_SaveStateSession):
    """Poly/ML-like refusal when a live parent filename is reused."""

    async def send(self, command: str, timeout: float | None = None) -> str:
        match = re.search(r'saveChild\s*\("([^"]+)"', command)
        if match and Path(match.group(1)).exists():
            return "Exception- SysErr: File being saved is used as a parent of this file"
        return await super().send(command, timeout)


class _TimeoutSession:
    """Stub session whose sends succeed except for the one carrying
    ``marker``, which reports a HOL timeout."""

    def __init__(self, marker: str):
        self.marker = marker
        self.sent: list[tuple[str, float | None]] = []
        self.interrupts = 0

    async def send(self, command: str, timeout: float | None = None) -> str:
        self.sent.append((command, timeout))
        if self.marker in command:
            return f"TIMEOUT: no response from HOL after {timeout}s"
        return "> val it = () : unit"

    def interrupt(self) -> None:
        self.interrupts += 1

    async def drain_stale(self) -> None:
        pass


def _theorem_sends(session, first_line: str) -> list[tuple[str, float | None]]:
    """Sends whose payload starts with ``first_line`` (a theorem's own text)."""
    return [(c, t) for c, t in session.sent if c.lstrip().startswith(first_line)]


# ---------------------------------------------------------------------------
# Finding #9 — full-file hash kills checkpoints of untouched theorems
# ---------------------------------------------------------------------------

TWO_THEOREM_SCRIPT = (
    "open HolKernel Parse boolLib bossLib;\n"        # 1
    "\n"                                             # 2
    'val _ = new_theory "reprockpttwo";\n'            # 3
    "\n"                                             # 4
    "Theorem first_thm:\n"                           # 5
    "  !x:num. x = x\n"                              # 6
    "Proof\n"                                        # 7
    "  simp[]\n"                                     # 8
    "QED\n"                                          # 9
    "\n"                                             # 10
    "Theorem second_thm:\n"                          # 11
    "  !y:num. y + 0 = y\n"                          # 12
    "Proof\n"                                        # 13
    "  simp[]\n"                                     # 14
    "QED\n"                                          # 15
    "\n"                                             # 16
    "val _ = export_theory();\n"                     # 17
)

SECOND_BODY_IDX = 13     # 0-based index of second_thm's tactic line (line 14)


def _add_context_checkpoint(cursor: FileProofCursor, name: str) -> Path:
    """Record a context checkpoint for ``name`` under the CURRENT file content,
    exactly as a completed ``_load_context_to_line`` would."""
    cursor._checkpoint_dir.mkdir(parents=True, exist_ok=True)
    path = cursor._get_checkpoint_path(name, "context")
    path.write_text("stub checkpoint")
    cursor._checkpoints[name] = TheoremCheckpoint(
        theorem_name=name,
        tactics_count=0,
        context_path=path,
        content_hash=cursor._theorem_prefix_hash(name),   # as the save path stamps it
    )
    return path


def _checkpointed_then_edited(tmp_path: Path) -> FileProofCursor:
    """Cursor over ``TWO_THEOREM_SCRIPT`` with a context checkpoint for
    ``first_thm``, after an edit confined to ``second_thm``'s proof body.

    ``first_thm`` ends at line 10; the edit is at line 14, so
    ``_invalidate_from_line`` keeps its checkpoint entry — only the hash test
    can reject it.
    """
    script = tmp_path / "reprockpttwoScript.sml"
    script.write_text(TWO_THEOREM_SCRIPT)
    cursor = FileProofCursor(
        script, session=_SaveStateSession(), checkpoint_dir=tmp_path / "ckpt"
    )
    cursor._reparse_if_changed()
    cursor._needs_session_reinit = False     # initial parse, not an edit

    _add_context_checkpoint(cursor, "first_thm")
    assert cursor._is_context_checkpoint_valid("first_thm"), \
        "setup: checkpoint invalid before any edit"

    lines = TWO_THEOREM_SCRIPT.split("\n")
    assert lines[SECOND_BODY_IDX] == "  simp[]", \
        f"setup: unexpected line {lines[SECOND_BODY_IDX]!r}"
    lines[SECOND_BODY_IDX] = "  rw[]"
    script.write_text("\n".join(lines))
    assert cursor._reparse_if_changed(), "setup: edit not detected"
    assert "first_thm" in cursor._checkpoints, \
        "setup: _invalidate_from_line dropped the entry, hash is not the issue"
    return cursor


def test_edit_to_later_theorem_keeps_earlier_checkpoint(tmp_path: Path):
    """Editing ``second_thm`` must not invalidate ``first_thm``'s checkpoint.

    Nothing at or before ``first_thm``'s ``QED`` changed, so the saved theory
    state is still an exact prefix of the current file; discarding it forces
    ``_restore_to_deps`` plus a full prefix re-replay for every later query.
    """
    cursor = _checkpointed_then_edited(tmp_path)

    assert cursor._is_context_checkpoint_valid("first_thm"), (
        "first_thm's context checkpoint was rejected after an edit that lands "
        "4 lines past its QED; the state it captures is unaffected by that edit"
    )


@pytest.mark.parametrize("kind", ["context", "end_of_proof"])
async def test_merge_save_refreshes_checkpoint_hash(tmp_path: Path, kind: str):
    """A checkpoint saved from the current session state must validate.

    Both save paths take a merge branch when an entry already exists (the usual
    case: a context checkpoint from loading, then an end-of-proof checkpoint
    from ``state_at``). The merge updates the path only, so the entry keeps the
    hash of the file as it was at the FIRST save and is rejected immediately.
    """
    cursor = _checkpointed_then_edited(tmp_path)
    cursor._base_checkpoint_saved = True    # base checkpoint exists in a live run

    if kind == "context":
        await cursor._save_context_checkpoint("first_thm")
        valid = cursor._is_context_checkpoint_valid("first_thm")
    else:
        saved = await cursor._save_end_of_proof_checkpoint("first_thm", 1)
        assert saved, "setup: end_of_proof save reported failure"
        valid = cursor._is_checkpoint_valid("first_thm")

    ckpt = cursor._checkpoints["first_thm"]
    assert valid, (
        f"the {kind} checkpoint just saved under the current file content is "
        f"already invalid: entry hash {ckpt.content_hash[:12]}... vs file hash "
        f"{cursor._content_hash[:12]}..., so the very next navigation re-replays"
    )


async def test_repeated_context_save_uses_fresh_path(tmp_path: Path):
    script = tmp_path / "reprockpttwoScript.sml"
    script.write_text(TWO_THEOREM_SCRIPT)
    cursor = FileProofCursor(
        script, session=_NoOverwriteSaveStateSession(), checkpoint_dir=tmp_path / "ckpt"
    )
    cursor._reparse_if_changed()
    cursor._base_checkpoint_saved = True
    cursor.SAVESTATE_EVERY = 1

    await cursor._save_context_checkpoint("first_thm")
    first = cursor._checkpoints["first_thm"].context_path
    await cursor._save_context_checkpoint("first_thm")
    second = cursor._checkpoints["first_thm"].context_path

    assert first != second
    assert first.exists() and second.exists()
    assert not cursor.take_notices()


# ---------------------------------------------------------------------------
# A-4 — an edit inside one Resume body discards the whole chain prefix
# ---------------------------------------------------------------------------

MULTI_RESUME_SCRIPT = (
    "open HolKernel Parse boolLib bossLib markerLib;\n"   # 1
    "\n"                                                   # 2
    'val _ = new_theory "reprockptmulti";\n'                # 3
    "\n"                                                   # 4
    "Theorem multi:\n"                                     # 5
    "  p /\\ (p ==> q) ==> p /\\ q\n"                      # 6
    "Proof\n"                                              # 7
    "  strip_tac >> conj_tac\n"                            # 8
    '  >- suspend "r1"\n'                                   # 9
    '  >- suspend "r2"\n'                                   # 10
    "QED\n"                                                # 11
    "\n"                                                   # 12
    "Resume multi[r1]:\n"                                  # 13
    "  first_assum ACCEPT_TAC\n"                           # 14
    "QED\n"                                                # 15
    "\n"                                                   # 16
    "Resume multi[r2]:\n"                                  # 17
    "  RES_TAC\n"                                          # 18
    "QED\n"                                                # 19
    "\n"                                                   # 20
    "val _ = export_theory();\n"                           # 21
)

LAST_RESUME_BODY_IDX = 17     # 0-based index of multi[r2]'s body (line 18)


def test_resume_body_edit_keeps_untouched_chain_prefix(tmp_path: Path):
    """An edit confined to the LAST ``Resume`` body must leave the checkpoints
    of the main proof and the earlier ``Resume`` bodies usable.

    ``multi`` ends at line 12 and ``multi[r1]`` at line 16; the edit is at line
    18. Their captured theory state is untouched, so navigating to
    ``multi[r2]`` should resume from ``multi[r1]``'s checkpoint and replay only
    the edited body — the difference between the field's 4.2s and 182s.
    """
    script = tmp_path / "reprockptmultiScript.sml"
    script.write_text(MULTI_RESUME_SCRIPT)
    cursor = FileProofCursor(script, session=None, checkpoint_dir=tmp_path / "ckpt")
    cursor._reparse_if_changed()
    cursor._needs_session_reinit = False

    for name in ("multi", "multi[r1]"):
        _add_context_checkpoint(cursor, name)
    cursor._loaded_to_line = 16
    cursor._loaded_content_hash = cursor._compute_hash(
        "\n".join(MULTI_RESUME_SCRIPT.split("\n")[:15])
    )

    target = cursor._get_theorem("multi[r2]")
    assert target is not None, "setup: multi[r2] not parsed"
    assert cursor._find_predecessor_checkpoint(target) is not None, \
        "setup: no predecessor checkpoint before the edit"

    lines = MULTI_RESUME_SCRIPT.split("\n")
    assert lines[LAST_RESUME_BODY_IDX] == "  RES_TAC", \
        f"setup: unexpected line {lines[LAST_RESUME_BODY_IDX]!r}"
    lines[LAST_RESUME_BODY_IDX] = "  metis_tac []"
    script.write_text("\n".join(lines))
    assert cursor._reparse_if_changed(), "setup: edit not detected"
    assert not cursor._needs_session_reinit, \
        "setup: healthy chain must not force a session reinit"

    target = cursor._get_theorem("multi[r2]")
    pred = cursor._find_predecessor_checkpoint(target)
    assert pred is not None, (
        "after editing multi[r2]'s body the predecessor lookup for multi[r2] "
        "misses: the checkpoints of multi (ends line 12) and multi[r1] (ends "
        "line 16) were both rejected, so replay restarts from dependencies "
        f"(entries still present: {sorted(cursor._checkpoints)})"
    )


# ---------------------------------------------------------------------------
# Finding #14 — the documented per-theorem budget is not on the live path
# ---------------------------------------------------------------------------

SLOW_PREFIX_SCRIPT = (
    "open HolKernel Parse boolLib bossLib;\n"        # 1
    "\n"                                             # 2
    'val _ = new_theory "reprockptslow";\n'           # 3
    "\n"                                             # 4
    "Theorem slow_thm:\n"                            # 5
    "  !x:num. x = x\n"                              # 6
    "Proof\n"                                        # 7
    "  loops_forever_tac\n"                          # 8
    "QED\n"                                          # 9
    "\n"                                             # 10
    "Theorem later_thm:\n"                           # 11
    "  !y:num. y + 0 = y\n"                          # 12
    "Proof\n"                                        # 13
    "  simp[]\n"                                     # 14
    "QED\n"                                          # 15
    "\n"                                             # 16
    "val _ = export_theory();\n"                     # 17
)


async def _load_over_slow_prefix(tmp_path: Path):
    """Run the live loader over a file whose first theorem times out."""
    script = tmp_path / "reprockptslowScript.sml"
    script.write_text(SLOW_PREFIX_SCRIPT)
    session = _TimeoutSession("loops_forever_tac")
    cursor = FileProofCursor(script, session=session, checkpoint_dir=tmp_path / "ckpt")
    cursor._reparse_if_changed()
    cursor._needs_session_reinit = False

    error = await cursor._load_context_to_line(16)   # past both theorems
    assert _theorem_sends(session, "Theorem slow_thm:"), \
        "setup: the slow theorem was never sent"
    return cursor, session, error


async def test_prefix_theorem_send_honours_per_theorem_budget(tmp_path: Path):
    """A prefix theorem must be given at most the documented per-theorem
    budget, not the caller's whole-navigation timeout."""
    _, session, _ = await _load_over_slow_prefix(tmp_path)

    used = [t for _, t in _theorem_sends(session, "Theorem slow_thm:")]
    assert max(used) <= PER_THEOREM_TIMEOUT, (
        f"prefix theorem slow_thm was sent with timeout={max(used)}s, but the "
        f"documented per-theorem budget is PER_THEOREM_TIMEOUT="
        f"{PER_THEOREM_TIMEOUT}s"
    )


async def test_prefix_theorem_timeout_is_auto_cheated_not_fatal(tmp_path: Path):
    """A slow PREFIX theorem must be cheated and reported, not abort the whole
    navigation.

    The documented behaviour (``_cheat_failed_theorem(thm, "timeout >120s
    loading whole proof")``) keeps the target reachable and names the culprit;
    the live path returns an error blaming "a definition or proof may be
    looping" and never loads ``later_thm``.
    """
    cursor, session, error = await _load_over_slow_prefix(tmp_path)

    assert error is None, (
        "a prefix theorem's timeout aborted the whole navigation instead of "
        f"being auto-cheated: {error}"
    )
    assert "slow_thm" in cursor._failed_proofs, (
        "the timed-out prefix theorem was not recorded in _failed_proofs, so "
        "no report can name it"
    )
    assert "timeout" in cursor._failed_proofs["slow_thm"].lower(), (
        f"recorded reason does not mention the timeout: "
        f"{cursor._failed_proofs['slow_thm']!r}"
    )
    assert _theorem_sends(session, "Theorem later_thm:"), (
        "loading stopped at the slow theorem; later_thm never reached HOL"
    )


# ---------------------------------------------------------------------------
# A-5 — the forced cold replay is never disclosed
# ---------------------------------------------------------------------------

BROKEN_CHAIN_SCRIPT = (
    "open HolKernel Parse boolLib bossLib markerLib;\n"   # 1
    "\n"                                                   # 2
    'val _ = new_theory "reprockptchain";\n'                # 3
    "\n"                                                   # 4
    "Theorem chain:\n"                                     # 5
    "  p /\\ (p ==> q) ==> p /\\ q\n"                      # 6
    "Proof\n"                                              # 7
    "  strip_tac >> conj_tac\n"                            # 8
    '  >- suspend "c1"\n'                                   # 9
    '  >- suspend "c2"\n'                                   # 10
    "QED\n"                                                # 11
    "\n"                                                   # 12
    "Resume chain[c1]:\n"                                  # 13
    "  first_assum ACCEPT_TAC\n"                           # 14
    "QED\n"                                                # 15
    "\n"                                                   # 16
    "Resume chain[c2]:\n"                                  # 17
    "  RES_TAC\n"                                          # 18
    "QED\n"                                                # 19
    "\n"                                                   # 20
    "val _ = export_theory();\n"                           # 21
)

BROKEN_BODY_IDX = 17     # 0-based index of chain[c2]'s body (line 18)
C2_START_LINE = 17       # "Resume chain[c2]:"


def test_broken_chain_edit_keeps_prefix_and_names_the_red_arm(tmp_path: Path):
    """An edit inside a broken chain is an ordinary partial edit: no session
    restart is armed and the prefix before the edited block is kept. The cost
    it does carry — the red arm re-runs on every load until it is green — is
    disclosed by name rather than paid silently.
    """
    script = tmp_path / "reprockptchainScript.sml"
    script.write_text(BROKEN_CHAIN_SCRIPT)
    cursor = FileProofCursor(script, session=None, checkpoint_dir=tmp_path / "ckpt")
    cursor._reparse_if_changed()
    cursor._needs_session_reinit = False

    for name in ("chain", "chain[c1]"):
        _add_context_checkpoint(cursor, name)
    cursor._loaded_to_line = 20
    cursor._loaded_content_hash = cursor._compute_hash(
        "\n".join(BROKEN_CHAIN_SCRIPT.split("\n")[:19])
    )
    # The chain is broken: chain[c2] was auto-cheated on the previous load.
    cursor._failed_proofs = {"chain[c2]": "error: RES_TAC failed"}

    lines = BROKEN_CHAIN_SCRIPT.split("\n")
    assert lines[BROKEN_BODY_IDX] == "  RES_TAC", \
        f"setup: unexpected line {lines[BROKEN_BODY_IDX]!r}"
    lines[BROKEN_BODY_IDX] = "  metis_tac []"
    script.write_text("\n".join(lines))
    assert cursor._reparse_if_changed(), "setup: edit not detected"
    assert not cursor._needs_session_reinit, (
        "a one-line edit inside a broken chain armed a full session restart "
        "plus a replay of the whole prefix from dependencies"
    )

    status = cursor.status
    assert "pending_work" not in status, status["pending_work"]
    assert status["loaded_to_line"] == C2_START_LINE, (
        f"prefix should be kept up to the edited block, got "
        f"loaded_to_line={status['loaded_to_line']}"
    )
    assert {"chain", "chain[c1]"} <= set(cursor._checkpoints), (
        f"checkpoints before the edit discarded: {sorted(cursor._checkpoints)}"
    )
    notices = "\n".join(cursor.take_notices())
    assert "chain[c2]" in notices and "RES_TAC failed" in notices, (
        f"the red arm's cost is not disclosed: {notices!r}"
    )
