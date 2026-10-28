"""Regression tests for caller-facing reporting/classification bugs.

Each test asserts the CORRECT behaviour; they were written red under
``xfail(strict=True)`` and the markers came off when the fixes landed.

Covered findings (``MCP_BUGS_review.md``):

  #1  ``hol_goals`` drops the navigation error of a broken replay and prints
      the failure-point goals as a clean ``N goal(s) (at line L)``.
  #3  ``hol_check_proof``'s Definition fallback tests ``not result.goals``
      before ``result.error``, so a TIMEOUT reports ``Status: OK``.
  #13 ``_NavResult.actual_replayed`` is the target position, not the number of
      commands issued (the ``reused`` strategy issues none).
  #15 ``show_partial`` is declared and documented by ``hol_state_at`` but the
      body never reads it.
  #16 ``status`` reports ``stale: True`` after a checkpoint load, because the
      restore stores the checkpoint's FULL-file hash in ``_loaded_content_hash``
      while ``_check_stale_state`` hashes only the loaded PREFIX.
"""

import ast
import inspect
import re
import textwrap
from pathlib import Path

import pytest

from hol4_mcp import hol_mcp_server as server
from hol4_mcp.hol_mcp_server import (
    hol_check_proof,
    hol_goals,
    hol_state_at,
    hol_stop,
)
from hol4_mcp.hol_cursor import (
    FileProofCursor,
    StateAtResult,
    TheoremCheckpoint,
    _NavResult,
    _TargetInfo,
)
from hol4_mcp.hol_file_parser import TheoremInfo


# ---------------------------------------------------------------------------
# Finding #1 — hol_goals hides a broken replay
# ---------------------------------------------------------------------------

BROKEN_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "reprorepbroken";

Theorem repro_broken:
  !x:num. x = x
Proof
  strip_tac
  >> EQ_TAC
  >> simp[]
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_hol_goals_reports_broken_replay(tmp_path):
    """``hol_goals(line=L)`` must not report a clean goal count for a position
    the replay never reached.

    ``EQ_TAC`` raises on the numeric goal ``x = x``, so replay stops at step 1
    of 3 with one goal on the stack. ``hol_state_at`` classifies that as
    PROOF BROKEN; ``hol_goals`` at the very same line, same file, no edit in
    between, prints ``1 goal(s) (at line 11, goal 1 = top)``.
    """
    script = tmp_path / "reprorepbrokenScript.sml"
    script.write_text(BROKEN_SCRIPT)
    qed_line = BROKEN_SCRIPT.split("\n").index("QED") + 1
    session = "repro_reporting_goals_broken"

    try:
        at = await hol_state_at(
            file=str(script), line=qed_line, session=session, max_output=4000
        )
        # Sanity: the navigation really is broken at this position.
        assert "PROOF BROKEN" in at, f"setup: expected a broken replay, got:\n{at}"

        goals = await hol_goals(file=str(script), line=qed_line, session=session)
        assert goals.startswith("ERROR") or "BROKEN" in goals, (
            "hol_goals presented the goals at the point replay STOPPED as the "
            f"goals at line {qed_line}, with no sign that the replay failed:\n"
            f"{goals}"
        )
    finally:
        await hol_stop(session=session)


# ---------------------------------------------------------------------------
# Finding #3 — Definition fallback reports OK on a timeout
# ---------------------------------------------------------------------------

class _StubCursor:
    """Minimal cursor standing in for the Definition path of hol_check_proof."""

    def __init__(self, thm: TheoremInfo):
        self.file = Path("/nonexistent/reproreportingScript.sml")
        self._thm = thm
        self._step_plan = []
        self._failed_proofs = {}

    def _reparse_if_changed(self):
        return False

    async def enter_theorem(self, name):
        return {}

    def _get_theorem(self, name):
        return self._thm if name == self._thm.name else None

    async def execute_proof_traced(self, name):
        return []          # Definition blocks always take the fallback path


@pytest.mark.asyncio
async def test_check_proof_definition_fallback_rejects_timeout(monkeypatch):
    """A termination proof that TIMED OUT was not validated and must not be
    reported OK.

    ``_state_at_bounded``'s overall-budget timeout returns ``goals=[]`` with the
    TIMEOUT text in ``error``; the fallback's empty-goals test fires first.
    """
    thm = TheoremInfo(
        name="repro_def",
        kind="Definition",
        goal="repro_def n = n",
        start_line=5,
        proof_start_line=7,
        proof_end_line=10,
        has_cheat=False,
        proof_body="WF_REL_TAC `measure I`",
        proof_body_offset=0,
    )
    cursor = _StubCursor(thm)

    async def fake_get_cursor(name):
        return cursor

    async def fake_state_at_bounded(cur, line, col=1, **kwargs):
        return StateAtResult(
            goals=[],
            tactic_idx=0,
            tactics_replayed=0,
            tactics_total=0,
            file_hash="",
            error="TIMEOUT: state_at exceeded its overall 300s budget and was aborted",
        )

    monkeypatch.setattr(server, "_get_cursor", fake_get_cursor)
    monkeypatch.setattr(server, "_state_at_bounded", fake_state_at_bounded)

    out = await hol_check_proof(theorem="repro_def", session="repro_reporting_def")

    assert "Status: OK" not in out, (
        "a timed-out termination proof was reported as verified:\n" + out
    )
    assert "TIMEOUT" in out, f"the timeout was not reported at all:\n{out}"


# ---------------------------------------------------------------------------
# Finding #13 — replayed=N/M is a position, not a cost
# ---------------------------------------------------------------------------

@pytest.mark.asyncio
async def test_nav_result_replayed_counts_commands_issued(tmp_path):
    """``_NavResult.actual_replayed`` (rendered as ``replayed=N/M``) must count
    work done, not the position reached.

    The ``reused`` strategy returns the live goal without issuing a single
    ``e()``; it still claims ``target.tactic_idx`` tactics replayed. A fix that
    renames the field to a position also satisfies this test (nothing named
    ``actual_replayed`` remains).
    """
    script = tmp_path / "reproreusedScript.sml"
    script.write_text("open HolKernel;\nval _ = new_theory \"reproreused\";\n")
    cursor = FileProofCursor(script, session=None)

    async def reuse_succeeds(tactic_idx):
        return True

    cursor._try_reuse_state = reuse_succeeds

    target = _TargetInfo(
        thm=None,
        tactic_idx=7,
        total_tactics=9,
        incremental_update=None,
        changed=False,
    )
    nav: _NavResult = await cursor._navigate_to_target(target)

    assert nav.strategy == "reused", f"setup: wrong strategy {nav.strategy}"
    assert getattr(nav, "actual_replayed", 0) == 0, (
        f"reused navigation issued no commands but reports "
        f"actual_replayed={nav.actual_replayed} (the target position)"
    )


# ---------------------------------------------------------------------------
# Finding #15 — show_partial is accepted, documented, and unused
# ---------------------------------------------------------------------------

def _executable_body(fn) -> list[ast.AST]:
    """AST of a function's body with the docstring removed."""
    tree = ast.parse(textwrap.dedent(inspect.getsource(fn)))
    fdef = tree.body[0]
    body = list(fdef.body)
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        body = body[1:]
    return body


def test_state_at_show_partial_is_wired():
    """A parameter the docstring gives semantics to must be read by the body.

    Removing the parameter is the other acceptable fix, so its absence from the
    signature also passes.
    """
    params = inspect.signature(hol_state_at).parameters
    if "show_partial" not in params:
        return  # fixed by removal

    used = any(
        isinstance(node, ast.Name) and node.id == "show_partial"
        for stmt in _executable_body(hol_state_at)
        for node in ast.walk(stmt)
    )
    assert used, (
        "hol_state_at accepts and documents show_partial but never reads it; "
        "the documented refusal-to-show-goals semantics does not exist"
    )


# ---------------------------------------------------------------------------
# Finding #16 — stale: True after a checkpoint load
# ---------------------------------------------------------------------------

TWO_THEOREM_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "reprorepstale";

Theorem repro_first:
  !x:num. x = x
Proof
  simp[]
QED

Theorem repro_second:
  !y:num. y + 0 = y
Proof
  simp[]
QED

val _ = export_theory();
"""


class _QuietSession:
    """HOL session stub emulating the Poly/ML SaveState calls: a hierarchy
    depth for ``showHierarchy`` and a real file for ``saveChild``."""

    async def send(self, command, timeout=None):
        if "length (PolyML.SaveState.showHierarchy" in command:
            return "> val it = 3 : int"
        if "showHierarchy" in command:
            return '> val it = ["state0", "heap", "base"] : string list'
        m = re.search(r'saveChild\s*\("([^"]+)"', command)
        if m:
            Path(m.group(1)).write_text("stub checkpoint")
        return "> val it = () : unit"


@pytest.mark.asyncio
async def test_status_not_stale_after_context_checkpoint_load(tmp_path):
    """Saving a context checkpoint and restoring it, with no edit in between,
    leaves the session in sync, so ``cursor.status['stale']`` must be False.

    The checkpoint is written by the real save path, so what it stamps and what
    ``_check_stale_state`` recomputes have to be the same kind of hash.
    """
    script = tmp_path / "reprorepstaleScript.sml"
    script.write_text(TWO_THEOREM_SCRIPT)

    cursor = FileProofCursor(
        script, session=_QuietSession(), checkpoint_dir=tmp_path / "ckpt"
    )
    cursor._reparse_if_changed()
    assert cursor._get_theorem("repro_first"), "setup: theorem not parsed"

    cursor._base_checkpoint_saved = True
    await cursor._save_context_checkpoint("repro_first")
    assert "repro_first" in cursor._checkpoints, "setup: checkpoint not saved"

    loaded = await cursor._load_context_checkpoint("repro_first")
    assert loaded, "setup: checkpoint restore failed"

    status = cursor.status
    assert status["stale"] is False, (
        "status reports a synchronized session as stale after a checkpoint "
        f"load (loaded_to_line={status['loaded_to_line']})"
    )
