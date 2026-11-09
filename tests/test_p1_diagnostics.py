"""P1 diagnostics in existing outputs.

P1c: auto-cheated deps are named (with reasons) in hol_state_at /
     hol_check_proof outputs.
P1b: a target strictly inside an opaque multi-line step gets an explicit
     chain-entry landing NOTE.
P1d: a per-tactic timeout is attributed to its source line span.
P1a: a Resume whose suspension label is missing gets an ancestor-chain
     diagnosis naming the first broken ancestor.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import StateAtResult
from hol4_mcp.hol_mcp_server import (
    hol_state_at as _hol_state_at,
    hol_check_proof as _hol_check_proof,
    hol_stop as _hol_stop,
    _init_file_cursor,
    _sessions,
)

hol_state_at = _hol_state_at
hol_check_proof = _hol_check_proof
hol_stop = _hol_stop
hol_file_init = _init_file_cursor


# Broken theorem followed by a theorem that uses it: loading auto-cheats
# fail_dep, so anything verified after rests on its STATEMENT only.
FAIL_DEP_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "p1cfail";

Theorem fail_dep:
  T /\\ T
Proof
  FAIL_TAC "nope"
QED

Theorem uses_dep:
  T /\\ T
Proof
  ACCEPT_TAC fail_dep
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_auto_cheated_deps_named(tmp_path):
    """P1c: outputs name auto-cheated deps and why they were cheated."""
    test_file = tmp_path / "p1cfailScript.sml"
    test_file.write_text(FAIL_DEP_SCRIPT)
    session = "p1c_deps_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # state_at at uses_dep's QED loads (and auto-cheats) fail_dep.
        r = await hol_state_at(session=session, line=15, col=1)
        assert "[context admission history (not a dependency list):" in r, r
        assert "fail_dep" in r
        assert "error" in r  # the recorded reason

        # Reason is recorded on the cursor.
        cursor = _sessions[session].cursor
        assert "fail_dep" in cursor._failed_proofs
        assert cursor._failed_proofs["fail_dep"].startswith(
            ("error", "timeout")
        )

        # check_proof on the dependent theorem: ⚠ marker plus the dep list.
        r = await hol_check_proof(theorem="uses_dep", session=session)
        assert "Status: OK" in r
        assert "⚠ depends on cheat" in r, f"oracle marker missing: {r}"
        assert "[context admission history (not a dependency list):" in r
        assert "fail_dep" in r
    finally:
        await hol_stop(session=session)


# A two-step proof whose second step (simp with a multi-line argument list)
# spans two source lines — one opaque step the replay cannot enter.
MULTILINE_STEP_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "p1binside";

Theorem multiline_simp:
  !a b. a /\\ b ==> b /\\ a
Proof
  rpt strip_tac >>
  simp[boolTheory.CONJ_COMM,
       boolTheory.AND_CLAUSES]
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_inside_opaque_step_note(tmp_path):
    """P1b: targeting a line strictly inside a multi-line opaque step gets an
    explicit chain-entry landing NOTE (the state shown is the step's ENTRY)."""
    test_file = tmp_path / "p1binsideScript.sml"
    test_file.write_text(MULTILINE_STEP_SCRIPT)
    session = "p1b_note_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # Line 10 is the second line of simp's argument list — strictly
        # inside the simp step (lines 9-10).
        r = await hol_state_at(session=session, line=10, col=8)
        assert "NOTE: target line 10 is INSIDE step" in r, f"NOTE missing: {r}"
        assert "ENTRY" in r
        assert ">- suspend" in r

        # A step-boundary target (start of simp, line 9 col 3) gets no NOTE.
        r = await hol_state_at(session=session, line=9, col=3)
        assert "NOTE: target line" not in r
    finally:
        await hol_stop(session=session)


# A proof with a deliberately slow middle tactic (interruptible sleep).
SLOW_STEP_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "p1dslow";

fun sleep_tac g = (OS.Process.sleep (Time.fromSeconds 5); ALL_TAC g);

Theorem slow_thm:
  T /\\ T
Proof
  conj_tac >>
  sleep_tac >>
  simp[]
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_timeout_attribution_check_proof(tmp_path):
    """P1d: a per-tactic timeout in hol_check_proof names the step's source
    line span with shrink-the-lump advice."""
    test_file = tmp_path / "p1dslowScript.sml"
    test_file.write_text(SLOW_STEP_SCRIPT)
    session = "p1d_timeout_test"

    try:
        await hol_file_init(file=str(test_file), session=session)
        _sessions[session].cursor._tactic_timeout = 2.0

        r = await hol_check_proof(theorem="slow_thm", session=session)
        assert "Status: FAILED" in r, f"expected FAILED: {r}"
        assert "TIMEOUT: step 2 spans line" in r, f"attribution missing: {r}"
        assert ">- suspend" in r
    finally:
        await hol_stop(session=session)


@pytest.mark.asyncio
async def test_timeout_attribution_state_at(tmp_path):
    """P1d: a replay timeout in hol_state_at names the failing step span.

    The replay path only reports a timeout after a >=30s batch send fails,
    so the cursor's state_at is stubbed with a crafted timed-out result;
    the theorem, step plan, and line math stay real.
    """
    test_file = tmp_path / "p1binsideScript.sml"
    test_file.write_text(MULTILINE_STEP_SCRIPT)
    session = "p1d_state_at_test"

    try:
        await hol_file_init(file=str(test_file), session=session)
        cursor = _sessions[session].cursor

        # Establish a real step plan / active theorem first.
        await hol_state_at(session=session, line=9, col=3)

        async def timed_out_state_at(line, col=1, skip_prefix=False):
            return StateAtResult(
                goals=[], tactic_idx=2, tactics_replayed=1, tactics_total=2,
                file_hash=cursor._content_hash,
                error="Tactic replay timed out (>2s)", timings={},
            )

        cursor.state_at = timed_out_state_at
        r = await hol_state_at(session=session, line=11, col=1)
        assert "PROOF BROKEN" in r
        assert "TIMEOUT: step 1" in r, f"attribution missing: {r}"
        assert ">- suspend" in r
    finally:
        await hol_stop(session=session)


# Dispatcher fails BEFORE its suspend runs: the suspension labels are never
# registered, so the Resume block below cannot find its label.
BROKEN_DISPATCHER_SCRIPT = """\
open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "p1abroken";

Theorem broken_dispatch:
  p /\\ (p ==> q) ==> p /\\ q
Proof
  strip_tac >>
  FAIL_TAC "broken before suspend" >>
  conj_tac
  >- suspend "p_case"
  >- suspend "q_case"
QED

Resume broken_dispatch[p_case]:
  ASM_REWRITE_TAC[]
QED

Finalise broken_dispatch

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_lost_suspension_ancestor_diagnosis(tmp_path):
    """P1a: a Resume whose label is missing reports the ancestor chain and
    the first broken ancestor (known-broken via _failed_proofs, or found by
    replaying the chain)."""
    test_file = tmp_path / "p1abrokenScript.sml"
    test_file.write_text(BROKEN_DISPATCHER_SCRIPT)
    session = "p1a_diag_test"

    try:
        await hol_file_init(file=str(test_file), session=session)

        # state_at inside the Resume body: setup fails (no label), and the
        # diagnosis names the auto-cheated dispatcher.
        r = await hol_state_at(session=session, line=17, col=3)
        assert "Ancestor chain for suspension 'broken_dispatch'" in r, (
            f"diagnosis missing: {r}"
        )
        assert "context admission history" in r
        assert "first broken ancestor" in r
        assert "broken_dispatch" in r

        # check_proof on the Resume reports CANNOT CHECK with the same chain.
        r = await hol_check_proof(
            theorem="broken_dispatch[p_case]", session=session
        )
        assert "Status: CANNOT CHECK" in r, f"unexpected status: {r}"
        assert "Ancestor chain" in r

        # With no known-broken ancestor recorded, the diagnosis replays the
        # chain and pins the failing step.
        cursor = _sessions[session].cursor
        cursor._failed_proofs.clear()
        diag = await cursor.diagnose_resume_failure("broken_dispatch[p_case]")
        assert diag is not None
        assert "first broken ancestor: Theorem broken_dispatch" in diag
        assert "step" in diag
    finally:
        await hol_stop(session=session)
