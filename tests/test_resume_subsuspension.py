"""Regression tests for the sub-suspension registration bug in Resume processing.

Background
==========

When hol4-mcp's file-replay path processes ``Resume thm[label]: tacs QED``, it
must record any sub-``suspend "X"`` calls inside ``tacs`` as resumption deltas
in the markerLib suspension store.  Without that recording, downstream
``Resume thm[X]:`` blocks fail to look up the saved goal: navigation reports
"No such label" and the user cannot iterate on those sub-bodies.

Holmake's canonical Resume processing (``markerLib.resume``) does the recording.
hol4-mcp's older path (``proofManagerLib.set_goalfrag`` + ``verify_core``) does
not.  These tests pin the canonical behaviour so the regression cannot return
silently.

Files
=====

- ``tests/fixtures/suspendNestedScript.sml`` — Theorem with one suspension
  ``"A"``; ``Resume A`` body issues sub-``suspend "B"``; ``Resume B`` closes.

Tests
=====

1. ``test_marker_resume_registers_subsuspensions`` — direct SML test: after
   ``markerLib.resume`` runs the ``Resume A`` body, ``lookup_resumption "B"``
   returns a non-empty list.  Demonstrates the canonical lifecycle.

2. ``test_proof_manager_path_does_not_register`` — direct SML test:
   ``proofManagerLib.set_goalfrag`` + ``proofManagerLib.expand`` on the same
   tactics leaves ``lookup_resumption "B"`` empty.  Demonstrates the bug class.

3. ``test_verify_all_proofs_processes_nested_resume`` — end-to-end via
   ``FileProofCursor.verify_all_proofs`` against the nested fixture.  Asserts
   that ``Resume nested[B]`` verifies (goals_after == 0, no error) — which can
   only happen if processing ``Resume nested[A]`` previously registered "B".
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp.hol_session import HOLSession


SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"
FIXTURES_DIR = Path(__file__).parent / "fixtures"


@pytest.fixture
async def hol_session_tmpdir(tmp_path):
    session = HOLSession(str(tmp_path))
    await session.start()
    await session.send(
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30
    )
    yield session
    await session.stop()


async def _stash_parent_with_suspend_A(session: HOLSession) -> None:
    """Define a tiny parent theorem that suspends label "A". Resets first."""
    await session.send("proofManagerLib.drop_all();", timeout=5)
    out = await session.send(
        'val nested = Q.store_thm("nested", '
        '`p /\\ p ==> p /\\ p`, '
        'markerLib.suspend "A");',
        timeout=15,
    )
    assert "Stashing suspended theorem nested" in out, (
        f"Parent theorem did not stash suspension: {out[-500:]!r}"
    )


@pytest.mark.asyncio
async def test_marker_resume_registers_subsuspensions(hol_session_tmpdir):
    """markerLib.resume (canonical path) records sub-``suspend "B"`` deltas.

    The Resume A body sub-suspends "B".  After processing via markerLib.resume,
    ``lookup_resumption ... label="B"`` must return a non-empty list.
    """
    await _stash_parent_with_suspend_A(hol_session_tmpdir)
    out = await hol_session_tmpdir.send(
        'val _ = markerLib.resume {suspension_name="nested", label_name="A"} '
        '  (strip_tac >> conj_tac >- markerLib.suspend "B" >- first_assum ACCEPT_TAC)'
        '  (Context.snapshot());'
        ' val pt_nested = #1 (valOf (markerLib.lookup_suspension "nested"));'
        ' val b_resumptions = markerLib.lookup_resumption '
        '   {parent_thy=pt_nested, parent_name="nested", label="B"};'
        ' print ("B_REG=" ^ Int.toString (length b_resumptions) ^ "\\n");',
        timeout=30,
    )
    assert "B_REG=1" in out, (
        "Canonical markerLib.resume failed to register sub-suspension B. "
        f"Output: {out[-800:]!r}"
    )


@pytest.mark.asyncio
async def test_proof_manager_path_does_not_register(hol_session_tmpdir):
    """proofManagerLib.set_goalfrag + e()/ef() does NOT register sub-suspensions.

    This pins the BUG class — it's why ``verify_resume_json`` must NOT be used
    for file replay where downstream Resume blocks may need the sub-suspension.
    """
    await _stash_parent_with_suspend_A(hol_session_tmpdir)
    out = await hol_session_tmpdir.send(
        'val (pt_nested, th) = valOf (markerLib.lookup_suspension "nested");'
        ' val (asms, concl) = markerLib.resumption_to_goal '
        '   (markerLib.extract_suspended_goal [th] "A");'
        ' val _ = proofManagerLib.set_goalfrag (asms, concl);'
        ' val _ = proofManagerLib.expand '
        '   (strip_tac >> conj_tac >- markerLib.suspend "B" >- first_assum ACCEPT_TAC);'
        ' val b_resumptions = markerLib.lookup_resumption '
        '   {parent_thy=pt_nested, parent_name="nested", label="B"};'
        ' print ("B_REG=" ^ Int.toString (length b_resumptions) ^ "\\n");',
        timeout=30,
    )
    assert "B_REG=0" in out, (
        "Sanity check failed: set_goalfrag path unexpectedly registered "
        f"sub-suspension B. Output: {out[-800:]!r}"
    )


@pytest.mark.asyncio
async def test_run_resume_canonical_json_registers_subsuspensions(hol_session_tmpdir):
    """The new SML helper ``run_resume_canonical_json`` routes through
    ``markerLib.resume``, so the sub-suspension lifecycle matches Holmake."""
    await _stash_parent_with_suspend_A(hol_session_tmpdir)
    out = await hol_session_tmpdir.send(
        'run_resume_canonical_json "nested" "A" "nested_A_proof" '
        '["strip_tac >> conj_tac >- markerLib.suspend \\"B\\" '
        '>- first_assum ACCEPT_TAC"] false 30.0;'
        ' val pt_nested = #1 (valOf (markerLib.lookup_suspension "nested"));'
        ' val b_resumptions = markerLib.lookup_resumption '
        '   {parent_thy=pt_nested, parent_name="nested", label="B"};'
        ' print ("B_REG=" ^ Int.toString (length b_resumptions) ^ "\\n");',
        timeout=30,
    )
    assert "B_REG=1" in out, (
        "run_resume_canonical_json failed to register sub-suspension B. "
        f"Output: {out[-800:]!r}"
    )


@pytest.mark.asyncio
async def test_verify_all_proofs_processes_nested_resume(
    hol_session_tmpdir, tmp_path: Path
):
    """End-to-end: verify_all_proofs on the nested-suspension fixture.

    Pre-condition for this to pass: file replay records the sub-suspension "B"
    when it processes Resume nested[A].  If file replay used the
    set_goalfrag/verify_core path, processing Resume nested[B] would fail
    because "B" isn't registered, leaving its trace empty or errored.
    """
    src = (FIXTURES_DIR / "suspendNestedScript.sml").read_text()
    script = tmp_path / "suspendNestedScript.sml"
    script.write_text(src)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    results = await cursor.verify_all_proofs()

    # The fixture has: Theorem nested, Resume nested[A], Resume nested[B].
    # All three names must appear and the Resume blocks must verify.
    assert "nested" in results, f"Missing parent theorem in results: {list(results)!r}"
    assert "nested[A]" in results, (
        f"Missing Resume nested[A] in results: {list(results)!r}"
    )
    assert "nested[B]" in results, (
        f"Missing Resume nested[B] in results: {list(results)!r}.  This is the "
        "primary symptom of the bug: Resume nested[B] cannot be processed "
        "because sub-suspension B was never registered when nested[A] ran."
    )

    trace_b = results["nested[B]"]
    assert trace_b, f"Empty trace for Resume nested[B]: {results['nested[B]']!r}"
    final_b = trace_b[-1]
    assert final_b.goals_after == 0, (
        f"Resume nested[B] did not close: {final_b!r}"
    )
    assert final_b.error is None, (
        f"Resume nested[B] errored: {final_b.error!r}"
    )
