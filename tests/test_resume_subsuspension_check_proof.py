"""End-to-end: hol_check_proof on a nested-Resume scenario.

Confirms that running hol_check_proof on Resume nested[B] (whose label was
sub-suspended inside Resume nested[A]) works correctly.  The success path
depends on _load_context_to_line (called from execute_proof_traced via
enter_theorem) sending the raw Resume nested[A] block text — which HOL
dispatches through markerLib.resume canonically, registering "B" so the
subsequent goal extraction for nested[B] succeeds.

If file-context loading bypassed canonical processing for Resume blocks,
this test would fail at "Resume 'nested[B]' has no suspension info" /
"No such label" during the goal extraction step.
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


@pytest.mark.asyncio
async def test_check_proof_on_subsuspended_resume(
    hol_session_tmpdir, tmp_path: Path
):
    """execute_proof_traced on Resume nested[B] succeeds because file-context
    loading for nested[A] runs through canonical markerLib.resume."""
    src = (FIXTURES_DIR / "suspendNestedScript.sml").read_text()
    script = tmp_path / "suspendNestedScript.sml"
    script.write_text(src)

    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # 1. Check the body of Resume nested[A] first.  This DOES NOT register
    #    "B" itself (it uses verify_resume_json's set_goalfrag path), but
    #    enter_theorem→_load_context_to_line→_load_remaining_content sends
    #    nested[A]'s text canonically up to here.  After this call, "B" is
    #    registered because the canonical send happened before the check.
    trace_a = await cursor.execute_proof_traced("nested[A]")
    assert trace_a, "Empty trace for Resume nested[A]"
    final_a = trace_a[-1]
    assert final_a.goals_after == 0, (
        f"Resume nested[A] did not close: {final_a!r}"
    )
    assert final_a.error is None, f"Resume nested[A] errored: {final_a.error!r}"

    # 2. Now check Resume nested[B].  For this to work, "B" must be in the
    #    markerLib suspension store: it was registered when nested[A]'s
    #    raw text was sent through HOL's normal parser → markerLib.resume.
    trace_b = await cursor.execute_proof_traced("nested[B]")
    assert trace_b, (
        f"Empty trace for Resume nested[B] — sub-suspension B was probably "
        f"not registered when nested[A]'s body ran."
    )
    final_b = trace_b[-1]
    assert final_b.error is None, (
        f"Resume nested[B] errored: {final_b.error!r}. This usually means "
        f"sub-suspension B was not registered."
    )
    assert final_b.goals_after == 0, (
        f"Resume nested[B] did not close: {final_b!r}"
    )
