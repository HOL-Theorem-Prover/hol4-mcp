"""P4a: navigation past broken earlier Resume blocks.

Investigation outcome (2026-06): the file-order Resume coupling for
navigation is already handled by the existing auto-cheat — a failing
earlier Resume body is re-sent as `Resume name[label]: cheat`, the
suspension closes canonically, and later content stays reachable. P1c
makes that visible ([auto-cheated deps: ...]), so the planned opt-in
skip_broken_resumes flag had no semantic gap left to fill and was NOT
added.

What WAS broken: a Resume whose label does not exist (typo, or recording
suspend never ran) is processed by HOL as a SILENT no-op — no output, no
error, nothing recorded. These are now detected at load (the pre-load
goal extraction fails) and recorded in _failed_proofs as skipped.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_mcp_server import (
    hol_state_at as _hol_state_at,
    hol_stop as _hol_stop,
    _init_file_cursor,
    _sessions,
)

hol_state_at = _hol_state_at
hol_stop = _hol_stop
hol_file_init = _init_file_cursor


TWO_RESUME_FIRST_BROKEN = """\
open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "p4atwores";

Theorem two_res:
  p /\\ (p ==> q) ==> p /\\ q
Proof
  strip_tac >> conj_tac
  >- suspend "p_case"
  >- suspend "q_case"
QED

Resume two_res[p_case]:
  FAIL_TAC "broken first resume"
QED

Resume two_res[q_case]:
  RES_TAC
QED

Finalise two_res

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_second_resume_reachable_past_broken_first(tmp_path):
    """Navigating into the second Resume works although the first Resume's
    body is broken: the broken body is auto-cheated (suspension closed
    canonically) and NAMED in the output with its failure reason."""
    test_file = tmp_path / "p4atworesScript.sml"
    test_file.write_text(TWO_RESUME_FIRST_BROKEN)
    session = "p4a_two_res_test"
    try:
        await hol_file_init(file=str(test_file), session=session)

        # QED of the second Resume: replay must succeed
        r = await hol_state_at(session=session, line=19, col=1)
        assert "two_res[q_case]" in r
        assert "No goals (proof complete)" in r, f"unexpected: {r}"

        # The broken first Resume is named, with the failure reason
        assert "[context admission history (not a dependency list):" in r
        assert "two_res[p_case]" in r
        assert "FAIL_TAC" in r

        cursor = _sessions[session].cursor
        assert "two_res[p_case]" in cursor._failed_proofs
        assert "two_res[q_case]" not in cursor._failed_proofs
    finally:
        await hol_stop(session=session)


UNKNOWN_LABEL_RESUME = """\
open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "p4btypo";

Theorem disp:
  p /\\ (p ==> q) ==> p /\\ q
Proof
  strip_tac >> conj_tac
  >- suspend "p_case"
  >- suspend "q_case"
QED

Resume disp[typo_case]:
  ASM_REWRITE_TAC[]
QED

Theorem after_ok:
  T
Proof
  simp[]
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_unknown_label_resume_recorded_as_skipped(tmp_path):
    """A Resume whose label was never registered is a silent no-op in HOL;
    loading must detect it (pre-load goal extraction fails) and record it
    so outputs can name the skipped block."""
    test_file = tmp_path / "p4btypoScript.sml"
    test_file.write_text(UNKNOWN_LABEL_RESUME)
    session = "p4b_typo_test"
    try:
        await hol_file_init(file=str(test_file), session=session)

        # Content after the typo Resume stays reachable
        r = await hol_state_at(session=session, line=21, col=1)  # after_ok QED
        assert "after_ok" in r
        assert "No goals (proof complete)" in r, f"unexpected: {r}"

        # The skipped Resume is detected and named
        cursor = _sessions[session].cursor
        assert "disp[typo_case]" in cursor._failed_proofs, (
            f"skip not recorded: {dict(cursor._failed_proofs)}"
        )
        assert "SKIPPED" in cursor._failed_proofs["disp[typo_case]"]
        assert "[context admission history (not a dependency list):" in r
        assert "disp[typo_case]" in r
    finally:
        await hol_stop(session=session)
