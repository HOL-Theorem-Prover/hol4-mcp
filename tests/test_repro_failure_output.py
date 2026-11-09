"""Failure output tells the truth first: an opaque break names the step and
the sub-suspend recipe before anything else and withholds the entry goal; a
TIMEOUT attributes its budget to prefix vs target; an absurd timeout is
refused; a cheat-dependent state is flagged on line one; an undeclared name
in hol_send points at the parked position; a repeated break at one step is
called out as a loop."""
import re

import pytest

from hol4_mcp.hol_mcp_server import (
    MAX_STATE_AT_TIMEOUT,
    _init_file_cursor,
    hol_check_proof,
    hol_goals,
    hol_send,
    hol_state_at,
    hol_stop,
)

OPAQUE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "opq";

Theorem opaque_fail:
  !x:num. x + 0 = x
Proof
  gen_tac >>
  (Induct_on `x` >>
   FAIL_TAC "inside")
QED

Theorem later_thm:
  T
Proof
  simp []
QED

val _ = export_theory();
"""
OPAQUE_QED_LINE = 11
OPAQUE_SPAN = "lines 9-10"

FAIL_DEP_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "fdep";

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

SLEEP_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "slp";

Theorem quick:
  T
Proof
  simp []
QED

Theorem sleeper:
  T
Proof
  (fn g => (OS.Process.sleep (Time.fromSeconds 20); ALL_TAC g)) >>
  simp []
QED

val _ = export_theory();
"""


async def init(tmp_path, name, script, session):
    f = tmp_path / f"{name}Script.sml"
    f.write_text(script)
    r = await _init_file_cursor(file=str(f), session=session)
    assert "Theorems:" in r, r
    return f


def body(output):
    """Output lines after the `Theorem:` header."""
    lines = output.split("\n")
    assert lines[0].startswith("Theorem:"), output
    return lines[1:]


async def test_opaque_break_names_step_first_and_withholds_goal(tmp_path):
    session = "fo_opaque"
    try:
        await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        r = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session)
        first = body(r)[0]
        assert first.startswith("PROOF BROKEN"), r
        m = re.search(r"opaque step (\d+) \(" + OPAQUE_SPAN + r"\)", first)
        assert m and "suspend" in first, r
        assert "=== Goal" not in r, r

        r2 = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session,
                                show_partial=True)
        assert body(r2)[0].startswith("PROOF BROKEN"), r2
        assert "=== Goal" in r2 and "entering the opaque step" in r2, r2
    finally:
        await hol_stop(session)


async def test_timeout_attributes_prefix_and_target(tmp_path):
    session = "fo_timeout"
    try:
        f = await init(tmp_path, "slp", SLEEP_SCRIPT, session)
        r = await hol_state_at(line=15, col=3, session=session, timeout=8)
        assert r.startswith("ERROR: TIMEOUT") or "TIMEOUT" in r.split("\n")[0], r
        m = re.search(r"prefix=(\d+(?:\.\d+)?)s.*target=(\d+(?:\.\d+)?)s", r)
        assert m, r
        prefix, target = float(m.group(1)), float(m.group(2))
        assert target >= 0.5 and prefix < target, r
        assert "YOUR tactics" in r, r
    finally:
        await hol_stop(session)


async def test_absurd_timeout_is_refused(tmp_path):
    session = "fo_absurd"
    try:
        await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        too_big = 2 * MAX_STATE_AT_TIMEOUT
        r = await hol_state_at(line=16, col=3, session=session, timeout=too_big)
        assert r.startswith("ERROR"), r
        assert f"{too_big:g}" in r and f"{MAX_STATE_AT_TIMEOUT:.0f}" in r, r
        assert "seconds" in r, r
    finally:
        await hol_stop(session)


async def test_admission_history_marked_on_first_line_and_use_in_verdict(tmp_path):
    session = "fo_cheat"
    try:
        await init(tmp_path, "fdep", FAIL_DEP_SCRIPT, session)
        r = await hol_state_at(line=15, col=1, session=session)
        assert "⚠ context has admission history" in r.split("\n")[0], r
        assert "[context admission history (not a dependency list):" in r, r

        r2 = await hol_check_proof(theorem="uses_dep", session=session)
        assert "⚠ context has admission history" in r2.split("\n")[0], r2
        assert "⚠ depends on cheat" in r2 and "kernel oracle evidence" in r2, r2
    finally:
        await hol_stop(session)


async def test_hol_send_undeclared_name_points_at_parked_position(tmp_path):
    session = "fo_send"
    try:
        f = await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        await hol_state_at(line=8, col=3, session=session)   # parked in opaque_fail
        r = await hol_send(command="later_thm;", session=session)
        assert "has not been declared" in r, r
        assert "later_thm" in r and "line 13" in r and "opaque_fail" in r, r
        assert "hol_state_at" in r, r
        # later_thm is the file's last block: no later proof admits it.
        assert "last block" in r and 'hol_check_proof(theorem="later_thm")' in r, r
        assert "line 17" not in r, r   # the line after QED is not a position
    finally:
        await hol_stop(session)


TRIO_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "trio";

Theorem first_thm:
  T
Proof
  simp []
QED

Theorem second_thm:
  T
Proof
  simp []
QED

Theorem third_thm:
  T
Proof
  simp []
QED

val _ = export_theory();
"""


async def test_hol_send_undeclared_name_routes_into_the_next_proof(tmp_path):
    session = "fo_send_next"
    try:
        await init(tmp_path, "trio", TRIO_SCRIPT, session)
        await hol_state_at(line=8, col=3, session=session)   # parked in first_thm
        r = await hol_send(command="second_thm;", session=session)
        assert "has not been declared" in r, r
        # The route is INTO third_thm's proof body (line 20), not the line
        # after second_thm's QED.
        assert "third_thm" in r and "hol_state_at(line=20)" in r, r
    finally:
        await hol_stop(session)


STATIC_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "stat";

Theorem static_fail:
  !x:num. x + 0 = x
Proof
  gen_tac >>
  (simp [] >>
   mp_tac undeclared_thm_xyz)
QED

val _ = export_theory();
"""


async def test_static_sml_error_is_not_an_opaque_proof_failure(tmp_path):
    session = "fo_static"
    try:
        await init(tmp_path, "stat", STATIC_SCRIPT, session)
        r = await hol_state_at(line=11, col=1, session=session)
        assert "PROOF BROKEN" in r, r
        assert "does not compile" in r and "undeclared_thm_xyz" in r, r
        assert "has not been declared" in r, r
        assert "`>- suspend" not in r and "Use Suspend/Resume" not in r, r
    finally:
        await hol_stop(session)


TERMINATION_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "term";

Definition count_def:
  count (n:num) = if n = 0 then 0 else count (n - 1)
Termination
  Q.EXISTS_TAC `measure I` >>
  (conj_tac >>
   FAIL_TAC "inside")
End

val _ = export_theory();
"""

SUSPENDED_TERMINATION_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "susterm";

Definition count_def:
  count (n:num) = if n = 0 then 0 else count (n - 1)
Termination
  WF_REL_TAC `measure I`
  >- suspend "Dec"
End

Resume count_def[Dec]:
  cheat
QED

Finalise count_def;

Theorem after_count:
  T
Proof
  simp []
QED

val _ = export_theory();
"""


async def test_opaque_break_in_termination_proof_does_not_prescribe_suspend(tmp_path):
    session = "fo_term"
    try:
        await init(tmp_path, "term", TERMINATION_SCRIPT, session)
        r = await hol_state_at(line=11, col=1, session=session)   # End line
        first = body(r)[0]
        assert first.startswith("PROOF BROKEN in opaque step"), r
        assert "Termination proof" in first, r
        assert "hol_send" in r and "cannot be sub-suspended" in r, r
        assert "`>- suspend" not in r and "Use Suspend/Resume" not in r, r
    finally:
        await hol_stop(session)


async def test_suspend_inside_termination_leaves_the_definition_unsaved(tmp_path):
    session = "fo_susterm"
    try:
        await init(tmp_path, "susterm", SUSPENDED_TERMINATION_SCRIPT, session)
        r = await hol_state_at(line=22, col=3, session=session)   # inside after_count
        assert "count_def" in r and ("failed" in r or "prefix errors" in r), r
    finally:
        await hol_stop(session)


PREFIX_ERROR_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "pfx";

Definition bad_def:
  bad (n:num) = if n = 0 then 0 else bad (n + 1)
End

Theorem after_bad:
  T
Proof
  simp []
QED

val _ = export_theory();
"""


async def test_failed_top_level_definition_is_reported_as_prefix_error(tmp_path):
    session = "fo_prefix_error"
    try:
        f = await init(tmp_path, "pfx", PREFIX_ERROR_SCRIPT, session)
        r = await hol_state_at(line=12, col=3, session=session)
        # The span is the whole pre-theorem chunk that was sent, and the
        # raise ended it: bad_def and anything after it in the span did not run.
        assert "[prefix errors" in r and "lines 1-8" in r and "bad_def" in r, r
        assert "rest of its span did not run" in r, r
        assert "PROOF BROKEN" not in r, r
        # Fixing the span clears the report on the next navigation.
        f.write_text(PREFIX_ERROR_SCRIPT.replace("bad (n + 1)", "bad (n - 1)"))
        r = await hol_state_at(line=12, col=3, session=session)
        assert "[prefix errors" not in r, r
    finally:
        await hol_stop(session)


TIMEOUT_WORD_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "tword";

Theorem mentions_timeout:
  T
Proof
  FAIL_TAC "Rtimeout_error is a constructor, not a timeout"
QED

val _ = export_theory();
"""


async def test_hol_goals_navigation_carries_the_timing_footer(tmp_path):
    session = "fo_goals_timing"
    try:
        f = await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        r = await hol_goals(file=str(f), line=8, col=3, session=session)
        assert "goal(s)" in r, r
        assert "[Timing: total=" in r and "[Cache: pos_before=" in r, r
    finally:
        await hol_stop(session)


async def test_check_proof_labels_a_timeout_only_for_a_timeout(tmp_path):
    session = "fo_tword"
    try:
        await init(tmp_path, "tword", TIMEOUT_WORD_SCRIPT, session)
        r = await hol_check_proof(theorem="mentions_timeout", session=session)
        assert "Status: FAILED" in r, r
        assert "TIMEOUT: step" not in r and "LOOPING tactic" not in r, r
    finally:
        await hol_stop(session)


async def test_repeated_break_at_same_step_is_called_a_loop(tmp_path):
    session = "fo_loop"
    try:
        f = await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        outputs = []
        for i in range(4):
            text = f.read_text().replace(
                'FAIL_TAC "inside"', f'FAIL_TAC "inside{i}"')
            text = re.sub(r'FAIL_TAC "inside\d*"', f'FAIL_TAC "inside{i}"', text)
            f.write_text(text)
            outputs.append(await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session))
        assert all("PROOF BROKEN" in o for o in outputs), outputs[-1]
        assert not any("[Loop:" in o for o in outputs[:3]), outputs[2]
        loop = [ln for ln in outputs[3].split("\n") if ln.startswith("[Loop:")]
        assert loop, outputs[3]
        assert "4 edit" in loop[0] and "opaque_fail" in loop[0], loop[0]
        assert re.search(r"same step \d+", loop[0]), loop[0]
        assert "suspend" in loop[0] and "Resume" in loop[0] and "QED" in loop[0], loop[0]

        # A passing navigation resets the counter.
        f.write_text(f.read_text().replace('FAIL_TAC "inside3"', 'simp []'))
        ok = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session)
        assert "PROOF BROKEN" not in ok, ok
        f.write_text(f.read_text().replace("   simp [])", '   FAIL_TAC "again")', 1))
        again = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session)
        assert "PROOF BROKEN" in again and "[Loop:" not in again, again
    finally:
        await hol_stop(session)
