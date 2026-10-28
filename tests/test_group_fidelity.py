"""A parenthesised group applied by `\\` to several goals runs once per goal,
so a `>-` inside it focuses each goal's first subgoal. The step plan must keep
such a group whole: flattened, its `>-` would take the first goal of all of
them, and a proof Holmake accepts would be reported broken (P5, C1)."""
from pathlib import Path

import pytest

from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    hol_check_proof,
    hol_state_at,
    hol_stop,
    holmake,
)

# conj_tac hands the inner group two goals; per goal, conj_tac >- simp[]
# closes `n = n` and ACCEPT_TAC TRUTH closes `T`. Flattened, ACCEPT_TAC TRUTH
# would meet the second goal's `1 = 1` and fail.
ARM_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "grp";

Theorem in_arm:
  T /\\ (T /\\ (((0 = 0) /\\ T) /\\ ((1 = 1) /\\ T)))
Proof
  conj_tac >- simp[] >- (
    conj_tac >- simp[] \\\\
    conj_tac \\\\ (
      conj_tac >- simp[] \\\\ ACCEPT_TAC TRUTH))
QED

Theorem in_selected_arm:
  T /\\ (T /\\ (((0 = 0) /\\ T) /\\ ((1 = 1) /\\ T)))
Proof
  conj_tac >- simp [] >~ [`T /\\ _`] >- (
    conj_tac >- (simp [])
    \\\\ conj_tac
    \\\\ (
      conj_tac >- (simp [])
      \\\\ ACCEPT_TAC TRUTH))
QED

val _ = export_theory();
"""


# The inner conj_tac gives each goal [n = n, T]. Per goal, LASTGOAL closes
# `T`, and the `>-` under TRY closes `n = n`; flattened over both goals, each
# acts on one goal of four and the next step meets a goal it cannot close.
NESTED_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "nst";

Theorem last_goal:
  ((0 = 0) /\\ T) /\\ ((1 = 1) /\\ T)
Proof
  conj_tac \\\\ (conj_tac >>> LASTGOAL (ACCEPT_TAC TRUTH) \\\\ REFL_TAC)
QED

Theorem under_try:
  ((0 = 0) /\\ T) /\\ ((1 = 1) /\\ T)
Proof
  conj_tac \\\\ (TRY (conj_tac >- REFL_TAC) \\\\ ACCEPT_TAC TRUTH)
QED

val _ = export_theory();
"""


@pytest.mark.parametrize("theorem", ["last_goal", "under_try"])
async def test_nested_goal_positional_group_runs_per_goal(tmp_path, theorem):
    script = tmp_path / "nstScript.sml"
    script.write_text(NESTED_SCRIPT)
    built = await holmake(str(tmp_path), target="nstTheory", timeout=120)
    assert "Build succeeded" in built, built
    session = f"nst_{theorem}"
    try:
        await _init_file_cursor(file=str(script), session=session)
        checked = await hol_check_proof(theorem=theorem, session=session)
        assert "Status: OK" in checked, checked
    finally:
        await hol_stop(session=session)


@pytest.mark.parametrize("theorem", ["in_arm", "in_selected_arm"])
async def test_group_inside_an_arm_runs_per_goal(tmp_path, theorem):
    script = tmp_path / "grpScript.sml"
    script.write_text(ARM_SCRIPT)
    built = await holmake(str(tmp_path), target="grpTheory", timeout=120)
    assert "Build succeeded" in built, built
    session = f"grp_{theorem}"
    try:
        await _init_file_cursor(file=str(script), session=session)
        checked = await hol_check_proof(theorem=theorem, session=session)
        assert "Status: OK" in checked, checked
    finally:
        await hol_stop(session=session)


@pytest.mark.parametrize("qed_line", [12, 23])
async def test_navigation_to_qed_matches_the_build(tmp_path, qed_line):
    script = tmp_path / "grpScript.sml"
    script.write_text(ARM_SCRIPT)
    session = f"grp_qed_{qed_line}"
    try:
        await _init_file_cursor(file=str(script), session=session)
        state = await hol_state_at(line=qed_line, col=1, session=session)
        assert "No goals" in state, state
    finally:
        await hol_stop(session=session)


async def test_navigation_inside_the_group_still_works(tmp_path):
    script = tmp_path / "grpScript.sml"
    script.write_text(ARM_SCRIPT)
    session = "grp_inside"
    try:
        await _init_file_cursor(file=str(script), session=session)
        state = await hol_state_at(line=11, col=7, session=session)
        assert "=== Goal" in state, state
        assert "ERROR" not in state.split("\n")[0], state
    finally:
        await hol_stop(session=session)
