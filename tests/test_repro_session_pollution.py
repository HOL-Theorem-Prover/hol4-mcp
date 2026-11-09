"""Reproductions for four session-pollution/staleness gaps (MCP_BUGS_review.md
#4, #5, #6, #8).

Every test asserts the CORRECT behaviour and is expected to FAIL until the
finding is fixed.  All four need a live session plus a file edit (or a live
probe) mid-test, so each writes its script into ``tmp_path`` and drives the
server-level tool functions, exactly as a caller would.

Finding #4 — edits to untracked constructs are silently ineffective
==================================================================

``parse_theorems`` does not track a plain ``Definition ... End``, so an edit
inside one is handled as a pre-content edit.  ``_reparse_if_changed``
(``hol_cursor.py:530-533``) truncates ``_loaded_to_line`` to
``first_changed - 1``, and ``_load_context_to_line``
(``hol_cursor.py:1526-1530``) resends the gap starting at that line.  When the
edit lands on the third or later line of the construct, the resend therefore
begins INSIDE it and the fragment is garbage.

Pinned here:

  - the navigation past the edited Definition wedges with
    ``Error executing file content`` and stays wedged
    (``test_definition_edit_does_not_wedge_later_navigation``);
  - the session's constant keeps its PRE-EDIT right-hand side, so every goal
    and probe after the edit is computed against the old definition
    (``test_definition_edit_reaches_the_session``).

Finding #5 — `_session_dirty` is honoured only by the reuse path
================================================================

A sanctioned short ``e``-probe on a navigated frontier taints the cursor
(``hol_mcp_server.py:871-874``).  Strategy 1 checks the flag
(``hol_cursor.py:1796``), but a subsequent FILE EDIT skips strategy 1 and
lands on strategy 2, whose gate (``hol_cursor.py:2091-2096``) never looks at
it; with the target inside the common prefix ``_try_incremental_navigate``
issues zero commands and returns the live, post-probe goal stack as if it were
the file's state.  ``_update_position`` (``hol_cursor.py:2139``) then clears
the flag (``test_probe_taint_survives_a_file_edit``).

Finding #6 — backward `state_at` replays in a future-polluted context
=====================================================================

``execute_proof_traced`` restores a predecessor context when
``_loaded_to_line`` extends past the target theorem
(``hol_cursor.py:2349-2368``); the ``state_at`` path has no such handling and
falls to ``_replay_to_boundary`` → ``_setup_proof_goal``
(``hol_cursor.py:1682-1732``), i.e. ``drop_all`` + ``gf`` in the CURRENT
session.  A later ``[simp]``-tagged theorem is then in the ambient simpset
while an earlier theorem replays, so the earlier proof reaches a state the
file's own order never produces
(``test_backward_state_at_ignores_later_simp_theorem``).

Finding #8 — stale "⚠ depends on cheat" verdicts are never invalidated
======================================================================

``_invalidate_from_line`` (``hol_cursor.py:968-1051``) cleans checkpoints,
traces, tc_goals, resume_goals and ``_failed_proofs`` but not
``_theorem_oracles``, and re-verification overwrites the entry only when the
new oracle list is non-empty (``hol_cursor.py:2444-2445``).  Discharging the
cheat therefore leaves the warning in place for the rest of the session
(``test_cheat_verdict_cleared_after_dependency_is_fixed``).
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    hol_check_proof as _hol_check_proof,
    hol_send as _hol_send,
    hol_state_at as _hol_state_at,
    hol_stop as _hol_stop,
)

hol_check_proof = _hol_check_proof
hol_send = _hol_send
hol_state_at = _hol_state_at
hol_stop = _hol_stop
hol_file_init = _init_file_cursor

COMPLETE_MARKER = "No goals (proof complete)"
WEDGE_MARKER = "Error executing file content"


# ----------------------------------------------------------------------
# Finding #4: a plain `Definition` edited on its third line.
# ----------------------------------------------------------------------
#
#  1 open HolKernel Parse boolLib bossLib;
#  3 val _ = new_theory "reprodefstale";
#  5 Theorem base: ... QED                        (tracked, before the edit)
# 11 Definition d_def:
# 12   d (n:num) =
# 13     if n = 0 then 0
# 14     else <VALUE>                             <-- the edited line
# 15 End
# 17 Theorem user: d 1 = 7 ... QED                (navigation target)


def _def_script(value: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"      # 1
        "\n"                                           # 2
        'val _ = new_theory "reprodefstale";\n'        # 3
        "\n"                                           # 4
        "Theorem base:\n"                              # 5
        "  T\n"                                        # 6
        "Proof\n"                                      # 7
        "  simp[]\n"                                   # 8
        "QED\n"                                        # 9
        "\n"                                           # 10
        "Definition d_def:\n"                          # 11
        "  d (n:num) =\n"                              # 12
        "    if n = 0 then 0\n"                        # 13
        f"    else {value}\n"                          # 14
        "End\n"                                        # 15
        "\n"                                           # 16
        "Theorem user:\n"                              # 17
        "  d 1 = 7\n"                                  # 18
        "Proof\n"                                      # 19
        "  simp[d_def]\n"                              # 20
        "QED\n"                                        # 21
        "\n"                                           # 22
        "val _ = export_theory();\n"                   # 23
    )


_DEF_USER_QED = 21
_DEF_STALE = "5"
_DEF_FIXED = "7"


async def _def_edit_run(tmp_path: Path, session: str) -> tuple[str, str, str]:
    """Navigate past `d_def`, edit its third line, navigate again.

    Returns (before, after, probe): the two ``hol_state_at`` reports and the
    session's own ``d_def`` after the edit.
    """
    script = tmp_path / "reprodefstaleScript.sml"
    script.write_text(_def_script(_DEF_STALE))

    init = await hol_file_init(file=str(script), session=session)
    assert not init.startswith("ERROR"), init

    before = await hol_state_at(session=session, line=_DEF_USER_QED, col=1)
    assert COMPLETE_MARKER not in before, (
        f"fixture setup: `user` must NOT close while d 1 = {_DEF_STALE}:\n{before}"
    )

    script.write_text(_def_script(_DEF_FIXED))
    after = await hol_state_at(session=session, line=_DEF_USER_QED, col=1)
    probe = await hol_send(command="d_def;", timeout=10, session=session)
    return before, after, probe


async def test_definition_edit_does_not_wedge_later_navigation(tmp_path: Path):
    session = "repro_pollution_def_wedge"
    try:
        _before, after, _probe = await _def_edit_run(tmp_path, session)
    finally:
        await hol_stop(session=session)

    assert WEDGE_MARKER not in after, (
        "editing a line inside a plain `Definition` wedged the navigation "
        "past it: the resend started mid-construct, so the fragment does not "
        f"parse and the region stays unreachable.\n{after}"
    )


async def test_definition_edit_reaches_the_session(tmp_path: Path):
    session = "repro_pollution_def_stale"
    try:
        _before, after, probe = await _def_edit_run(tmp_path, session)
    finally:
        await hol_stop(session=session)

    assert f"else {_DEF_FIXED}" in probe, (
        "the session's `d_def` still shows the PRE-EDIT right-hand side after "
        "the file was edited and navigated past, so goals and probes are "
        f"computed against a definition that no longer exists.\n"
        f"--- d_def ---\n{probe}\n--- state_at ---\n{after}"
    )


# ----------------------------------------------------------------------
# Finding #5: an `e`-probe at the frontier, then a file edit.
# ----------------------------------------------------------------------
#
#  5 Theorem probe_target:
#  6   !a b. (a:num) + b = b + a
#  7 Proof
#  8   rpt strip_tac >>                           (step 0 — the frontier)
#  9   <SECOND>                                   (step 1 — the edited step)
# 10 QED


def _probe_script(second: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"      # 1
        "\n"                                           # 2
        'val _ = new_theory "reproprobetaint";\n'      # 3
        "\n"                                           # 4
        "Theorem probe_target:\n"                      # 5
        "  !a b. (a:num) + b = b + a\n"                # 6
        "Proof\n"                                      # 7
        "  rpt strip_tac >>\n"                         # 8
        f"  {second}\n"                                # 9
        "QED\n"                                        # 10
        "\n"                                           # 11
        "val _ = export_theory();\n"                   # 12
    )


_PROBE_FRONTIER = 9          # start of the second step: after `rpt strip_tac`
_PROBE_GOAL = "a + b = b + a"


async def test_probe_taint_survives_a_file_edit(tmp_path: Path):
    script = tmp_path / "reproprobetaintScript.sml"
    script.write_text(_probe_script("simp[arithmeticTheory.ADD_COMM]"))

    session = "repro_pollution_probe_taint"
    try:
        init = await hol_file_init(file=str(script), session=session)
        assert not init.startswith("ERROR"), init

        frontier = await hol_state_at(
            session=session, line=_PROBE_FRONTIER, col=3
        )
        assert _PROBE_GOAL in frontier, (
            f"fixture setup: expected the frontier goal at line "
            f"{_PROBE_FRONTIER}:\n{frontier}"
        )

        # Sanctioned short probe on the navigated frontier: it closes the goal
        # in the live proofManager, one step past the cursor's position.
        probe = await hol_send(
            command="e (simp[arithmeticTheory.ADD_COMM]);",
            timeout=20, session=session,
        )
        assert "BLOCKED" not in probe, f"fixture setup: probe refused:\n{probe}"

        # Edit the step AFTER the frontier: the common prefix still covers the
        # target, so strategy 2 is chosen and strategy 1 is skipped.
        script.write_text(_probe_script("simp[Once arithmeticTheory.ADD_COMM]"))
        after = await hol_state_at(
            session=session, line=_PROBE_FRONTIER, col=3
        )
    finally:
        await hol_stop(session=session)

    assert _PROBE_GOAL in after and COMPLETE_MARKER not in after, (
        "after an `e` probe and a file edit, state_at reported the probe's "
        "goal stack instead of the file's state at the same position — the "
        "incremental path navigated from the polluted position without "
        f"issuing a single command.\n--- before probe ---\n{frontier}\n"
        f"--- probe ---\n{probe}\n--- after edit ---\n{after}"
    )


# ----------------------------------------------------------------------
# Finding #6: navigate forward past a `[simp]` theorem, then backward.
# ----------------------------------------------------------------------
#
#  5 Definition f_def:  f (n:num) = n + 1  End
#  9 Theorem early:
# 10   !n. f (n + 0) = n + 1
# 11 Proof
# 12   simp[] >>                                  (step 0)
# 13   simp[f_def]                                (step 1 — the read position)
# 14 QED
# 16 Theorem f_thm[simp]: f n = n + 1 ... QED     (later, tagged [simp])
# 22 Theorem late: ... QED                        (forward navigation target)
#
# In file order step 0 leaves `∀n. f n = n + 1` open (nothing unfolds `f`).
# With `f_thm[simp]` registered, the very same step closes the goal.

_POLLUTED_SCRIPT = (
    "open HolKernel Parse boolLib bossLib;\n"      # 1
    "\n"                                           # 2
    'val _ = new_theory "reprofuturepoll";\n'      # 3
    "\n"                                           # 4
    "Definition f_def:\n"                          # 5
    "  f (n:num) = n + 1\n"                        # 6
    "End\n"                                        # 7
    "\n"                                           # 8
    "Theorem early:\n"                             # 9
    "  !n. f (n + 0) = n + 1\n"                    # 10
    "Proof\n"                                      # 11
    "  simp[] >>\n"                                # 12
    "  simp[f_def]\n"                              # 13
    "QED\n"                                        # 14
    "\n"                                           # 15
    "Theorem f_thm[simp]:\n"                       # 16
    "  f n = n + 1\n"                              # 17
    "Proof\n"                                      # 18
    "  simp[f_def]\n"                              # 19
    "QED\n"                                        # 20
    "\n"                                           # 21
    "Theorem late:\n"                              # 22
    "  f 5 = 6\n"                                  # 23
    "Proof\n"                                      # 24
    "  simp[]\n"                                   # 25
    "QED\n"                                        # 26
    "\n"                                           # 27
    "val _ = export_theory();\n"                   # 28
)

_EARLY_MID = 13              # inside `early`, after its first step
_LATE_QED = 26


async def test_backward_state_at_ignores_later_simp_theorem(tmp_path: Path):
    script = tmp_path / "reprofuturepollScript.sml"
    script.write_text(_POLLUTED_SCRIPT)

    cold_session = "repro_pollution_simp_cold"
    try:
        init = await hol_file_init(file=str(script), session=cold_session)
        assert not init.startswith("ERROR"), init
        cold = await hol_state_at(session=cold_session, line=_EARLY_MID, col=3)
    finally:
        await hol_stop(session=cold_session)

    assert COMPLETE_MARKER not in cold, (
        f"fixture setup: in file order `early`'s first step must leave a "
        f"goal open:\n{cold}"
    )

    back_session = "repro_pollution_simp_back"
    try:
        init = await hol_file_init(file=str(script), session=back_session)
        assert not init.startswith("ERROR"), init
        forward = await hol_state_at(session=back_session, line=_LATE_QED, col=1)
        assert not forward.startswith("ERROR"), forward
        back = await hol_state_at(session=back_session, line=_EARLY_MID, col=3)
    finally:
        await hol_stop(session=back_session)

    assert COMPLETE_MARKER not in back, (
        "after navigating past `f_thm[simp]`, navigating BACK into `early` "
        "replayed its first step with that later theorem in the ambient "
        "simpset, so the step closes a goal that Holmake leaves open. The "
        "same position in a cold session shows the goal.\n"
        f"--- cold ---\n{cold}\n--- after backward jump ---\n{back}"
    )


# ----------------------------------------------------------------------
# Finding #8: discharge the cheat a verdict was derived from.
# ----------------------------------------------------------------------
#
#  5 Definition p_def:  p (n:num) = (n + 0 = n)  End
#  9 Theorem dep:
# 10   !n. p n
# 11 Proof
# 12   <DEP PROOF>                                <-- `cheat`, then a real proof
# 13 QED
# 15 Theorem usedep:  p 3 /\ p 4  Proof simp[dep] QED


def _oracle_script(dep_proof: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"      # 1
        "\n"                                           # 2
        'val _ = new_theory "reprooraclestale";\n'     # 3
        "\n"                                           # 4
        "Definition p_def:\n"                          # 5
        "  p (n:num) = (n + 0 = n)\n"                  # 6
        "End\n"                                        # 7
        "\n"                                           # 8
        "Theorem dep:\n"                               # 9
        "  !n. p n\n"                                  # 10
        "Proof\n"                                      # 11
        f"  {dep_proof}\n"                             # 12
        "QED\n"                                        # 13
        "\n"                                           # 14
        "Theorem usedep:\n"                            # 15
        "  p 3 /\\ p 4\n"                              # 16
        "Proof\n"                                      # 17
        "  simp[dep]\n"                                # 18
        "QED\n"                                        # 19
        "\n"                                           # 20
        "val _ = export_theory();\n"                   # 21
    )


_CHEAT_WARNING = "depends on cheat"


async def test_cheat_verdict_cleared_after_dependency_is_fixed(tmp_path: Path):
    script = tmp_path / "reprooraclestaleScript.sml"
    script.write_text(_oracle_script("cheat"))

    session = "repro_pollution_oracle"
    try:
        init = await hol_file_init(file=str(script), session=session)
        assert not init.startswith("ERROR"), init

        cheated = await hol_check_proof(theorem="usedep", session=session)
        assert _CHEAT_WARNING in cheated, (
            f"fixture setup: `usedep` must inherit `dep`'s cheat:\n{cheated}"
        )

        # Discharge the cheat: `dep` now has a real proof.
        script.write_text(_oracle_script("simp[p_def]"))
        dep_now = await hol_check_proof(theorem="dep", session=session)
        assert "Status: OK" in dep_now and _CHEAT_WARNING not in dep_now, (
            f"fixture setup: `dep` must verify cleanly after the fix:\n{dep_now}"
        )

        fixed = await hol_check_proof(theorem="usedep", session=session)
    finally:
        await hol_stop(session=session)

    assert _CHEAT_WARNING not in fixed, (
        "`usedep` still reports a cheat dependency after `dep` was re-proved "
        "cleanly in the same session; the verdict contradicts the tool's own "
        f"dep listing.\n--- dep after fix ---\n{dep_now}\n"
        f"--- usedep after fix ---\n{fixed}"
    )
