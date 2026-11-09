"""End-to-end regression for the stale auto-cheat verdict bug.

A Resume body that fails at load is auto-cheated and recorded in
``cursor._failed_proofs`` (so outputs can name it as a cheated dep). The bug:
that verdict survived an ordinary body edit, so after FIXING the body the
navigator kept reporting it as auto-cheated / "NOT VALIDATED" — and a
sub-dispatcher's children kept showing "No such label" — until a full session
``hol_stop`` + cold reload. ``_invalidate_from_line`` now drops the verdict for
the edited theorem (and anything after it), so a fix is honoured in the SAME
session with no restart.

These drive ``FileProofCursor`` directly (the FastMCP tool wrappers are not
callable under pytest in this environment), against a real HOL session.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp.hol_session import HOLSession


SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session_tmpdir(tmp_path):
    session = HOLSession(str(tmp_path))
    await session.start()
    await session.send(
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30
    )
    yield session
    await session.stop()


# Two-suspension theorem; p_case's body is the hole we break then fix.
# p_case QED is on line 15 in BOTH versions (body stays one line), so the same
# navigation target works before and after the edit.
def _script(p_case_body: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib markerLib;\n"          # 1
        "\n"                                                          # 2
        'val _ = new_theory "invres";\n'                             # 3
        "\n"                                                          # 4
        "Theorem two_res:\n"                                          # 5
        "  p /\\ (p ==> q) ==> p /\\ q\n"                            # 6
        "Proof\n"                                                     # 7
        "  strip_tac >> conj_tac\n"                                   # 8
        '  >- suspend "p_case"\n'                                     # 9
        '  >- suspend "q_case"\n'                                     # 10
        "QED\n"                                                       # 11
        "\n"                                                          # 12
        "Resume two_res[p_case]:\n"                                   # 13
        f"  {p_case_body}\n"                                          # 14
        "QED\n"                                                       # 15
        "\n"                                                          # 16
        "Resume two_res[q_case]:\n"                                   # 17
        "  RES_TAC\n"                                                 # 18
        "QED\n"                                                       # 19
        "\n"                                                          # 20
        "Finalise two_res\n"                                          # 21
        "\n"                                                          # 22
        "val _ = export_theory();\n"                                  # 23
    )


P_CASE_QED_LINE = 15
Q_CASE_QED_LINE = 19


def _is_proof_complete(res) -> bool:
    """Proof reached completion: every tactic replayed, no residual goals, and
    no real error (a benign 'no goals' error when landing past QED is fine)."""
    return bool(
        not res.goals
        and res.tactics_replayed == res.tactics_total
        and (res.error is None or "no goals" in res.error.lower())
    )


@pytest.mark.asyncio
async def test_fixed_resume_body_honoured_without_restart(
    hol_session_tmpdir, tmp_path: Path
):
    script = tmp_path / "invresScript.sml"

    # 1. Broken p_case body. Navigate to q_case's QED so p_case is in the
    #    PREFIX — that is what auto-cheats it and records it in _failed_proofs.
    script.write_text(_script('FAIL_TAC "broken p_case"'))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    await cursor.state_at(Q_CASE_QED_LINE, 1)
    assert "two_res[p_case]" in cursor._failed_proofs, (
        "broken p_case (in the prefix) should be auto-cheated and recorded"
    )

    # 2. Fix the body in place — SAME cursor/session, no hol_stop. Re-navigate
    #    to q_case's QED: the prefix re-runs the now-fixed p_case.
    script.write_text(_script("ASM_REWRITE_TAC[]"))
    res_q = await cursor.state_at(Q_CASE_QED_LINE, 1)

    # The stale verdict must be gone (the core of the fix): without it, p_case
    # would still be reported as auto-cheated until a session restart.
    assert "two_res[p_case]" not in cursor._failed_proofs, (
        "stale auto-cheat verdict survived the edit — would still cry wolf "
        "until a session restart"
    )
    assert _is_proof_complete(res_q), (
        f"q_case did not validate after fixing the prefix: error={res_q.error!r} "
        f"replayed={res_q.tactics_replayed}/{res_q.tactics_total}"
    )

    # 3. The fixed p_case body itself now replays to completion as a target.
    res_p = await cursor.state_at(P_CASE_QED_LINE, 1)
    assert _is_proof_complete(res_p), (
        f"fixed p_case did not validate in-session: error={res_p.error!r} "
        f"replayed={res_p.tactics_replayed}/{res_p.tactics_total} "
        f"goals={res_p.goals!r}"
    )


# A Resume sub-dispatcher: nested[A]'s body sub-suspends "B", which nested[B]
# resumes. If nested[A]'s body fails it is auto-cheated, the `suspend "B"` never
# runs, and B is orphaned (navigating to nested[B] -> "No such label"). Breaking
# then fixing nested[A] is exactly the restart-forcing scenario.
def _nested_script(dispatcher_body: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib markerLib;\n"          # 1
        "\n"                                                          # 2
        'val _ = new_theory "invnest";\n'                            # 3
        "\n"                                                          # 4
        "Theorem nested:\n"                                          # 5
        "  p /\\ p ==> p /\\ p\n"                                    # 6
        "Proof\n"                                                     # 7
        '  suspend "A"\n'                                             # 8
        "QED\n"                                                       # 9
        "\n"                                                          # 10
        "Resume nested[A]:\n"                                         # 11
        f"  {dispatcher_body}\n"                                      # 12
        "QED\n"                                                       # 13
        "\n"                                                          # 14
        "Resume nested[B]:\n"                                         # 15
        "  first_assum ACCEPT_TAC\n"                                  # 16
        "QED\n"                                                       # 17
        "\n"                                                          # 18
        "Finalise nested\n"                                           # 19
        "\n"                                                          # 20
        "val _ = export_theory();\n"                                  # 21
    )


NESTED_B_QED_LINE = 17
_GOOD_DISPATCHER = 'strip_tac >> conj_tac >- suspend "B" >- first_assum ACCEPT_TAC'
_BROKEN_DISPATCHER = 'FAIL_TAC "broken dispatcher" >> ' + _GOOD_DISPATCHER


@pytest.mark.asyncio
async def test_fixed_subdispatcher_unorphans_child_without_restart(
    hol_session_tmpdir, tmp_path: Path
):
    script = tmp_path / "invnestScript.sml"

    # 1. Broken dispatcher: nested[A] is auto-cheated, so "B" never registers
    #    and nested[B] is orphaned.
    script.write_text(_nested_script(_BROKEN_DISPATCHER))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    await cursor.state_at(NESTED_B_QED_LINE, 1)
    assert "nested[A]" in cursor._failed_proofs, (
        "broken dispatcher nested[A] should be auto-cheated"
    )

    # 2. Fix the dispatcher — SAME cursor/session, no hol_stop. Re-navigating to
    #    nested[B] must now succeed: the prefix re-runs the fixed nested[A],
    #    which re-registers "B" so the child is navigable again.
    script.write_text(_nested_script(_GOOD_DISPATCHER))
    res_b = await cursor.state_at(NESTED_B_QED_LINE, 1)

    assert "nested[A]" not in cursor._failed_proofs, (
        "stale dispatcher verdict survived the edit"
    )
    assert "nested[B]" not in cursor._failed_proofs, (
        "child nested[B] still flagged as skipped/orphaned after the fix"
    )
    assert _is_proof_complete(res_b), (
        f"nested[B] not navigable after fixing the dispatcher in-session: "
        f"error={res_b.error!r} "
        f"replayed={res_b.tactics_replayed}/{res_b.tactics_total} "
        f"goals={res_b.goals!r}"
    )


# Structure-change case: a HEALTHY chain (nothing auto-cheated) whose dispatcher
# is edited to add a NEW sub-suspend "C" plus its Resume block. The Bug-B reinit
# is gated on the chain being broken, so this falls through to the normal
# partial-replay path — this test checks whether the new child is navigable
# without a restart, i.e. whether that gate needs widening.
_STRUCT_V1 = (
    "open HolKernel Parse boolLib bossLib markerLib;\n"   # 1
    "\n"                                                   # 2
    'val _ = new_theory "invstruct";\n'                   # 3
    "\n"                                                   # 4
    "Theorem nested:\n"                                    # 5
    "  p /\\ p ==> p /\\ p\n"                              # 6
    "Proof\n"                                              # 7
    '  suspend "A"\n'                                      # 8
    "QED\n"                                                # 9
    "\n"                                                   # 10
    "Resume nested[A]:\n"                                  # 11
    "  strip_tac >> conj_tac\n"                            # 12
    '  >- suspend "B"\n'                                   # 13
    "  >- first_assum ACCEPT_TAC\n"                        # 14
    "QED\n"                                                # 15
    "\n"                                                   # 16
    "Resume nested[B]:\n"                                  # 17
    "  first_assum ACCEPT_TAC\n"                           # 18
    "QED\n"                                                # 19
    "\n"                                                   # 20
    "Finalise nested\n"                                    # 21
    "\n"                                                   # 22
    "val _ = export_theory();\n"                           # 23
)
# Only line 14 changes (inline close -> sub-suspend C) plus a new Resume block.
_STRUCT_V2 = (
    "open HolKernel Parse boolLib bossLib markerLib;\n"   # 1
    "\n"                                                   # 2
    'val _ = new_theory "invstruct";\n'                   # 3
    "\n"                                                   # 4
    "Theorem nested:\n"                                    # 5
    "  p /\\ p ==> p /\\ p\n"                              # 6
    "Proof\n"                                              # 7
    '  suspend "A"\n'                                      # 8
    "QED\n"                                                # 9
    "\n"                                                   # 10
    "Resume nested[A]:\n"                                  # 11
    "  strip_tac >> conj_tac\n"                            # 12
    '  >- suspend "B"\n'                                   # 13
    '  >- suspend "C"\n'                                   # 14
    "QED\n"                                                # 15
    "\n"                                                   # 16
    "Resume nested[B]:\n"                                  # 17
    "  first_assum ACCEPT_TAC\n"                           # 18
    "QED\n"                                                # 19
    "\n"                                                   # 20
    "Resume nested[C]:\n"                                  # 21
    "  first_assum ACCEPT_TAC\n"                           # 22
    "QED\n"                                                # 23
    "\n"                                                   # 24
    "Finalise nested\n"                                    # 25
    "\n"                                                   # 26
    "val _ = export_theory();\n"                           # 27
)
STRUCT_V1_B_QED = 19
STRUCT_V2_C_QED = 23


@pytest.mark.asyncio
async def test_healthy_chain_structure_change_new_child_navigable(
    hol_session_tmpdir, tmp_path: Path
):
    script = tmp_path / "invstructScript.sml"

    # 1. Healthy chain — validate it so nothing is in _failed_proofs.
    script.write_text(_STRUCT_V1)
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    res_b = await cursor.state_at(STRUCT_V1_B_QED, 1)
    assert _is_proof_complete(res_b), f"v1 nested[B] should be healthy: {res_b.error!r}"
    assert cursor._failed_proofs == {}, (
        f"chain must be healthy before the structure change: {cursor._failed_proofs!r}"
    )

    # 2. Add a new sub-suspend "C" to the dispatcher + its Resume block, then
    #    navigate to nested[C] — same cursor/session, no restart.
    script.write_text(_STRUCT_V2)
    res_c = await cursor.state_at(STRUCT_V2_C_QED, 1)

    assert _is_proof_complete(res_c), (
        f"new child nested[C] not navigable after a healthy structure change: "
        f"error={res_c.error!r} "
        f"replayed={res_c.tactics_replayed}/{res_c.tactics_total} "
        f"goals={res_c.goals!r}"
    )
