"""Editing a `Definition` above the cursor must re-execute it, not go stale.

Two coupled defects from ``HOL_STATE_AT_DEF_EDIT_STALENESS_NOTES.md``, both
triggered by editing a construct that sits *before* the cursor's position:

* **A (silent staleness)** — the edited `Definition` is never re-executed, so
  the in-heap constant keeps its old rhs. A later theorem then replays against
  the stale constant. The dangerous direction is the one asserted here: after
  the edit the consumer's statement is *false*, so a session that has gone
  stale reports a false theorem as proved.
* **B (wedged forward replay)** — navigating backwards past the edit and then
  forwards again fails with ``Error executing file content``, and the region
  stays unreachable until the session is restarted.

Both are provoked by editing a line in the *middle* of a multi-line construct,
which is what makes the partial-reload truncation point land inside it.

Drives ``FileProofCursor`` directly against a real HOL session, as the other
invalidation tests do.
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


# `value` occupies line 12 only — a MIDDLE line of the three-line Definition.
def _script(value: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"   # 1
        "\n"                                        # 2
        'val _ = new_theory "defstale";\n'          # 3
        "\n"                                        # 4
        "Theorem base:\n"                           # 5
        "  T\n"                                     # 6
        "Proof\n"                                   # 7
        "  simp[]\n"                                # 8
        "QED\n"                                     # 9
        "\n"                                        # 10
        "Definition d_def:\n"                       # 11
        f"  d = ({value}:num)\n"                     # 12
        "End\n"                                     # 13
        "\n"                                        # 14
        "Theorem user:\n"                           # 15
        "  d = 1\n"                                 # 16
        "Proof\n"                                   # 17
        "  simp[d_def]\n"                           # 18
        "QED\n"                                     # 19
        "\n"                                        # 20
        "val _ = export_theory();\n"                # 21
    )


BASE_QED_LINE = 9
USER_QED_LINE = 19


def _is_proof_complete(res) -> bool:
    return bool(
        not res.goals
        and res.tactics_replayed == res.tactics_total
        and (res.error is None or "no goals" in res.error.lower())
    )


@pytest.mark.asyncio
async def test_edited_definition_is_reexecuted_for_later_theorem(
    hol_session_tmpdir, tmp_path: Path
):
    """Defect A: a stale session must not report a now-false theorem as proved."""
    script = tmp_path / "defstaleScript.sml"

    # 1. d = 1, so `user : d = 1` closes.
    script.write_text(_script("1"))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    res_ok = await cursor.state_at(USER_QED_LINE, 1)
    assert _is_proof_complete(res_ok), (
        "sanity: `user` must close while d = 1: "
        f"error={res_ok.error!r} goals={res_ok.goals!r}"
    )

    # 2. Change the Definition's middle line to d = 2. `user : d = 1` is now
    #    FALSE. Its own text is unchanged, so it must be replayed against the
    #    NEW definition and must no longer close.
    script.write_text(_script("2"))
    res_stale = await cursor.state_at(USER_QED_LINE, 1)

    assert not _is_proof_complete(res_stale), (
        "`user` still closes after `d_def` was changed to d = 2 — the session "
        "replayed against the stale pre-edit definition, so a FALSE theorem is "
        f"reported as proved: error={res_stale.error!r} "
        f"replayed={res_stale.tactics_replayed}/{res_stale.tactics_total} "
        f"goals={res_stale.goals!r}"
    )


@pytest.mark.asyncio
async def test_backward_then_forward_navigation_after_definition_edit(
    hol_session_tmpdir, tmp_path: Path
):
    """Defect B: backwards past the edit, then forwards, must not wedge."""
    script = tmp_path / "defstaleScript.sml"

    script.write_text(_script("1"))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    await cursor.state_at(USER_QED_LINE, 1)

    # Edit the Definition's middle line, then jump BACKWARDS to a theorem
    # before it, then forwards again.
    script.write_text(_script("2"))
    res_back = await cursor.state_at(BASE_QED_LINE, 1)
    assert res_back.error is None or "executing file content" not in res_back.error, (
        f"backward navigation itself wedged: {res_back.error!r}"
    )

    res_fwd = await cursor.state_at(USER_QED_LINE, 1)
    assert res_fwd.error is None or "executing file content" not in res_fwd.error, (
        "forward replay after a backward jump past the edited Definition "
        f"wedged: {res_fwd.error!r}"
    )


# A multi-line comment sitting in the gap between two blocks. Editing its last
# line makes the reload resume mid-comment, and HOL then parses the comment's
# words as terms — the observed symptom is `Unknown identifier: <a word of the
# comment>`, pointing nowhere near the edit.
def _comment_script(value: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"   # 1
        "\n"                                        # 2
        'val _ = new_theory "cmtstale";\n'          # 3
        "\n"                                        # 4
        "Theorem base:\n"                           # 5
        "  T\n"                                     # 6
        "Proof\n"                                   # 7
        "  simp[]\n"                                # 8
        "QED\n"                                     # 9
        "\n"                                        # 10
        "(* a comment about d\n"                    # 11
        "   spanning several lines\n"               # 12
        f"   {value} *)\n"                          # 13
        "Definition d_def:\n"                       # 14
        "  d = (1:num)\n"                           # 15
        "End\n"                                     # 16
        "\n"                                        # 17
        "Theorem user:\n"                           # 18
        "  d = 1\n"                                 # 19
        "Proof\n"                                   # 20
        "  simp[d_def]\n"                           # 21
        "QED\n"                                     # 22
        "\n"                                        # 23
        "val _ = export_theory();\n"                # 24
    )


COMMENT_USER_QED_LINE = 22


@pytest.mark.asyncio
async def test_edit_inside_multiline_comment_does_not_wedge_replay(
    hol_session_tmpdir, tmp_path: Path
):
    """Editing a multi-line comment must not resend from mid-comment."""
    script = tmp_path / "cmtstaleScript.sml"

    script.write_text(_comment_script("first"))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    res_ok = await cursor.state_at(COMMENT_USER_QED_LINE, 1)
    assert _is_proof_complete(res_ok), (
        f"sanity: `user` must close: error={res_ok.error!r} goals={res_ok.goals!r}"
    )

    # Edit the comment's LAST line only. Nothing semantic changed.
    script.write_text(_comment_script("second"))
    res_after = await cursor.state_at(COMMENT_USER_QED_LINE, 1)

    assert res_after.error is None or "executing file content" not in res_after.error, (
        "replay resumed inside the comment, so HOL parsed its words as terms: "
        f"{res_after.error!r}"
    )
    assert _is_proof_complete(res_after), (
        "`user` no longer closes after a comment-only edit: "
        f"error={res_after.error!r} goals={res_after.goals!r}"
    )


# The comment is NOT edited here; the edit lands inside the Theorem that sits
# directly BELOW a multi-line comment. Field recurrence 2026-08-28 on
# data_to_wordProofScript.sml (`Unknown identifier: leaves`/`goes`/`the`, each
# the first word of a comment's CONTINUATION line) had exactly this shape, with
# the mid-gap fix already live — so the comment-edit test above does not cover
# it.
def _below_comment_script(annot: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"   # 1
        "\n"                                        # 2
        'val _ = new_theory "belowcmt";\n'          # 3
        "\n"                                        # 4
        "Theorem base:\n"                           # 5
        "  T\n"                                     # 6
        "Proof\n"                                   # 7
        "  simp[]\n"                                # 8
        "QED\n"                                     # 9
        "\n"                                        # 10
        "(* the word code found at dest is the callee body --\n"   # 11
        "   find_code_thm leaves those labels existential *)\n"     # 12
        "Theorem lemma:\n"                          # 13
        f"  !(n:num). n + ({annot}) = ({annot}) + n\n"  # 14  <- EDITED
        "Proof\n"                                   # 15
        "  simp[]\n"                                # 16
        "QED\n"                                     # 17
        "\n"                                        # 18
        "Theorem user:\n"                           # 19
        "  (1:num) + 2 = 2 + 1\n"                   # 20
        "Proof\n"                                   # 21
        "  simp[]\n"                                # 22
        "QED\n"                                     # 23
        "\n"                                        # 24
        "val _ = export_theory();\n"                # 25
    )


BELOW_COMMENT_USER_QED_LINE = 23


@pytest.mark.asyncio
async def test_edit_below_multiline_comment_does_not_wedge_replay(
    hol_session_tmpdir, tmp_path: Path
):
    """Editing INSIDE the block below a multi-line comment must not wedge.

    Regression guard for the 2026-08-28 recurrence: the truncation boundary is
    the Theorem's own line, so the resend must never hand HOL the tail of the
    comment above it.
    """
    script = tmp_path / "belowcmtScript.sml"

    script.write_text(_below_comment_script("1:num"))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    # Load PAST the edit point, so the later edit is above _loaded_to_line and
    # takes the partial-reload path.
    res_ok = await cursor.state_at(BELOW_COMMENT_USER_QED_LINE, 1)
    assert _is_proof_complete(res_ok), (
        f"sanity: `user` must close: error={res_ok.error!r} goals={res_ok.goals!r}"
    )

    # Edit a line INSIDE `lemma` (line 14) — the comment itself is untouched.
    script.write_text(_below_comment_script("2:num"))
    res_after = await cursor.state_at(BELOW_COMMENT_USER_QED_LINE, 1)

    assert res_after.error is None or "Unknown identifier" not in res_after.error, (
        "replay handed HOL a fragment of the comment above the edited block: "
        f"{res_after.error!r}"
    )
    assert res_after.error is None or "executing file content" not in res_after.error, (
        f"forward replay wedged after an edit below a multi-line comment: "
        f"{res_after.error!r}"
    )
    assert _is_proof_complete(res_after), (
        "`user` no longer closes after an edit below a multi-line comment: "
        f"error={res_after.error!r} goals={res_after.goals!r}"
    )
