"""Regression tests for the goalfrag_step_plan byte/char offset bug.

Symptom (cake-datacut, ``size_of_app_Number`` in
``compiler/backend/proofs/data_to_word_assignProofScript.sml``):
``hol_state_at(line=<QED-line>)`` reports ``replayed=5/8`` with an
open ``Goal (1 of 1)`` even though ``hol_check_proof`` confirms the
proof closes in 8 steps. The cursor mis-resolves the QED position
to a mid-body tactic index and leaves the goal apparently open.

Root cause
==========

``goalfrag_step_plan_json`` (SML) emits ``step.end`` as a position
into the proof-body string measured in BYTES — SML strings are
byte arrays under Poly/ML, and multibyte UTF-8 characters
(``‘``, ``’``, ``α``, …) advance the internal parser position by
their byte count (e.g., 3 for ``‘``).

The Python cursor stores these as ``StepPlan.end`` and then:

  - compares them against ``len(thm.proof_body)`` (CHAR count) in
    ``_offset_to_tactic_idx``
  - adds them to ``thm.proof_body_offset`` (CHAR count) before
    indexing ``cursor._content`` (a ``str``) in ``tactic_to_loc``

On any proof body containing non-ASCII characters, the step.end
overshoots ``len(body)``, so the QED-line cursor maps to a tactic
index well below ``len(step_plan)`` and the cursor reports the
proof as partially replayed.

Concrete cake-datacut measurements: body chars = 494, body bytes
= 522, step plan ends = [115, 134, 368, 381, 472, 504, 513, 522].
``_offset_to_tactic_idx(494)`` stops at index 5 (504 > 494),
reporting ``replayed=5/8``.

Fix (commit on this branch): convert byte→char offsets at the
parse boundary. ``parse_step_plan_output`` accepts an optional
``body`` parameter; when provided, each ``step.end`` is mapped
through ``_byte_to_char_offset(body.encode('utf-8'), end)``. All
three call sites in ``hol_cursor.py`` pass ``thm.proof_body``.

These tests pin:

  - ``parse_step_plan_output`` with ``body=`` returns char-positioned ends
  - cursor ``state_at`` at QED line replays the full proof when the
    body contains non-ASCII characters
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output, _byte_to_char_offset
from hol4_mcp.hol_cursor import FileProofCursor


FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    await session.send(
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30
    )
    yield session
    await session.stop()


async def step_plan_json(session, body, *, convert=True):
    escaped = escape_sml_string(body)
    out = await session.send(f'goalfrag_step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(out, body if convert else None)


# ----------------------------------------------------------------------
# Unit: byte→char conversion utility
# ----------------------------------------------------------------------


def test_byte_to_char_offset_ascii_identity():
    """Pure-ASCII body: byte offsets and char offsets coincide."""
    body = b"strip_tac >> simp [] >> simp []"
    assert _byte_to_char_offset(body, 0) == 0
    assert _byte_to_char_offset(body, 10) == 10
    assert _byte_to_char_offset(body, len(body)) == len(body)


def test_byte_to_char_offset_multibyte():
    """3-byte UTF-8 chars (``‘``/``’``) consume more bytes than chars."""
    body_str = "‘x’"
    body_bytes = body_str.encode("utf-8")
    assert len(body_str) == 3 and len(body_bytes) == 7
    # End of body in bytes → end of body in chars.
    assert _byte_to_char_offset(body_bytes, len(body_bytes)) == len(body_str)
    # First char fully consumed (3 bytes) → 1 char.
    assert _byte_to_char_offset(body_bytes, 3) == 1
    # Past end → clamped to char length.
    assert _byte_to_char_offset(body_bytes, len(body_bytes) + 5) == len(body_str)


# ----------------------------------------------------------------------
# Integration: parse_step_plan_output converts when body provided
# ----------------------------------------------------------------------


@pytest.mark.asyncio
async def test_step_plan_offsets_are_char_positions_when_body_provided(hol_session):
    """``parse_step_plan_output(out, body)`` must return ``end`` values
    that match Python CHARACTER positions in ``body``, even when the
    body contains multibyte UTF-8 characters.

    Without the fix, the last step's ``end`` exceeds ``len(body)``
    because it's a byte position from the SML side.
    """
    body = "strip_tac >> Cases_on ‘x’ >> simp []"
    char_len = len(body)
    byte_len = len(body.encode("utf-8"))
    assert byte_len > char_len, "test setup: body should contain unicode chars"

    steps = await step_plan_json(hol_session, body)
    assert steps, "no steps returned"
    assert steps[-1].end == char_len, (
        f"Last step end {steps[-1].end} should equal Python char length "
        f"{char_len} (byte length {byte_len})."
    )


@pytest.mark.asyncio
async def test_step_plan_offsets_unchanged_without_body(hol_session):
    """Backwards-compat: omitting ``body`` preserves the SML/byte
    positions (existing tests that only count steps still work).
    """
    body = "strip_tac >> Cases_on ‘x’ >> simp []"
    byte_len = len(body.encode("utf-8"))
    steps_bytes = await step_plan_json(hol_session, body, convert=False)
    assert steps_bytes[-1].end == byte_len, (
        f"Without body=, last step end {steps_bytes[-1].end} should equal "
        f"byte length {byte_len}."
    )


# ----------------------------------------------------------------------
# End-to-end: state_at at QED replays full proof on unicode-bearing body
# ----------------------------------------------------------------------


@pytest.mark.asyncio
async def test_state_at_at_qed_replays_full_proof_with_unicode(
    hol_session, tmp_path
):
    """state_at(QED-line) must replay all chunks when the proof body
    contains non-ASCII characters like ``‘``.

    Pre-fix: cursor reports ``replayed < total`` with an open
    residual goal because step.end (bytes) overshoots
    ``len(body)`` (chars), so ``_offset_to_tactic_idx`` breaks early.
    Post-fix: parse_step_plan_output converts byte→char positions,
    so all chunks are recognised at the QED line.
    """
    script = tmp_path / "unicodeScript.sml"
    script.write_text(
        "open HolKernel Parse boolLib bossLib;\n"
        'val _ = new_theory "unicode";\n'
        "\n"
        "Theorem unicode_body:\n"
        "  !x:num. x = x\n"
        "Proof\n"
        "  strip_tac\n"
        "  >> Cases_on ‘x’ >> simp [] >> simp []\n"
        "QED\n"
        "\n"
        "val _ = export_theory();\n"
    )
    cursor = FileProofCursor(script, hol_session)
    await cursor.init()

    thms = [t for t in cursor._theorems if t.name == "unicode_body"]
    assert thms, f"missing theorem: {[t.name for t in cursor._theorems]}"
    thm = thms[0]
    qed_line = thm.proof_end_line - 1  # actual QED keyword line

    result = await cursor.state_at(line=qed_line, col=1)

    proof_complete = (
        result.tactics_total >= 3
        and result.tactics_replayed == result.tactics_total
        and not result.goals
        and (
            result.error is None
            or "no goals" in (result.error or "").lower()
        )
    )
    assert proof_complete, (
        f"state_at at QED reports proof incomplete on body containing "
        f"unicode chars. "
        f"tactic_idx={result.tactic_idx}, "
        f"replayed={result.tactics_replayed}/{result.tactics_total}, "
        f"goals={result.goals!r}, error={result.error!r}"
    )
