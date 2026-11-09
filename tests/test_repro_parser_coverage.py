"""Reproductions for two parser/taint gaps (MCP_BUGS_review.md #2 and #12).

Finding #2 — unbalanced delimiters silently truncate the step plan
=================================================================

The Python file parser locates a block's ``QED`` TEXTUALLY, so
``proof_body`` keeps everything up to that line, a surplus ``)``
included.  The SML side (``goalfrag_step_plan_json`` →
``parseTacticBlockFromString``) takes the FIRST declaration
``HOLSourceParser.parseSML`` yields and never checks that the parse
consumed the whole body, so the surplus ``)`` ends the expression early
and every tactic after it is dropped from the plan.  Python accepts the
plan with no coverage check.

Consequences pinned here:

  - the plan for a body whose file form does not parse silently omits
    later tactics (``test_step_plan_does_not_silently_drop_tactics``);
  - ``hol_state_at`` on such a block replays the truncated prefix,
    finds no residual goal and reports the proof COMPLETE
    (``test_state_at_does_not_report_unparsable_block_complete``);
  - that report contradicts what navigating to the NEXT block says,
    which is where the broken text actually reaches HOL
    (``test_complete_report_consistent_with_next_block_load``).

Finding #12 — proof-state-mutator taint regex misses bare drivers
================================================================

``_PROOFMGR_MUTATING_RE`` matches qualified ``proofManagerLib.eall`` and
a bare-driver list ``e|ef|expand|…``, but the bare escape hatches
``eall``/``enth``/``ee``/``eta`` match neither alternative, so a
``hol_send`` of one mutates the live goal stack without tainting the
cursor (``test_bare_goalstack_drivers_taint_session``).

Every test asserts the CORRECT behaviour and is expected to FAIL until
the findings are fixed.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import escape_sml_string
from hol4_mcp.hol_file_parser import (
    HOLParseError, parse_file, parse_step_plan_output,
)
from hol4_mcp.hol_mcp_server import (
    _command_mutates_proof_state,
    _init_file_cursor,
    hol_state_at as _hol_state_at,
    hol_stop as _hol_stop,
)

hol_state_at = _hol_state_at
hol_stop = _hol_stop
hol_file_init = _init_file_cursor

FIXTURES_DIR = Path(__file__).parent / "fixtures"
END_FIXTURE = FIXTURES_DIR / "repro_parser_surplus_endScript.sml"
MID_FIXTURE = FIXTURES_DIR / "repro_parser_surplus_midScript.sml"

COMPLETE_MARKER = "No goals (proof complete)"


def _block(path: Path, name: str):
    """Return the parsed block called ``name`` from ``path``."""
    blocks = [t for t in parse_file(path) if t.name == name]
    assert blocks, f"{name} not found in {path.name}: " \
                   f"{[t.name for t in parse_file(path)]}"
    return blocks[0]


def _qed_line(block) -> int:
    """Line of the block's ``QED`` keyword."""
    return block.proof_end_line - 1


# ----------------------------------------------------------------------
# Finding #2, plan level: a body that does not parse must not yield a
# plan that silently omits the tactics after the bad delimiter.
# ----------------------------------------------------------------------


async def test_step_plan_does_not_silently_drop_tactics(hol_session):
    """The body does not parse, so no plan can cover it — the requirement is
    that the shortfall is REPORTED rather than handed back as a short plan."""
    block = _block(MID_FIXTURE, "mid_surplus[pp_case]")
    body = block.proof_body
    in_body = body.count("ASM_REWRITE_TAC")
    assert in_body == 2, f"fixture setup: expected 2 arms, body={body!r}"

    escaped = escape_sml_string(body)
    out = await hol_session.send(
        f'goalfrag_step_plan_json "{escaped}";', timeout=15
    )
    try:
        steps = parse_step_plan_output(out, body)
    except HOLParseError:
        return  # reported, which is the correct outcome

    in_plan = sum(s.text.count("ASM_REWRITE_TAC") for s in steps)
    assert in_plan == in_body, (
        f"step plan covers only {in_plan} of the {in_body} tactics in the "
        f"body and no error was raised; the text after the surplus ')' was "
        f"dropped silently. plan={[(s.kind, s.text, s.end) for s in steps]}, "
        f"len(body)={len(body)}"
    )


# ----------------------------------------------------------------------
# Finding #2, end to end: the truncated prefix replays and completes.
# ----------------------------------------------------------------------


async def test_state_at_does_not_report_unparsable_block_complete():
    block = _block(END_FIXTURE, "end_surplus[p_case]")
    assert block.proof_body.rstrip().endswith("))"), \
        f"fixture setup: expected a surplus ')', body={block.proof_body!r}"

    session = "repro_parser_end_complete"
    try:
        await hol_file_init(file=str(END_FIXTURE), session=session)
        r = await hol_state_at(session=session, line=_qed_line(block), col=1)
    finally:
        await hol_stop(session=session)

    assert COMPLETE_MARKER not in r, (
        "state_at reports the proof complete for a block whose file text "
        f"does not parse (surplus ')'). output:\n{r}"
    )


async def test_complete_report_consistent_with_next_block_load():
    first = _block(END_FIXTURE, "end_surplus[p_case]")
    second = _block(END_FIXTURE, "end_surplus[q_case]")

    session = "repro_parser_end_consistency"
    try:
        await hol_file_init(file=str(END_FIXTURE), session=session)
        r_first = await hol_state_at(session=session, line=_qed_line(first), col=1)
        r_second = await hol_state_at(session=session, line=_qed_line(second), col=1)
    finally:
        await hol_stop(session=session)

    reported_complete = COMPLETE_MARKER in r_first
    next_block_broken = (
        "parse error" in r_second.lower()
        or "expected 'QED'" in r_second
        or "expected 'qed'" in r_second.lower()
    )

    assert not (reported_complete and next_block_broken), (
        "contradictory reports for the same block text: state_at on "
        f"{first.name} said the proof is complete, but loading "
        f"{second.name} failed to parse it.\n"
        f"--- {first.name} ---\n{r_first}\n"
        f"--- {second.name} ---\n{r_second}"
    )


# ----------------------------------------------------------------------
# Finding #12: bare goal-stack drivers must taint the session.
# ----------------------------------------------------------------------


@pytest.mark.parametrize(
    "command",
    [
        "eall (simp[])",
        "enth (simp[]) 1",
        "ee (simp[])",
        "eta (simp[])",
    ],
)
def test_bare_goalstack_drivers_taint_session(command):
    assert _command_mutates_proof_state(command), (
        f"{command!r} mutates the live proofManager goal stack but is not "
        f"recognised as a proof-state mutator, so the next state_at reuses "
        f"the polluted live state"
    )
