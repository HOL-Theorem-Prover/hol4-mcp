"""Tests for raised-exception reporting in state_at (MCP Bug B).

When replay stops on a RAISED EXCEPTION (e.g. a qpat_x_assum / qmatch whose
pattern no longer matches -> HOL_ERR), the failing-step pin is only where
replay halted, not a confident fault site. The report must say so and must
not present a sound tactic as 'FAILED'.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_mcp_server import (
    _is_raised_exception,
    _exception_advisory_lines,
)
from hol4_mcp.hol_cursor import FileProofCursor
from hol4_mcp.hol_session import HOLSession

FIXTURES_DIR = Path(__file__).parent / "fixtures"
EXC_FIXTURE = FIXTURES_DIR / "raiseExcScript.sml"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


# --- pure classification ---------------------------------------------------

def test_is_raised_exception_classification():
    assert _is_raised_exception("Tactic replay failed: ... Exception- HOL_ERR ...")
    assert _is_raised_exception("uncaught exception: raised exception in tactic")
    assert not _is_raised_exception("Tactic replay timed out (>120s)")
    assert not _is_raised_exception("TIMEOUT after 120s - sent interrupt.")
    assert not _is_raised_exception(None)
    assert not _is_raised_exception("proof incomplete (2 goals remaining)")


def test_exception_advisory_mentions_match_tactics():
    out = "\n".join(_exception_advisory_lines("Exception- HOL_ERR foo"))
    assert "RAISED EXCEPTION" in out
    assert "qpat" in out.lower() or "qmatch" in out.lower()
    # The advisory must say the pin is only where replay stopped.
    assert "earlier" in out.lower()


# --- integration via FileProofCursor (the real replay path) ----------------
# The tool layer (@mcp.tool()) is unusable under the pytest env's FastMCP
# version, so drive the cursor directly: a qpat_x_assum no-match raises HOL_ERR
# during replay, and that error must classify as a raised exception so the
# formatter softens its report.

@pytest.fixture
async def cursor(tmp_path):
    session = HOLSession(str(tmp_path))
    await session.start()
    await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
    c = FileProofCursor(EXC_FIXTURE, session, checkpoint_dir=tmp_path / "checkpoints")
    await c.init()
    yield c
    await session.stop()


async def test_replay_failure_is_classified_as_exception(cursor):
    qed_line = next(
        i for i, l in enumerate(EXC_FIXTURE.read_text().splitlines(), 1)
        if l.strip() == "QED"
    )
    result = await cursor.state_at(line=qed_line)
    # Replay must fail (the qpat_x_assum `F` matches nothing).
    assert result.error, "expected replay to fail on the no-match qpat"
    # And it must be recognized as a RAISED EXCEPTION, which drives the
    # softened reporting (vs a confident step pin).
    assert _is_raised_exception(result.error), result.error
