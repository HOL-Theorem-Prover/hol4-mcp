"""P2 information tools.

P2a: hol_search — first-class DB.find/DB.match queries.
P2b: hol_goals — goal count, headlines, and slices without top_goals() dumps.
P2c: smart-quote diagnosis (quote_check module + parse-error hookup).
"""

import pytest
from pathlib import Path

from hol4_mcp.quote_check import (
    find_unmatched_quotes,
    fix_unmatched_quotes,
)
from hol4_mcp.hol_mcp_server import (
    hol_start as _hol_start,
    hol_send as _hol_send,
    hol_search as _hol_search,
    hol_goals as _hol_goals,
    hol_state_at as _hol_state_at,
    hol_stop as _hol_stop,
    _init_file_cursor,
    _quote_diagnosis_if_parse_error,
)

hol_start = _hol_start
hol_send = _hol_send
hol_search = _hol_search
hol_goals = _hol_goals
hol_state_at = _hol_state_at
hol_stop = _hol_stop
hol_file_init = _init_file_cursor

FIXTURES_DIR = Path(__file__).parent / "fixtures"


# ---------------------------------------------------------------------------
# P2a: hol_search
# ---------------------------------------------------------------------------

@pytest.mark.asyncio
async def test_hol_search(tmp_path):
    session = "p2a_search_test"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        # Name query
        r = await hol_search(query="CONJ_COMM", session=session)
        assert "match(es)" in r, f"unexpected: {r}"
        assert "CONJ_COMM" in r
        assert "bool." in r

        # Name + theory filter
        r = await hol_search(query="CONJ_COMM", theory="bool", session=session)
        assert "bool.CONJ_COMM" in r

        # Pattern + query intersection
        r = await hol_search(
            query="CONJ", pattern=r"_ /\ _", session=session
        )
        assert "CONJ" in r and "match(es)" in r

        # Statement truncation
        r = await hol_search(
            query="CONJ_COMM", max_statement=10, session=session
        )
        assert "…" in r

        # No match
        r = await hol_search(query="zzqqxyzzyx", session=session)
        assert "No matches." in r

        # Neither query nor pattern
        r = await hol_search(session=session)
        assert r.startswith("ERROR")
    finally:
        await hol_stop(session=session)


# ---------------------------------------------------------------------------
# P2b: hol_goals
# ---------------------------------------------------------------------------

@pytest.mark.asyncio
async def test_hol_goals_live_session(tmp_path):
    session = "p2b_goals_live_test"
    await hol_start(workdir=str(tmp_path), name=session)
    try:
        # No live proof yet
        r = await hol_goals(session=session)
        assert "No live proof" in r, f"unexpected: {r}"

        # Direct goal creation is guarded; establish the same live frontier
        # through file navigation, then test the session-only inspection API.
        blocked = await hol_send(
            session=session, command="g `p /\\ q ==> q /\\ p`;"
        )
        assert "BLOCKED" in blocked
        script = tmp_path / "liveGoalsScript.sml"
        script.write_text(
            "open HolKernel Parse boolLib bossLib;\n"
            "Theorem live_goal:\n  p /\\ q ==> q /\\ p\nProof\n"
            "  strip_tac >>\n  simp[]\nQED\n")
        frontier = await hol_state_at(file=str(script), line=6, col=3, session=session)
        assert "PROOF BROKEN" not in frontier and not frontier.startswith("ERROR"), frontier

        r = await hol_goals(session=session)
        assert "1 goal(s)" in r, f"unexpected: {r}"
        assert "[2 asm]" in r  # strip_tac leaves p, q as assumptions

        r = await hol_goals(n=1, session=session)
        assert "Goal 1 of 1" in r
        assert "asm 1:" in r and "asm 2:" in r

        r = await hol_goals(n=1, asm=1, session=session)
        assert "Goal 1 assumption 1:" in r
        assert r.strip().endswith(("p", "q"))

        # Out-of-range checks
        r = await hol_goals(n=5, session=session)
        assert r.startswith("ERROR")
        r = await hol_goals(n=1, asm=9, session=session)
        assert r.startswith("ERROR")
    finally:
        await hol_stop(session=session)


GOALS_AT_LINE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "p2bgoals";

Theorem two_subgoals:
  T /\\ (T \\/ F)
Proof
  conj_tac >>
  simp[]
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_hol_goals_at_line(tmp_path):
    test_file = tmp_path / "p2bgoalsScript.sml"
    test_file.write_text(GOALS_AT_LINE_SCRIPT)
    session = "p2b_goals_line_test"
    try:
        # After conj_tac (line 9 = start of simp): two goals
        r = await hol_goals(
            file=str(test_file), line=9, col=3, session=session
        )
        assert "2 goal(s)" in r, f"unexpected: {r}"
        assert "at line 9" in r
    finally:
        await hol_stop(session=session)


# ---------------------------------------------------------------------------
# P2c: smart-quote diagnosis
# ---------------------------------------------------------------------------

def test_find_unmatched_quotes():
    # Matched pair: valid term quotation, untouched
    assert find_unmatched_quotes("Cases_on ‘x’ >> simp[]") == []
    # Unmatched close (the classic pasted-apostrophe case)
    bad = "simp[foo’]"
    res = find_unmatched_quotes(bad)
    assert len(res) == 1
    assert res[0][2] == 'close'
    # Unmatched open
    res = find_unmatched_quotes("metis_tac[‘bar]")
    assert len(res) == 1
    assert res[0][2] == 'open'
    # Pair plus a stray: only the stray reported
    res = find_unmatched_quotes("‘x’ and q’")
    assert len(res) == 1
    assert res[0][2] == 'close'


def test_fix_unmatched_quotes(tmp_path):
    f = tmp_path / "quotes.sml"
    f.write_text("val x’ = ‘tm’;\n", encoding="utf-8")
    n = fix_unmatched_quotes(f)
    assert n == 1
    assert f.read_text(encoding="utf-8") == "val x' = ‘tm’;\n"


def test_quote_diagnosis_gating(tmp_path):
    f = tmp_path / "gScript.sml"
    f.write_text("val x’ = T;\n", encoding="utf-8")
    # Non-parse error: no diagnosis even though the file has a stray quote
    assert _quote_diagnosis_if_parse_error(f, "Tactic failed") == []
    # Parse-flavoured error: diagnosis with location and fix command
    out = _quote_diagnosis_if_parse_error(f, "Failed to parse step plan: x")
    assert any("unmatched smart quote" in l for l in out)
    assert any("--fix" in l for l in out)
    # Parse error but clean file: nothing
    f.write_text("val x = T;\n", encoding="utf-8")
    assert _quote_diagnosis_if_parse_error(f, "unknown character") == []


BAD_QUOTE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "p2cquote";

Theorem bad_quote:
  T
Proof
  simp[] >> metis_tac[foo’]
QED

val _ = export_theory();
"""


@pytest.mark.asyncio
async def test_quote_diagnosis_in_state_at(tmp_path):
    """A stray smart quote in a proof body surfaces the quote diagnosis.

    The quote splits the body into two SML declarations, so the step-plan
    coverage check refuses it before the replay; either report is acceptable
    as long as the diagnosis names the quote.
    """
    test_file = tmp_path / "p2cquoteScript.sml"
    test_file.write_text(BAD_QUOTE_SCRIPT, encoding="utf-8")
    session = "p2c_quote_test"
    try:
        # Navigating past the bad step (QED line) produces a parse-flavoured
        # error; the diagnosis must name the stray quote.
        r = await hol_state_at(
            file=str(test_file), session=session, line=9, col=1
        )
        assert "PROOF BROKEN" in r or r.startswith("ERROR"), f"unreported: {r}"
        assert "unmatched smart quote" in r, f"diagnosis missing: {r}"
        assert "--fix" in r
    finally:
        await hol_stop(session=session)


async def test_holmake_detached_mode(tmp_path):
    import asyncio
    import re
    import shutil
    import time as _time
    from hol4_mcp import hol_mcp_server as srv

    for f in FIXTURES_DIR.iterdir():
        if f.is_file():
            shutil.copy(f, tmp_path / f.name)
    t0 = _time.monotonic()
    started = await srv.holmake(workdir=str(tmp_path), target="testTheory", detach=True)
    assert _time.monotonic() - t0 < 2.0, started
    m = re.search(r"job=(\S+)", started)
    assert m and "log" in started, started
    job = m.group(1)

    status = None
    for _ in range(120):
        status = await srv.hol_build_status(job=job)
        if "done" in status:
            break
        assert "running" in status, status
        await asyncio.sleep(1)
    assert status and "done" in status and "Build succeeded" in status, status
    assert (tmp_path / ".hol" / "objs" / "testTheory.dat").exists()

    # cancel kills a running job's process group
    started = await srv.holmake(workdir=str(tmp_path), target="failTheory", detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    cancelled = await srv.hol_build_status(job=job, cancel=True)
    assert "cancelled" in cancelled or "done" in cancelled, cancelled
