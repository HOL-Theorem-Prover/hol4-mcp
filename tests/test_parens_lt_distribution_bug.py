"""Regression tests for the parens-around-LT distribution bug:

  Group(span, ThenLT(_, [LThen1 _]))    — parens around `>-`
  Group(span, ThenLT(_, [LNullOk (LTacsToLT _)])) — parens around `>|`

When the parenthesised form sits inside a `\\` chain, Holmake distributes
the parenthesised tactic per source goal of the outer `\\`. Without the
fix, `reexpand_group_atoms` would re-expand the Group, producing the same
flat fragment sequence as the un-parenthesised form, so the MCP would
run `open_then1` (or the `>|` equivalent) GLOBALLY against the first
goal, not per-source.

Fix (commit on this branch): `isComposable` excludes ThenLT whose ls
contains a goal-positional LT operator (LThen1 / LFirst / LTacsToLT /
LSplit, including those wrapped in LNullOk / LRepeat / LTry / LFirstLT).
The Group stays as a single FAtom and goalFrag.expand runs the whole
parenthesised tactic atomically per source goal — matches Holmake.

Trade-off: lose mid-arm navigation INSIDE parens-grouped LT chains
(can't place cursor between TAC1 and TAC2 inside `(TAC1 >- TAC2)`).
The un-parenthesised form retains its decomposition and full navigation.

Empirical verification (against `(T /\\ T) /\\ (T /\\ T)`):

  parens  `conj_tac \\\\ (conj_tac >- ACCEPT_TAC TRUTH)`  → 2 goals (correct)
  unparens `conj_tac \\\\ conj_tac >- ACCEPT_TAC TRUTH`   → 3 goals (correct)

Real-world trigger: cake-while `evaluate_sf_gc_consts[Call]` after
inlining Resume[Result]. Pre-fix: Holmake builds, hol_check_proof
reports residue. Post-fix: both agree.
"""

import pytest
import json
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    result = await session.send(
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30
    )
    assert "error" not in result.lower()
    yield session
    await session.stop()


async def call_step_plan(session, tactic_str):
    escaped = escape_sml_string(tactic_str)
    result = await session.send(
        f'goalfrag_step_plan_json "{escaped}";', timeout=10
    )
    return parse_step_plan_output(result)


async def goal_count(session):
    """Read length(top_goals()) from the running proof."""
    r = await session.send('print (Int.toString (length (top_goals())) ^ "\\n");',
                            timeout=10)
    # Take the last numeric line.
    for line in reversed(r.strip().split('\n')):
        s = line.strip()
        if s.isdigit():
            return int(s)
    raise AssertionError(f"no goal count in: {r!r}")


async def test_parens_then1_step_plan_distinct_from_unparens(hol_session):
    """The parens form `(TAC1 >- TAC2)` should produce a DIFFERENT step
    plan from the no-parens `TAC1 >- TAC2` form, because they have
    different per-goal-distribution semantics under a surrounding `\\`.

    Currently both forms produce the same flat decomposition, which
    matches no-parens semantics and breaks the parens case."""
    parens = await call_step_plan(
        hol_session, "conj_tac \\\\ (conj_tac >- ACCEPT_TAC TRUTH)"
    )
    no_parens = await call_step_plan(
        hol_session, "conj_tac \\\\ conj_tac >- ACCEPT_TAC TRUTH"
    )
    parens_kinds = [s.kind for s in parens]
    no_parens_kinds = [s.kind for s in no_parens]
    # When the bug is fixed: parens form should NOT contain `open_then1` /
    # `close_paren` (the `>-` should be embedded in a single atomic expand
    # step `(conj_tac >- ACCEPT_TAC TRUTH)`).
    assert parens_kinds != no_parens_kinds, (
        f"parens and no-parens produce identical step kinds — bug present: "
        f"parens={parens_kinds}, no_parens={no_parens_kinds}"
    )
    # Specifically, parens form should be 2 expand steps (conj_tac, then the
    # whole grouped tactic).
    assert len(parens) == 2, (
        f"parens form should merge to 2 atomic steps; got {len(parens)}: "
        f"{[(s.kind, s.text) for s in parens]}"
    )


async def test_parens_then1_executes_per_goal_under_then(hol_session):
    """End-to-end execution: source form `conj_tac \\\\ (conj_tac >- ACCEPT_TAC TRUTH)`
    on `(T /\\ T) /\\ (T /\\ T)` should leave 2 goals (each source `T /\\ T`
    closes its first conjunct, leaves the second). Holmake confirms this.

    The MCP-decomposed plan currently leaves 3 goals — close 1 of 4
    globally instead of 1 per source."""
    plan = await call_step_plan(
        hol_session, "conj_tac \\\\ (conj_tac >- ACCEPT_TAC TRUTH)"
    )
    await hol_session.send('drop_all();', timeout=5)
    await hol_session.send('gf `(T /\\ T) /\\ (T /\\ T)`;', timeout=10)
    for step in plan:
        r = await hol_session.send(step.cmd, timeout=10)
        assert "Exception-" not in r, f"step failed: {step.cmd} → {r}"
    n = await goal_count(hol_session)
    assert n == 2, (
        f"parens form should leave 2 goals (per-goal semantics); MCP gave {n}"
    )


async def test_parens_thenL_executes_per_goal_under_then(hol_session):
    """Same mechanism for `>|` (LTacsToLT). Source form
    `conj_tac \\\\ (conj_tac >| [ACCEPT_TAC TRUTH, ACCEPT_TAC TRUTH])`
    on `(T /\\ T) /\\ (T /\\ T)` closes the proof per Holmake (per-source
    `>|` matches arity 2). The MCP plan runs `>|` globally on 4 goals,
    raising HOL_ERR (lists of different length)."""
    plan = await call_step_plan(
        hol_session,
        "conj_tac \\\\ (conj_tac >| [ACCEPT_TAC TRUTH, ACCEPT_TAC TRUTH])"
    )
    await hol_session.send('drop_all();', timeout=5)
    await hol_session.send('gf `(T /\\ T) /\\ (T /\\ T)`;', timeout=10)
    last_err = None
    for step in plan:
        r = await hol_session.send(step.cmd, timeout=10)
        if "Exception-" in r:
            last_err = r
            break
    if last_err is not None:
        raise AssertionError(
            f"MCP plan raised exception (arity mismatch from global >|); "
            f"Holmake parens form closes the proof. Trace: {last_err!r}"
        )
    n = await goal_count(hol_session)
    assert n == 0, (
        f"parens >| form should close all goals; MCP gave {n}"
    )


async def test_unparens_then1_unchanged_correct(hol_session):
    """Sanity: the un-parenthesised form `TAC1 >- TAC2` (no Group wrapper)
    has the un-merged decomposition that's CORRECT (matches HOL4 left-assoc
    parse). This test passes today and must continue passing after the fix.

    Goal: `(T /\\ T) /\\ (T /\\ T)`. Source: `conj_tac \\\\ conj_tac >- ACCEPT_TAC TRUTH`
    parses as `((conj_tac \\\\ conj_tac) >- ACCEPT_TAC TRUTH)` — runs >-
    once globally on 4 sub-goals, leaves 3."""
    plan = await call_step_plan(
        hol_session, "conj_tac \\\\ conj_tac >- ACCEPT_TAC TRUTH"
    )
    await hol_session.send('drop_all();', timeout=5)
    await hol_session.send('gf `(T /\\ T) /\\ (T /\\ T)`;', timeout=10)
    for step in plan:
        r = await hol_session.send(step.cmd, timeout=10)
        assert "Exception-" not in r, f"step failed: {step.cmd} → {r}"
    n = await goal_count(hol_session)
    assert n == 3, f"unparens form should leave 3 goals (global >-); got {n}"
