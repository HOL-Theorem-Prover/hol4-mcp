"""Tests for realizing operand-spanning atoms as tactics in the step plan.

`by` and `rename` are parsed by TacticParse into atoms whose span is only an
OPERAND (a term quotation / a quotation list), not a runnable tactic:

    `P` by tac        ->  Subgoal (span = `P`)          -- needs an `sg ` prefix
    >>~- ([pat], t)   ->  Group(false, pat, Rename pat) -- needs `Q.RENAME_TAC `

while the application forms already span a complete tactic and must be left
alone:

    sg `P` / subgoal `P`   ->  Group(true, <whole call>, Subgoal _)
    rename [pat]           ->  Group(true, <whole call>, Rename _)

`Group`'s first field is exactly that distinction (TacticParse `group tac a b`),
so it — not the first character of the span — decides whether a prefix is added.
Sniffing for an ASCII backtick misses `‘…’` / `“…”`, which is what CakeML and
most modern HOL4 sources use.
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
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower()
    yield session
    await session.stop()


async def call_step_plan(session, tactic_str):
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'goalfrag_step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(result)


async def execute_steps(session, steps, goal):
    """Run a step plan on `goal`; -1 means a step raised (e.g. a type error)."""
    await session.send('drop_all();', timeout=5)
    await session.send(f'gf `{goal}`;', timeout=10)
    for step in steps:
        r = await session.send(step.cmd, timeout=10)
        if "Exception-" in r or "error:" in r or "poly:" in r or "Type error" in r:
            return -1
    r = await session.send('goals_json();', timeout=10)
    for line in r.strip().split('\n'):
        if line.startswith('{"ok":'):
            return len(json.loads(line)['ok'])
    return -1


async def remaining_goals(session, steps, goal):
    """Run a step plan on `goal`; return the surviving goals' conclusions.

    None means a step raised. Goal count alone cannot tell `by` from
    `suffices_by` — both leave one goal — so the conclusions are the evidence.
    """
    await session.send('drop_all();', timeout=5)
    await session.send(f'gf `{goal}`;', timeout=10)
    for step in steps:
        r = await session.send(step.cmd, timeout=20)
        if "Exception-" in r or "error:" in r or "poly:" in r or "Type error" in r:
            return None
    r = await session.send('goals_json();', timeout=10)
    for line in r.strip().split('\n'):
        if line.startswith('{"ok":'):
            return [g["goal"] for g in json.loads(line)['ok']]
    return None


def texts(steps):
    return [s.text for s in steps]


def unquote(t):
    """Normalise every term-quotation delimiter to the ASCII backtick."""
    for c in "‘’“”":
        t = t.replace(c, "`")
    return t


def bare_quotations(steps):
    """Steps that are nothing but a term quotation — not a runnable tactic."""
    out = []
    for t in texts(steps):
        s = unquote(t).strip()
        if len(s) >= 2 and s.startswith("`") and s.endswith("`"):
            out.append(t)
    return out


# ---------------------------------------------------------------------------
# `Q` by tac — the Subgoal atom spans only the quotation
# ---------------------------------------------------------------------------

ASCII_BY = "`T` by SIMP_TAC bool_ss []"
UNICODE_BY = "‘T’ by SIMP_TAC bool_ss []"

# The shape real sources use: mid-chain, with a parenthesised `by` body.
CHAIN_ASCII_BY = "rpt strip_tac \\\\ `T` by (ALL_TAC \\\\ SIMP_TAC bool_ss [])"
CHAIN_UNICODE_BY = "rpt strip_tac \\\\ ‘T’ by (ALL_TAC \\\\ SIMP_TAC bool_ss [])"


class TestSubgoalByRealization:
    async def test_ascii_by_merges_to_one_step(self, hol_session):
        """Control: the ASCII form is realized and merged into one atomic step."""
        steps = await call_step_plan(hol_session, ASCII_BY)
        assert texts(steps) == [ASCII_BY], texts(steps)

    async def test_unicode_by_merges_to_one_step(self, hol_session):
        """Unicode quotes must behave identically to the ASCII control."""
        steps = await call_step_plan(hol_session, UNICODE_BY)
        assert texts(steps) == [UNICODE_BY], texts(steps)

    async def test_no_bare_quotation_step(self, hol_session):
        """A bare term quotation is not a tactic: handing it to goalFrag.expand
        is a Poly/ML 'Type error in function application'."""
        steps = await call_step_plan(hol_session, UNICODE_BY)
        assert not bare_quotations(steps), texts(steps)

    async def test_unicode_by_executes(self, hol_session):
        steps = await call_step_plan(hol_session, UNICODE_BY + " \\\\ ASM_REWRITE_TAC []")
        assert await execute_steps(hol_session, steps, "T") == 0

    async def test_chain_quote_style_does_not_change_the_plan(self, hol_session):
        """The mid-chain, parenthesised-body shape real sources use. Quote
        style is not semantics: both plans must be identical."""
        ascii_steps = await call_step_plan(hol_session, CHAIN_ASCII_BY)
        uni_steps = await call_step_plan(hol_session, CHAIN_UNICODE_BY)
        assert [unquote(t) for t in texts(uni_steps)] == \
               [unquote(t) for t in texts(ascii_steps)]

    async def test_chain_unicode_by_has_no_bare_quotation(self, hol_session):
        steps = await call_step_plan(hol_session, CHAIN_UNICODE_BY)
        assert not bare_quotations(steps), texts(steps)

    async def test_chain_unicode_by_executes_like_ascii(self, hol_session):
        ascii_steps = await call_step_plan(hol_session, CHAIN_ASCII_BY)
        expected = await execute_steps(hol_session, ascii_steps, "T")
        assert expected >= 0, "ASCII control itself failed to execute"
        uni_steps = await call_step_plan(hol_session, CHAIN_UNICODE_BY)
        assert await execute_steps(hol_session, uni_steps, "T") == expected

    async def test_unicode_by_after_multi_goal_split(self, hol_session):
        """`Q` by tac must stay ONE atomic step so it distributes per goal.

        Decomposed as [sg Q, open_then1, tac, close] only the FIRST goal's
        subgoal is discharged; the rest stay open (see merge_by_steps)."""
        tac = "conj_tac \\\\ " + UNICODE_BY + " \\\\ ASM_REWRITE_TAC []"
        steps = await call_step_plan(hol_session, tac)
        assert await execute_steps(hol_session, steps, "T /\\ T") == 0


# ---------------------------------------------------------------------------
# rename [pat] — the Group spans the whole call, so it is ALREADY a tactic
# ---------------------------------------------------------------------------

RENAME_CALL = "rename [‘y = y’]"
SELECT_THEN = "conj_tac >>~- ([‘T’], SIMP_TAC bool_ss [])"


class TestRenameRealization:
    async def test_rename_call_kept_verbatim(self, hol_session):
        """`rename [pat]` is a complete tactic; prefixing it yields
        `Q.RENAME_TAC rename [pat]` — a function applied to a tactic."""
        steps = await call_step_plan(hol_session, RENAME_CALL)
        assert texts(steps) == [RENAME_CALL], texts(steps)

    async def test_renamed_tac_call_kept_verbatim(self, hol_session):
        call = "Q.RENAME_TAC [‘y = y’]"
        steps = await call_step_plan(hol_session, call)
        assert texts(steps) == [call], texts(steps)

    async def test_rename_call_executes(self, hol_session):
        steps = await call_step_plan(hol_session, RENAME_CALL + " \\\\ REFL_TAC")
        assert await execute_steps(hol_session, steps, "x = x") == 0

    async def test_select_arm_still_prefixed(self, hol_session):
        """Regression guard: in `>>~- ([pat], tac)` the span IS just the
        pattern, so it still needs the Q.RENAME_TAC prefix."""
        steps = await call_step_plan(hol_session, SELECT_THEN)
        prefixed = [t for t in texts(steps) if t.startswith("Q.RENAME_TAC ")]
        assert prefixed, texts(steps)
        assert prefixed[0] == "Q.RENAME_TAC [‘T’]", prefixed

    async def test_select_then_still_executes(self, hol_session):
        steps = await call_step_plan(hol_session, SELECT_THEN)
        assert await execute_steps(hol_session, steps, "T /\\ T") == 0


# ---------------------------------------------------------------------------
# `Q` suffices_by tac — the operand span arrives as a ThenLT, not a Subgoal
# ---------------------------------------------------------------------------
#
# TacticParse (src/parse/TacticParse.sml) elaborates the two `by` flavours
# differently:
#
#     `Q` by tac           ->  ThenLT (Subgoal Q, [LThen1 tac])
#     `Q` suffices_by tac  ->  ThenLT (group false Q (ThenLT (Subgoal Q,
#                                                             [LReverse])),
#                                      [LThen1 tac])
#
# Both spans cover only the quotation, but unwrapping the second reaches a
# ThenLT rather than a bare Subgoal, so a `Subgoal`-only realization drops
# through to the catch-all and emits the raw quotation. `goalFrag.expand`
# takes a tactic, so the step dies as a Poly/ML "Type error in function
# application" pointing at a line of perfectly good HOL.
#
# Use Q_TAC SUFF_TAC, like BasicProvers.suffices_by. Reversed sg leaves the
# same final goal, but gives the closer stripped assumptions, not Q ==> G.

SUFFICES = "`q ∧ p` suffices_by metis_tac[]"
SUFFICES_UNICODE = "‘q ∧ p’ suffices_by metis_tac[]"
# Mid-chain the whole form merges into one step; standalone it decomposes.
SUFFICES_CHAIN = "ALL_TAC \\\\ `q ∧ p` suffices_by metis_tac[]"


class TestSufficesByRealization:
    @pytest.mark.parametrize("quotes", [("`", "`"), ("‘", "’")])
    async def test_cakeml_existential_assertion_agrees_with_native(self, hol_session, quotes):
        # The assertion from completeness's nPTbase arm. Fix its otherwise
        # polymorphic token/location types through the parked goal.
        assertion = "∃e l t. pfx ++ sfx = (e,l)::t ∧ e ≠ LparT ∧ ¬isTyvarT e"
        goal = assertion.replace("pfx ++", "(pfx : (num # num) list) ++")
        quotation = quotes[0] + assertion + quotes[1]
        source = quotation + " suffices_by (strip_tac >> metis_tac[])"
        steps = await call_step_plan(hol_session, source)
        actual = await remaining_goals(hol_session, steps[:1], goal)
        assert actual is not None and len(actual) == 2
        actual_json = await hol_session.send('goals_json();', timeout=10)
        await hol_session.send(f'drop_all(); gf `{goal}`;', timeout=10)
        native = await hol_session.send(
            f'ef(goalFrag.expand (Q_TAC SUFF_TAC {quotation}) (Context.snapshot()));', timeout=10)
        assert "Exception-" not in native and "error:" not in native, native
        assert actual_json == await hol_session.send('goals_json();', timeout=10)
        # Run the stripping closer too; compare assumptions as well as goals.
        assert await remaining_goals(hol_session, steps, goal) is not None
        actual_json = await hol_session.send('goals_json();', timeout=10)
        await hol_session.send(f'drop_all(); gf `{goal}`;', timeout=10)
        native = await hol_session.send(f'ef(goalFrag.expand ({source}) (Context.snapshot()));', timeout=10)
        assert "Exception-" not in native and "error:" not in native, native
        assert actual_json == await hol_session.send('goals_json();', timeout=10)

    @pytest.mark.parametrize("quotation", ["`q ∧ p`", "‘q ∧ p’"])
    async def test_closer_receives_native_implication(self, hol_session, quotation):
        steps = await call_step_plan(
            hol_session, quotation + " suffices_by (strip_tac >> simp[])")
        actual = await remaining_goals(hol_session, steps[:1], "p ∧ q")
        assert actual == ["q ∧ p ⇒ p ∧ q", "q ∧ p"], (texts(steps), actual)
        actual_json = await hol_session.send('goals_json();', timeout=10)
        await hol_session.send('drop_all(); gf `p ∧ q`;', timeout=10)
        native = await hol_session.send(
            f'ef(goalFrag.expand (Q_TAC SUFF_TAC {quotation}) (Context.snapshot()));', timeout=10)
        assert "Exception-" not in native and "error:" not in native, native
        native_json = await hol_session.send('goals_json();', timeout=10)
        assert actual_json == native_json

    @pytest.mark.parametrize("prefix", ["", "ALL_TAC \\\\", "conj_tac \\\\"])
    async def test_strip_closer_agrees_with_native(self, hol_session, prefix):
        source = prefix + " ‘q ∧ p’ suffices_by (strip_tac >> simp[])"
        goal = "p ∧ p" if prefix.startswith("conj_tac") else "p:bool"
        steps = await call_step_plan(hol_session, source)
        actual = await remaining_goals(hol_session, steps, goal)
        await hol_session.send('drop_all();', timeout=10)
        await hol_session.send(f'gf `{goal}`;', timeout=10)
        native = await hol_session.send(f'ef(goalFrag.expand ({source}) (Context.snapshot()));', timeout=10)
        assert "Exception-" not in native and "error:" not in native, native
        expected = await hol_session.send('goals_json();', timeout=10)
        expected = next(json.loads(l)['ok'] for l in expected.splitlines()
                        if l.startswith('{"ok":'))
        assert actual == [g['goal'] for g in expected], (texts(steps), actual)

    async def test_no_bare_quotation_step(self, hol_session):
        steps = await call_step_plan(hol_session, SUFFICES)
        assert not bare_quotations(steps), texts(steps)

    async def test_unicode_form_has_no_bare_quotation(self, hol_session):
        steps = await call_step_plan(hol_session, SUFFICES_UNICODE)
        assert not bare_quotations(steps), texts(steps)

    async def test_plan_executes(self, hol_session):
        steps = await call_step_plan(hol_session, SUFFICES)
        assert await remaining_goals(hol_session, steps, "p ∧ q") is not None

    async def test_leaves_the_sufficient_goal_not_the_original(self, hol_session):
        """The discriminating check: `by` semantics would leave `p ∧ q`."""
        steps = await call_step_plan(hol_session, SUFFICES)
        assert await remaining_goals(hol_session, steps, "p ∧ q") == ["q ∧ p"]

    async def test_decomposed_form_agrees_with_merged_chain_form(self, hol_session):
        """Whether the form merges into one step depends on its context; the
        goal it leaves must not."""
        chain = await call_step_plan(hol_session, SUFFICES_CHAIN)
        expected = await remaining_goals(hol_session, chain, "p ∧ q")
        assert expected == ["q ∧ p"], expected
        standalone = await call_step_plan(hol_session, SUFFICES)
        assert await remaining_goals(hol_session, standalone, "p ∧ q") == expected

    async def test_by_control_is_unchanged(self, hol_session):
        """`by` must keep its own realization — the two must not converge."""
        steps = await call_step_plan(hol_session, "`T` by SIMP_TAC bool_ss []")
        assert texts(steps) == ["`T` by SIMP_TAC bool_ss []"], texts(steps)
