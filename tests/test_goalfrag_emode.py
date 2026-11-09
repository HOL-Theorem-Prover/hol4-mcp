"""Regression test for the GOALFRAG e-mode footgun.

hol_state_at leaves the proofManager as a GOALFRAG (needed for ef()/open/close
fine-grained navigation). On a GOALFRAG, the stock proofManagerLib.e/expand
apply a tactic to ALL goals in the current Base (`>>` / THEN semantics), not
the first goal as on a GOALSTACK. So manually driving a navigated proof with
`e` silently misfires per-goal (`>-`/THEN1) tactics across sibling goals
(classically: drule_all -> "Lib.assert: predicate not true").

tactic_prefix.sml installs `safe_e`, and shadows both the top-level `e`/`expand`
and the structure `proofManagerLib` (re-exporting everything, overriding only
e/expand), so that BOTH bare `e` and qualified `proofManagerLib.e`/`.expand`
apply to the FIRST goal only on a goalfrag (classic e-mode) with no goalstate
conversion and all sibling goals left in place. On a goalstack they are the
stock first-goal `e`.

The probe uses a per-goal tactic that closes goal 1 but cannot prove goal 2:
  ACCEPT_TAC (REFL ``0n``)   (* proves 0=0, fails on 1=1 *)
First-goal application -> succeeds, 1 goal remains. All-goals application (the
bug) -> raises on the 1=1 sibling.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_session import HOLSession

SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session_tmpdir(tmp_path):
    session = HOLSession(str(tmp_path))
    await session.start()
    # Loading tactic_prefix.sml installs the safe_e e-mode guard.
    await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=60)
    yield session
    await session.stop()


# Set up a 2-goal GOALFRAG: conj_tac on (0=0)/\(1=1).
_SETUP = (
    "val _ = (proofManagerLib.drop_all (); ()) handle _ => ();"
    "val _ = proofManagerLib.set_goalfrag ([], ``(0n=0)/\\(1n=1)``);"
    "val _ = proofManagerLib.e conj_tac;"
)


def _probe(driver: str) -> str:
    return (
        f"val r = ({driver} (ACCEPT_TAC (REFL ``0n``)); \"OK\") handle _ => \"FAIL\";"
        "val n = (length (proofManagerLib.top_goals ())) handle _ => ~1;"
        'print ("RESULT " ^ r ^ " " ^ Int.toString n ^ "\\n");'
    )


@pytest.mark.asyncio
async def test_bare_e_first_goal_on_goalfrag(hol_session_tmpdir):
    out = await hol_session_tmpdir.send(_SETUP + _probe("e"), timeout=30)
    assert "RESULT OK 1" in out, (
        "bare `e` on a 2-goal GOALFRAG must apply to the first goal only "
        f"(close 0=0, leave 1=1); got: {out[-400:]!r}"
    )


@pytest.mark.asyncio
async def test_qualified_proofmanagerlib_e_first_goal_on_goalfrag(hol_session_tmpdir):
    # The habitual qualified call must be guarded too (structure shadow).
    out = await hol_session_tmpdir.send(_SETUP + _probe("proofManagerLib.e"), timeout=30)
    assert "RESULT OK 1" in out, (
        "`proofManagerLib.e` on a 2-goal GOALFRAG must apply to the first goal "
        f"only; got: {out[-400:]!r}"
    )


@pytest.mark.asyncio
async def test_e_classic_on_goalstack(hol_session_tmpdir):
    # On a GOALSTACK, behaviour is the stock first-goal `e` (unchanged).
    setup_gs = (
        "val _ = (proofManagerLib.drop_all (); ()) handle _ => ();"
        "val _ = proofManagerLib.set_goal ([], ``(0n=0)/\\(1n=1)``);"
        "val _ = proofManagerLib.e conj_tac;"
    )
    out = await hol_session_tmpdir.send(setup_gs + _probe("e"), timeout=30)
    assert "RESULT OK 1" in out, (
        f"`e` on a 2-goal GOALSTACK must apply to the first goal; got: {out[-400:]!r}"
    )
