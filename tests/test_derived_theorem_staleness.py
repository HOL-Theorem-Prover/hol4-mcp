"""A fixed `Theorem name = <derivation>` must be honoured by later theorems.

Derived theorems (`Theorem foo = <rule application>`, no `Proof`/`QED`) are
ordinary file content: editing one changes what every later proof sees. The
partial-reload path truncates ``_loaded_to_line`` to the change point, so the
derivation should be re-executed and rebound on the next navigation.

Regression: after editing such a derivation, a later theorem that consumes it
kept replaying against the PRE-EDIT value, so a genuine fix to the derivation
looked like it had no effect and the consumer stayed broken.

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


# `derived` is a one-line derivation, so USER_QED_LINE is stable across versions.
def _script(derivation: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"     # 1
        "\n"                                          # 2
        'val _ = new_theory "derivstale";\n'          # 3
        "\n"                                          # 4
        "Theorem base:\n"                             # 5
        "  T\n"                                       # 6
        "Proof\n"                                     # 7
        "  simp[]\n"                                  # 8
        "QED\n"                                       # 9
        "\n"                                          # 10
        f"Theorem derived = {derivation}\n"           # 11
        "\n"                                          # 12
        "Theorem user:\n"                             # 13
        "  T /\\ T\n"                                 # 14
        "Proof\n"                                     # 15
        "  ACCEPT_TAC derived\n"                      # 16
        "QED\n"                                       # 17
        "\n"                                          # 18
        "val _ = export_theory();\n"                  # 19
    )


USER_QED_LINE = 17
_TOO_WEAK = "base"                 # derived : T          -> `user` cannot close
_CORRECT = "CONJ base base"        # derived : T /\ T     -> `user` closes


def _is_proof_complete(res) -> bool:
    return bool(
        not res.goals
        and res.tactics_replayed == res.tactics_total
        and (res.error is None or "no goals" in res.error.lower())
    )


@pytest.mark.asyncio
async def test_edited_derivation_is_rebound_for_later_theorem(
    hol_session_tmpdir, tmp_path: Path
):
    script = tmp_path / "derivstaleScript.sml"

    # 1. Derivation too weak: `user` cannot close against it.
    script.write_text(_script(_TOO_WEAK))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()

    res_bad = await cursor.state_at(USER_QED_LINE, 1)
    assert not _is_proof_complete(res_bad), (
        "sanity: `user` must NOT close while `derived` is too weak"
    )

    # 2. Fix the derivation only — same cursor/session, no restart. `user` is
    #    unchanged text, but must now be replayed against the NEW `derived`.
    script.write_text(_script(_CORRECT))
    res_good = await cursor.state_at(USER_QED_LINE, 1)

    assert _is_proof_complete(res_good), (
        "`user` still fails after `derived` was fixed — it replayed against the "
        f"stale pre-edit derivation: error={res_good.error!r} "
        f"replayed={res_good.tactics_replayed}/{res_good.tactics_total} "
        f"goals={res_good.goals!r}"
    )
