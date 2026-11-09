"""An edit inside a BROKEN suspend/Resume chain must not discard the whole
file's cached state or force a session restart.

``_reparse_if_changed`` used to answer a broken chain (a member auto-cheated
at load, so its children are orphaned — "No such label") with a FULL session
reinit: HOL restarted, dependencies reloaded, prefix replayed from line 1.
The premise was that the session-global suspension store cannot be partially
rolled back. That was true when the edit path only lowered a Python line
counter and re-sent into the live heap; it is not true now that an edit
truncating the loaded prefix rewinds to the predecessor's context checkpoint
(``_context_rewind_pending``). A context checkpoint is a Poly/ML heap image
taken after each prefix theorem; loading it restores markerLib's two stores
to exactly the state they had before the edited block first ran, so the
fixed block re-registers its children on the ordinary partial path.

The cost of the old behaviour scaled with the file, not the edit: on an
11,000-line script every edit inside the chain paid ~200s of restart +
dependency reload + prefix resend for 2-15s of actual replay — and the
guidance for a failing arm (sub-suspend it and iterate on it) keeps the arm
red between edits, so the penalty recurred on every edit until it proved.

The pure tests drive the parsed-state bookkeeping with no HOL session. The
integration test pins the guarantee the reinit was protecting: a fixed
dispatcher's orphaned child comes back — and now without a restart.
"""

import re
import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import (
    FileProofCursor, SessionPosition, TheoremCheckpoint,
)
from hol4_mcp.hol_session import HOLSession


SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


# ---------------------------------------------------------------------------
# Pure tests: parsed-state bookkeeping only (session=None).
# ---------------------------------------------------------------------------

def _chain_script(c2_body: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib markerLib;\n"   # 1
        "\n"                                                   # 2
        'val _ = new_theory "brokenchain";\n'                 # 3
        "\n"                                                   # 4
        "Theorem lemma_before:\n"                              # 5
        "  p ==> p\n"                                          # 6
        "Proof\n"                                              # 7
        "  strip_tac >> first_assum ACCEPT_TAC\n"              # 8
        "QED\n"                                                # 9
        "\n"                                                   # 10
        "Theorem chain:\n"                                     # 11
        "  p /\\ (p ==> q) ==> p /\\ q\n"                      # 12
        "Proof\n"                                              # 13
        "  strip_tac >> conj_tac\n"                            # 14
        '  >- suspend "c1"\n'                                  # 15
        '  >- suspend "c2"\n'                                  # 16
        "QED\n"                                                # 17
        "\n"                                                   # 18
        "Resume chain[c1]:\n"                                  # 19
        "  first_assum ACCEPT_TAC\n"                           # 20
        "QED\n"                                                # 21
        "\n"                                                   # 22
        "Resume chain[c2]:\n"                                  # 23
        f"  {c2_body}\n"                                       # 24
        '  >- suspend "c3"\n'                                  # 25
        "QED\n"                                                # 26
        "\n"                                                   # 27
        "Resume chain[c3]:\n"                                  # 28
        "  first_assum ACCEPT_TAC\n"                           # 29
        "QED\n"                                                # 30
        "\n"                                                   # 31
        "Finalise chain\n"                                     # 32
        "\n"                                                   # 33
        "val _ = export_theory();\n"                           # 34
    )


C2_START_LINE = 23
C2_BODY_LINE = 24
BROKEN_C2 = 'FAIL_TAC "broken" >> strip_tac >> conj_tac'
FIXED_C2 = "strip_tac >> conj_tac"
C2_FAIL_REASON = 'error: FAIL_TAC "broken"'
C3_ORPHAN_REASON = "label not found at load — Resume block SKIPPED, never ran"


def _loaded_cursor(tmp_path: Path, c2_body: str) -> tuple[Path, FileProofCursor]:
    """A cursor whose bookkeeping says: the whole file has been loaded, every
    theorem has a context checkpoint, every Resume goal is cached, and the
    navigator sits inside chain[c2]."""
    script = tmp_path / "brokenchainScript.sml"
    script.write_text(_chain_script(c2_body))
    ckpt_dir = tmp_path / "ckpt"
    ckpt_dir.mkdir()
    cursor = FileProofCursor(script, session=None, checkpoint_dir=ckpt_dir)
    cursor._reparse_if_changed()
    # The first parse (from empty content) schedules the cold init; the
    # simulated cursor is one whose init has already run.
    cursor._needs_session_reinit = False
    cursor._reinit_reason = None
    cursor._context_rewind_pending = False
    cursor.take_notices()

    cursor._loaded_to_line = script.read_text().count("\n") + 1
    cursor._base_checkpoint_saved = True
    for thm in cursor._theorems:
        path = cursor._get_checkpoint_path(thm.name, "context")
        path.write_text("")
        cursor._checkpoints[thm.name] = TheoremCheckpoint(
            theorem_name=thm.name, tactics_count=0, context_path=path,
            content_hash=cursor._theorem_prefix_hash(thm.name),
        )
        if thm.kind == "Resume":
            cursor._resume_goals[thm.name] = {"asms": [], "goal": "g"}
    cursor._proof_traces["lemma_before"] = []
    cursor._pos = SessionPosition(
        tactic_idx=1, content_hash=cursor._content_hash, initialized=True)
    cursor._active_theorem = "chain[c2]"
    return script, cursor


def _broken_cursor(tmp_path: Path) -> tuple[Path, FileProofCursor]:
    script, cursor = _loaded_cursor(tmp_path, BROKEN_C2)
    cursor._failed_proofs = {
        "chain[c2]": C2_FAIL_REASON,
        "chain[c3]": C3_ORPHAN_REASON,
    }
    # Precondition: this is exactly the case the reinit gate fires on.
    assert cursor._affected_chain_is_broken(C2_BODY_LINE)
    return script, cursor


def test_edit_in_broken_chain_keeps_prefix_cache(tmp_path: Path):
    """Fixing the red arm must invalidate from the edited block on, and no
    further: no session reinit, prefix kept up to the block, checkpoints and
    caches before it retained."""
    script, cursor = _broken_cursor(tmp_path)

    script.write_text(_chain_script(FIXED_C2))
    assert cursor._reparse_if_changed() is True

    assert not cursor._needs_session_reinit, (
        "an edit inside a broken chain forced a FULL session reinit (HOL "
        "restart + dependency reload + prefix replay from line 1)"
    )
    assert cursor._loaded_to_line == C2_START_LINE, (
        f"loaded prefix should be truncated at the edited block's start "
        f"(line {C2_START_LINE}), not reset to {cursor._loaded_to_line}"
    )
    assert cursor._context_rewind_pending, (
        "the next enter_theorem must rewind the heap to a predecessor "
        "checkpoint — that is what makes the partial replay sound"
    )

    c2 = cursor._get_theorem("chain[c2]")
    predecessor = cursor._find_predecessor_checkpoint(c2)
    assert predecessor is not None and predecessor.name == "chain[c1]", (
        f"context checkpoints before the edit were discarded: predecessor="
        f"{predecessor and predecessor.name!r}, kept={sorted(cursor._checkpoints)}"
    )
    assert "lemma_before" in cursor._checkpoints
    assert "chain" in cursor._checkpoints
    # The edited block and everything after it ARE stale.
    assert "chain[c2]" not in cursor._checkpoints
    assert "chain[c3]" not in cursor._checkpoints

    assert "lemma_before" in cursor._proof_traces, "trace before the edit dropped"
    assert "chain[c1]" in cursor._resume_goals, (
        "chain[c1]'s goal comes from the untouched root; it must survive"
    )
    # Verdicts for the edited block and its orphaned child are re-derived on
    # the next load, never carried forward.
    assert "chain[c2]" not in cursor._failed_proofs
    assert "chain[c3]" not in cursor._failed_proofs


def test_edit_in_broken_chain_names_chain_and_failed_member(tmp_path: Path):
    """The caller must be able to see that the reload it is about to pay is
    a consequence of its own red arm: the notice names the chain root, the
    failed member with its reason, and the child it orphaned."""
    script, cursor = _broken_cursor(tmp_path)

    script.write_text(_chain_script(FIXED_C2))
    cursor._reparse_if_changed()

    notices = "\n".join(cursor.take_notices())
    assert "chain[c2]" in notices and C2_FAIL_REASON in notices, (
        f"no notice named the failed chain member and why it failed: "
        f"{notices!r}"
    )
    assert re.search(r"\bchain\b", notices), f"chain root not named: {notices!r}"
    assert "chain[c3]" in notices, (
        f"the child orphaned by the red arm was not named: {notices!r}"
    )


def test_edit_in_healthy_chain_is_silent_and_partial(tmp_path: Path):
    script, cursor = _loaded_cursor(tmp_path, FIXED_C2)
    cursor._failed_proofs = {}

    script.write_text(_chain_script("strip_tac >> conj_tac >> ALL_TAC"))
    cursor._reparse_if_changed()

    assert not cursor._needs_session_reinit
    assert cursor._loaded_to_line == C2_START_LINE
    assert cursor.take_notices() == []


# ---------------------------------------------------------------------------
# Making the remaining full reinits, and a red arm's cost, legible.
# ---------------------------------------------------------------------------

def test_pre_theorem_edit_reinit_is_named(tmp_path: Path):
    """A full reinit that IS still owed (edit before the first theorem) must
    say why, so a 200s `startup=` is attributable to something."""
    script, cursor = _loaded_cursor(tmp_path, FIXED_C2)

    script.write_text(_chain_script(FIXED_C2).replace(
        'new_theory "brokenchain"', 'new_theory "renamed"'))
    cursor._reparse_if_changed()

    assert cursor._needs_session_reinit
    assert cursor._reinit_reason and "precedes the first theorem" in cursor._reinit_reason
    notices = "\n".join(cursor.take_notices())
    assert "line 3" in notices and "precedes the first theorem" in notices, notices


def test_slow_prefix_line_names_known_cause():
    from hol4_mcp import hol_mcp_server as srv
    cause = "session reinit: the edit at line 2 precedes the first theorem (line 5)"
    with_cause = "".join(srv._slow_nav_lines("s", "f", "thm", 200, 199, cause=cause))
    assert cause in with_cause
    assert "Inspect current-file" not in with_cause, (
        "a known cause must replace the generic 'inspect translation/"
        "dependency loads' guess")
    assert "does not justify splitting" in with_cause
    without = "".join(srv._slow_nav_lines("s", "f", "thm", 200, 199))
    assert "Inspect current-file" in without


class _FakeSession:
    """Accepts every command; a Theorem cheat reads as bound."""
    def __init__(self):
        self.sent: list[str] = []

    async def send(self, cmd: str, timeout=None) -> str:
        self.sent.append(cmd)
        m = re.match(r"Theorem (\S+?)(\[|:)", cmd)
        return f"val {m.group(1)} = |- T: thm" if m else ""

    async def drain_stale(self):
        pass


@pytest.mark.asyncio
async def test_auto_cheat_of_chain_member_names_orphans_and_remedy(tmp_path: Path):
    """At the moment an arm goes red the caller is told what it just cost:
    which Resume blocks are now unreachable, that every load re-runs the
    body, and the pattern that avoids it."""
    script = tmp_path / "brokenchainScript.sml"
    script.write_text(_chain_script(BROKEN_C2))
    cursor = FileProofCursor(script, _FakeSession(), checkpoint_dir=tmp_path / "ckpt")
    cursor._reparse_if_changed()
    cursor.take_notices()

    err = await cursor._cheat_failed_theorem(
        cursor._get_theorem("chain[c2]"), C2_FAIL_REASON)
    assert err is None
    assert cursor._failed_proofs["chain[c2]"] == C2_FAIL_REASON
    notice = "\n".join(cursor.take_notices())
    assert "chain[c2]" in notice and C2_FAIL_REASON in notice, notice
    assert "chain[c3]" in notice, f"orphaned child not named: {notice!r}"
    assert "`cheat`" in notice and "suspend" in notice, notice

    # A plain lemma's auto-cheat is not a chain event: no notice.
    err = await cursor._cheat_failed_theorem(
        cursor._get_theorem("lemma_before"), "error: nope")
    assert err is None
    assert "lemma_before" in cursor._failed_proofs
    assert cursor.take_notices() == []


# ---------------------------------------------------------------------------
# Integration: the guarantee the reinit protected, kept without a restart.
# ---------------------------------------------------------------------------

@pytest.fixture
async def hol_session_tmpdir(tmp_path):
    session = HOLSession(str(tmp_path))
    await session.start()
    await session.send(
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30
    )
    yield session
    await session.stop()


# nested[A]'s body sub-suspends "B". If it fails it is auto-cheated, the
# `suspend "B"` never runs, and nested[B] is orphaned ("No such label").
def _nested_script(dispatcher_body: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib markerLib;\n"          # 1
        "\n"                                                          # 2
        'val _ = new_theory "partnest";\n'                           # 3
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


def _is_proof_complete(res) -> bool:
    return bool(
        not res.goals
        and res.tactics_replayed == res.tactics_total
        and (res.error is None or "no goals" in res.error.lower())
    )


async def _resumptions_for(session, label: str) -> int:
    out = await session.send(
        'length (markerLib.lookup_resumption {parent_thy = "partnest", '
        f'parent_name = "nested", label = "{label}"}});', timeout=10)
    m = re.search(r"val it = (\d+)", out)
    assert m, f"could not read the resumption count: {out!r}"
    return int(m.group(1))


@pytest.mark.asyncio
async def test_fixed_subdispatcher_unorphans_child_without_process_restart(
    hol_session_tmpdir, tmp_path: Path
):
    script = tmp_path / "partnestScript.sml"

    # 1. Broken dispatcher: nested[A] auto-cheated, "B" never registered.
    script.write_text(_nested_script(_BROKEN_DISPATCHER))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    await cursor.state_at(NESTED_B_QED_LINE, 1)
    assert "nested[A]" in cursor._failed_proofs
    pid_before = hol_session_tmpdir.process.pid

    # 2. Fix the dispatcher; navigate to the child again.
    script.write_text(_nested_script(_GOOD_DISPATCHER))
    res_b = await cursor.state_at(NESTED_B_QED_LINE, 1)

    # The guarantee: the child is back.
    assert "nested[A]" not in cursor._failed_proofs
    assert "nested[B]" not in cursor._failed_proofs
    assert _is_proof_complete(res_b), (
        f"nested[B] not navigable after fixing the dispatcher: "
        f"error={res_b.error!r} "
        f"replayed={res_b.tactics_replayed}/{res_b.tactics_total}"
    )
    # ...and it was not bought with a restart.
    assert hol_session_tmpdir.process.pid == pid_before, (
        "fixing a broken chain restarted the HOL process (full reinit)"
    )
    assert not cursor._needs_session_reinit
    assert res_b.timings.get("startup_cause") is None

    # The store is what a clean run would hold: ONE resumption for A (the
    # rewind dropped the auto-cheat's entry rather than stacking the real
    # one on top of it) and B registered by it.
    assert await _resumptions_for(hol_session_tmpdir, "A") == 1
    assert await _resumptions_for(hol_session_tmpdir, "B") == 1


@pytest.mark.asyncio
async def test_fresh_cursor_init_is_not_paid_twice(hol_session_tmpdir, tmp_path: Path):
    """A fresh cursor's first parse is a change 'at line 1, before the first
    theorem' — which must not schedule a second cold start for the first
    navigation to pay (HOL restart + dependency reload)."""
    script = tmp_path / "partnestScript.sml"
    script.write_text(_nested_script(_GOOD_DISPATCHER))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    assert not cursor._needs_session_reinit, (
        "init left a full reinit pending: the first navigation restarts HOL "
        "and reloads every dependency a second time"
    )
    pid_after_init = hol_session_tmpdir.process.pid

    res = await cursor.state_at(NESTED_B_QED_LINE, 1)
    assert _is_proof_complete(res), res.error
    assert hol_session_tmpdir.process.pid == pid_after_init, (
        "first navigation after init restarted HOL"
    )


@pytest.mark.asyncio
async def test_reinit_cause_reaches_navigation_timings(
    hol_session_tmpdir, tmp_path: Path
):
    """A full reinit that is still owed carries its reason into the
    navigation's timings, where the slow-prefix line reads it."""
    script = tmp_path / "partnestScript.sml"
    script.write_text(_nested_script(_GOOD_DISPATCHER))
    cursor = FileProofCursor(script, hol_session_tmpdir)
    await cursor.init()
    res = await cursor.state_at(NESTED_B_QED_LINE, 1)
    assert _is_proof_complete(res), res.error
    assert res.timings.get("startup_cause") is None

    # Edit BEFORE the first theorem: the header may have changed, reinit owed.
    script.write_text("(* header *)\n" + _nested_script(_GOOD_DISPATCHER))
    res = await cursor.state_at(NESTED_B_QED_LINE + 1, 1)
    assert _is_proof_complete(res), res.error
    cause = res.timings.get("startup_cause")
    assert cause and "precedes the first theorem" in cause, res.timings
    assert res.timings["startup"] > 0

    # Consumed: the next navigation does not re-attribute it.
    res = await cursor.state_at(NESTED_B_QED_LINE + 1, 1)
    assert res.timings.get("startup_cause") is None
