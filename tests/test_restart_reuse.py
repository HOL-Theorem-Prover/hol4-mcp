"""A HOL restart (stop, restart, setenv) starts from the previous session's
saved states of the script when nothing they depend on changed — the same
`hol`, SML helpers, direct dependencies and loaded modules — instead of
reloading the dependencies and replaying the prefix; any such change, and a
fresh check, loads cold."""
import os
import time

import pytest

from hol4_mcp import hol_cursor
from hol4_mcp import hol_mcp_server as srv
from hol4_mcp.hol_cursor import FileProofCursor


def _script(directory, log, ancestors=""):
    header = (f'Theory reuse\nAncestors\n  {ancestors}\n\n' if ancestors else
              'open HolKernel Parse boolLib bossLib;\n\nval _ = new_theory "reuse";\n\n')
    counted = (f'fun counted g = (let val s = TextIO.openAppend "{log}" in '
               f'TextIO.output (s, "run\\n"); TextIO.closeOut s end; ALL_TAC g);\n\n')
    theorems = "".join(f"Theorem t{i}:\n  T\nProof\n  counted >> simp[]\nQED\n\n"
                       for i in range(1, 7))
    path = directory / "reuseScript.sml"
    path.write_text(header + counted + theorems)
    return path


def _runs(log):
    return len(log.read_text().splitlines()) if log.exists() else 0


def _line(path, needle):
    return next(i for i, ln in enumerate(path.read_text().split("\n"), 1) if needle in ln)


@pytest.fixture
def every_theorem_saves(monkeypatch):
    monkeypatch.setattr(FileProofCursor, "SAVESTATE_EVERY", 1)


async def _into_t6(script, session):
    return await srv.hol_state_at(line=_line(script, "Theorem t6") + 3, col=3,
                                  file=str(script), session=session)


async def test_a_restart_with_another_heap_starts_from_the_saved_prefix(tmp_path,
                                                                       every_theorem_saves):
    log = tmp_path / "runs.log"
    script = _script(tmp_path, log)
    session = "reuse_restart"
    try:
        state = await _into_t6(script, session)
        assert "=== Goal" in state and _runs(log) == 5, state
        restarted = await srv.hol_setenv({"HOL4_MCP_MAXHEAP_MB": "3072"}, session=session)
        assert "ERROR" not in restarted, restarted
        state = await _into_t6(script, session)
        assert "=== Goal" in state, state
        assert "Reused the state" in state and "(t5)" in state, state
        assert _runs(log) == 5, "the prefix replayed although its saved state was reused"
        assert srv._sessions[session].session.maxheap_mb == 3072
        # The reused heap is a working one: the next theorem replays on it.
        state = await srv.hol_state_at(line=_line(script, "Theorem t6") + 4, col=1,
                                       session=session)
        assert "No goals" in state, state
    finally:
        await srv.hol_stop(session=session)
        srv._session_envs.pop(session, None)


@pytest.mark.parametrize("change", ["helpers", "ancestor"])
async def test_a_changed_dependency_loads_cold(tmp_path, monkeypatch, every_theorem_saves,
                                               change):
    log = tmp_path / "runs.log"
    if change == "ancestor":
        (tmp_path / "upScript.sml").write_text(
            "Theory up\n\nTheorem up_thm:\n  T\nProof\n  simp[]\nQED\n")
        built = await srv.holmake(str(tmp_path), target="upTheory", timeout=300)
        assert "Build succeeded" in built, built
        script = _script(tmp_path, log, ancestors="up")
    else:
        script = _script(tmp_path, log)
    session = f"reuse_{change}"
    try:
        assert "=== Goal" in await _into_t6(script, session)
        await srv.hol_stop(session=session)
        if change == "helpers":
            monkeypatch.setattr(hol_cursor, "_helpers_hash", lambda: "changed")
        else:
            uo = next(tmp_path.glob("**/upTheory.uo"))
            later = time.time() + 10
            os.utime(uo, (later, later))
        state = await _into_t6(script, session)
        assert "=== Goal" in state and "Reused" not in state, state
        assert _runs(log) == 10
    finally:
        await srv.hol_stop(session=session)


async def test_a_fresh_check_never_reuses(tmp_path, every_theorem_saves):
    log = tmp_path / "runs.log"
    script = _script(tmp_path, log)
    session = "reuse_fresh"
    try:
        assert "=== Goal" in await _into_t6(script, session)
        await srv.hol_stop(session=session)
        result = await srv.hol_check_proof(theorem="t6", file=str(script), session=session,
                                           fresh=True)
        assert "Status: OK" in result, result
        assert _runs(log) == 5 + 6, _runs(log)
    finally:
        await srv.hol_stop(session=session)
