"""Session lifecycle: a live session must follow an ancestor rebuild, follow a
workdir switch, explain a dependency-load timeout, and report startup time
separately from replay. Each test builds real theories with Holmake."""
import re
import shutil
from pathlib import Path

import pytest

from hol4_mcp.hol_mcp_server import (
    hol_sessions,
    hol_state_at,
    hol_stop,
    holmake,
)

FIXTURES = Path(__file__).parent / "fixtures"

ANC_A = """\
open HolKernel boolLib bossLib;
val _ = new_theory "ancA";
Definition a_def:
  a = {value}n
End
val _ = export_theory();
"""

ANC_B = """\
open HolKernel boolLib bossLib;
open ancATheory;
val _ = new_theory "ancB";
Theorem b_thm:
  a = a
Proof
  PURE_ONCE_REWRITE_TAC [a_def]
  >> simp []
QED
val _ = export_theory();
"""
B_LINE_AFTER_REWRITE = 8   # the `>> simp []` line: state after the rewrite


def make_theory_dir(root: Path, value: int = 1) -> Path:
    root.mkdir(parents=True, exist_ok=True)
    shutil.copy(FIXTURES / "Holmakefile", root / "Holmakefile")
    (root / "ancAScript.sml").write_text(ANC_A.format(value=value))
    (root / "ancBScript.sml").write_text(ANC_B)
    return root


async def build_a(root: Path):
    out = await holmake(workdir=str(root), target="ancATheory", timeout=300)
    assert "Build succeeded" in out, out


def goal_line(output: str) -> str:
    m = re.search(r"=== Goal[^\n]*===\n(.*)", output)
    assert m, output
    return m.group(1).strip()


async def test_live_session_follows_ancestor_rebuild(tmp_path):
    root = make_theory_dir(tmp_path / "thy")
    await build_a(root)
    session = "lifecycle_rebuild"
    try:
        r1 = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6,
                                file=str(root / "ancBScript.sml"), session=session)
        assert goal_line(r1) == "1 = 1", r1

        (root / "ancAScript.sml").write_text(ANC_A.format(value=2))
        await build_a(root)

        r2 = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6, session=session)
        assert "[Session reloaded: ancestor ancATheory rebuilt" in r2, r2
        assert goal_line(r2) == "2 = 2", r2
    finally:
        await hol_stop(session)


async def test_missing_ancestor_recovers_after_build(tmp_path):
    root = make_theory_dir(tmp_path / "thy")
    session = "lifecycle_missing"
    try:
        first = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6,
                                   file=str(root / "ancBScript.sml"), session=session)
        assert first.startswith("ERROR"), first
        assert "ancATheory.uo" in first and "no target proof has run" in first, first
        await build_a(root)
        recovered = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6,
                                       session=session)
        assert goal_line(recovered) == "1 = 1", recovered
        assert "[Session reloaded: ancestor ancATheory rebuilt" in recovered, recovered
    finally:
        await hol_stop(session)


async def test_workdir_switch_restarts_transparently(tmp_path):
    d1 = make_theory_dir(tmp_path / "one")
    d2 = make_theory_dir(tmp_path / "two", value=2)
    await build_a(d1)
    await build_a(d2)
    session = "lifecycle_switch"
    try:
        r1 = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6,
                                file=str(d1 / "ancBScript.sml"), session=session)
        assert goal_line(r1) == "1 = 1", r1

        r2 = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6,
                                file=str(d2 / "ancBScript.sml"), session=session)
        assert not r2.startswith("ERROR"), r2
        assert goal_line(r2) == "2 = 2", r2
        assert "[Session restarted: workdir" in r2, r2
        assert str(d1) in r2 and str(d2) in r2, r2

        listing = await hol_sessions()
        assert listing.count("running") == 1, listing
    finally:
        await hol_stop(session)


async def test_dep_load_timeout_names_cause(tmp_path, monkeypatch):
    root = make_theory_dir(tmp_path / "thy")
    await build_a(root)
    monkeypatch.setenv("HOL4_MCP_DEP_LOAD_TIMEOUT", "0.001")
    session = "lifecycle_deptimeout"
    try:
        r = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6,
                               file=str(root / "ancBScript.sml"), session=session)
        assert r.startswith("ERROR"), r
        assert "timed out" in r, r
        assert "0.001" in r and "HOL4_MCP_DEP_LOAD_TIMEOUT" in r, r
        assert "HOLHEAP" in r, r
    finally:
        await hol_stop(session)


async def test_timing_line_reports_startup_separately(tmp_path):
    root = make_theory_dir(tmp_path / "thy")
    await build_a(root)
    session = "lifecycle_timing"
    try:
        cold = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6,
                                  file=str(root / "ancBScript.sml"), session=session)
        m = re.search(r"\[Timing: total=(\d+)ms, replay=(\d+)ms, startup=(\d+)ms", cold)
        assert m, cold
        total, replay, startup = (int(x) for x in m.groups())
        assert startup > 0 and replay < startup and startup <= total, cold

        warm = await hol_state_at(line=B_LINE_AFTER_REWRITE, col=6, session=session)
        assert "startup=0ms" in warm, warm
    finally:
        await hol_stop(session)
