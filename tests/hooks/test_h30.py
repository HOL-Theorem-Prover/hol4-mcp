"""H30 records its refusal (time, target, stale theories' directories) in the
session's hook state, which H29 reads to let the stop before the rebuild
through; a navigation that passes records nothing."""
import json
import os
import time

import pytest

SESSION = "h30-session"


def _project(tmp_path, built):
    root = tmp_path / "repo"
    (root / ".git").mkdir(parents=True)
    up = root / "up"
    up.mkdir()
    (up / "upScript.sml").write_text("Theory up\n\nTheorem a: T\nProof simp[]\nQED\n")
    if built:
        (up / ".hol" / "objs").mkdir(parents=True)
        dat = up / ".hol" / "objs" / "upTheory.dat"
        dat.write_text("built")
        later = time.time() + 5
        os.utime(dat, (later, later))
    down = root / "down"
    down.mkdir()
    target = down / "downScript.sml"
    target.write_text("Theory down\nAncestors\n  up\n\nTheorem b: T\nProof simp[]\nQED\n")
    return target, up


def _navigate(run_hook, target):
    return run_hook("h30_stale_ancestors.py", "mcp__hol4__hol_state_at",
                    {"file": str(target), "line": 6}, session_id=SESSION)


def _record(home):
    path = home / ".claude" / "hook-state" / SESSION / "last_stale_block"
    return json.loads(path.read_text()) if path.exists() else None


def test_a_refusal_is_recorded(run_hook, tmp_path):
    target, up = _project(tmp_path, built=False)
    code, err, _ = _navigate(run_hook, target)
    assert code == 2, err
    record = _record(run_hook.home)
    assert record is not None
    assert record["target"] == str(target)
    assert str(up) in record["stale_dirs"]
    assert time.time() - record["ts"] < 60


def test_a_pass_records_nothing(run_hook, tmp_path):
    target, _ = _project(tmp_path, built=True)
    code, err, out = _navigate(run_hook, target)
    assert code == 0, err
    assert _record(run_hook.home) is None
