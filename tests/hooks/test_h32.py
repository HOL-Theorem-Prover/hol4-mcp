"""H32: a holmake call must name a target, and a target whose ancestor
closure would pull a rebuild into ANOTHER directory needs `build ok`;
fresh ancestors and in-workdir builds pass."""
import os
import subprocess
import time

import pytest


HOOK = "h32_holmake_preflight.py"

LIB = """\
Theory lib
Ancestors
  arithmetic

Definition l_def:
  l = 1n
End
"""
APP = """\
Theory app
Ancestors
  lib

Theorem a_thm:
  l = 1
Proof
  rw [l_def]
QED
"""


def touch(path, ts):
    os.utime(path, (ts, ts))


@pytest.fixture
def repo(tmp_path):
    root = tmp_path / "repo"
    (root / "lib").mkdir(parents=True)
    (root / "app").mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    (root / "lib" / "libScript.sml").write_text(LIB)
    (root / "app" / "appScript.sml").write_text(APP)
    (root / "lib" / "Holmakefile").write_text("")
    (root / "app" / "Holmakefile").write_text("INCLUDES = ../lib\n")
    now = time.time()
    # lib built after its script: fresh.
    objs = root / "lib" / ".hol" / "objs"
    objs.mkdir(parents=True)
    (objs / "libTheory.dat").write_text("")
    touch(root / "lib" / "libScript.sml", now - 100)
    touch(objs / "libTheory.dat", now - 50)
    return root


def call(run_hook, repo, tool_input, user_msg=""):
    return run_hook(HOOK, "mcp__hol4__holmake", tool_input, user_msg=user_msg, cwd=repo)


def test_untargeted_build_is_blocked(run_hook, repo):
    code, err, _ = call(run_hook, repo, {"workdir": str(repo / "app")})
    assert code == 2, err
    assert "H32" in err and "target" in err


def test_untargeted_build_with_consent_passes(run_hook, repo):
    code, _, _ = call(run_hook, repo, {"workdir": str(repo / "app")}, user_msg="build ok")
    assert code == 0


def test_fresh_ancestors_pass(run_hook, repo):
    code, err, _ = call(run_hook, repo, {"workdir": str(repo / "app"), "target": "appTheory"})
    assert code == 0, err






def test_in_workdir_target_passes_even_when_stale(run_hook, repo):
    touch(repo / "lib" / "libScript.sml", time.time())
    code, err, _ = call(run_hook, repo, {"workdir": str(repo / "lib"), "target": "libTheory"})
    assert code == 0, err
