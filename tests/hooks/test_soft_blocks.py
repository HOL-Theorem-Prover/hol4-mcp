"""Soft hooks (H28, H29, H30, H31, H32, H33) block a situation ONCE, then let an
identical retry through with a prominent override note and a log entry; a
consent phrase in ANY earlier user turn pre-grants. The hard hooks (H14
`git ok`, H27 `wip ok`) keep reading the latest message only, and a `git
commit` reports the session's overrides."""
import json
import os
import subprocess
import time

import pytest


SESSION = "soft-session"


def ctx(out):
    return json.loads(out)["hookSpecificOutput"]["additionalContext"] if out.strip() else ""


def state_dir(home):
    d = home / ".claude" / "hook-state" / SESSION
    d.mkdir(parents=True, exist_ok=True)
    return d


# --- H28 ---------------------------------------------------------------------

def test_h28_blocks_once_then_retry_passes_with_override(run_hook):
    call = lambda: run_hook("h28_shell_hol_build.py", "Bash", {"command": "Holmake --qof"},
                            session_id=SESSION)
    code, err, _ = call()
    assert code == 2 and "repeat" in err.lower(), err
    code, _, out = call()
    assert code == 0
    assert "OVERRIDDEN" in ctx(out) and "H28" in ctx(out), out


def test_h28_different_command_blocks_again(run_hook):
    run_hook("h28_shell_hol_build.py", "Bash", {"command": "Holmake --qof"}, session_id=SESSION)
    code, _, _ = run_hook("h28_shell_hol_build.py", "Bash", {"command": "Holmake fooTheory"},
                          session_id=SESSION)
    assert code == 2


def test_h28_pregrant_in_earlier_message(run_hook):
    code, _, out = run_hook("h28_shell_hol_build.py", "Bash", {"command": "Holmake --qof"},
                            user_msg="continue", history=["shell holmake ok for today"],
                            session_id=SESSION)
    assert code == 0, out
    assert "pre-granted" in ctx(out).lower(), out


def test_h28_block_message_does_not_ask_the_user(run_hook):
    code, err, _ = run_hook("h28_shell_hol_build.py", "Bash", {"command": "Holmake --qof"},
                            session_id=SESSION)
    assert code == 2
    assert "ask the user" not in err.lower() and "next message" not in err.lower(), err


# --- H29 ---------------------------------------------------------------------

def seed_h29(home, path, last):
    d = state_dir(home)
    (d / "hol4_file").write_text(path)
    (d / "h29_last_stop").write_text(json.dumps(
        {"ts": time.time() - 60, "tool": "mcp__hol4__hol_stop", "file": last}))


def test_h29_repeat_stop_blocks_once_then_passes(run_hook):
    seed_h29(run_hook.home, "/w/thy/fooScript.sml", "/w/thy/fooScript.sml")
    call = lambda: run_hook("h29_hol_stop_repeat.py", "mcp__hol4__hol_stop", {"session": "default"},
                            session_id=SESSION)
    code, err, _ = call()
    assert code == 2, err
    code, _, out = call()
    assert code == 0 and "OVERRIDDEN" in ctx(out), out


def test_h29_allowed_after_a_recorded_timeout(run_hook):
    seed_h29(run_hook.home, "/w/thy/fooScript.sml", "/w/thy/fooScript.sml")
    # A navigation that hit the budget was recorded by the PostToolUse side.
    run_hook("h6_check_proof_failure.py", "mcp__hol4__hol_state_at", {"line": 3},
             event="PostToolUse", session_id=SESSION,
             tool_response="ERROR: TIMEOUT: state_at exceeded its overall 300s budget and was "
                           "aborted (HOL interrupted; session recovered). Spent: prefix=1.0s, target=299.0s")
    code, _, out = run_hook("h29_hol_stop_repeat.py", "mcp__hol4__hol_stop", {"session": "default"},
                            session_id=SESSION)
    assert code == 0, out
    assert "timeout" in ctx(out).lower(), out


# --- H30 ---------------------------------------------------------------------

LIB = "Theory lib\nAncestors\n  arithmetic\n\nDefinition l_def:\n  l = 1n\nEnd\n"
APP = "Theory app\nAncestors\n  lib\n\nTheorem a_thm:\n  l = 1\nProof\n  rw [l_def]\nQED\n"


@pytest.fixture
def stale_repo(tmp_path):
    root = tmp_path / "repo"
    (root / "lib").mkdir(parents=True)
    (root / "app").mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    (root / "lib" / "libScript.sml").write_text(LIB)
    (root / "lib" / "lib2Script.sml").write_text(LIB.replace("Theory lib", "Theory lib2"))
    (root / "app" / "appScript.sml").write_text(APP.replace("  lib\n", "  lib lib2\n"))
    objs = root / "lib" / ".hol" / "objs"
    objs.mkdir(parents=True)
    now = time.time()
    for thy in ("lib", "lib2"):
        (objs / f"{thy}Theory.dat").write_text("")
        os.utime(objs / f"{thy}Theory.dat", (now - 100, now - 100))
        os.utime(root / "lib" / f"{thy}Script.sml", (now - 200, now - 200))   # fresh
    os.utime(root / "lib" / "libScript.sml", (now, now))                    # lib stale
    return root


def nav(run_hook, repo, **kw):
    return run_hook("h30_stale_ancestors.py", "mcp__hol4__hol_state_at",
                    {"line": 8, "file": str(repo / "app" / "appScript.sml")},
                    session_id=SESSION, **kw)


def test_h30_blocks_once_then_retry_passes_with_override(run_hook, stale_repo):
    code, err, _ = nav(run_hook, stale_repo)
    assert code == 2 and "libScript.sml" in err, err
    code, _, out = nav(run_hook, stale_repo)
    assert code == 0, out
    assert "OVERRIDDEN" in ctx(out) and "lib" in ctx(out), out


def test_h30_suggests_rebuilding_from_the_ancestors_own_directory(run_hook, stale_repo):
    code, err, _ = nav(run_hook, stale_repo)
    assert code == 2
    assert f"workdir={stale_repo / 'lib'}" in err and "target=libTheory" in err, err


def test_h30_new_staleness_blocks_again(run_hook, stale_repo):
    nav(run_hook, stale_repo)
    code, _, _ = nav(run_hook, stale_repo)
    assert code == 0
    # A second ancestor becomes stale: a new situation, blocked once more.
    now = time.time()
    os.utime(stale_repo / "lib" / "lib2Script.sml", (now, now))
    code, err, _ = nav(run_hook, stale_repo)
    assert code == 2, err


def test_h30_pregrant_in_earlier_message(run_hook, stale_repo):
    code, _, out = nav(run_hook, stale_repo, user_msg="go on", history=["stale ok, keep going"])
    assert code == 0, out
    assert "pre-granted" in ctx(out).lower(), out


@pytest.mark.parametrize("tool", ["holmake", "hol_build_status", "hol_cancel_build",
                                 "hol_stop", "hol_sessions"])
def test_h30_non_navigation_does_not_consume_override(run_hook, stale_repo, tool):
    # A denied navigation still caches the target, as in the real incident.
    assert nav(run_hook, stale_repo)[0] == 2
    state = run_hook.home / ".claude" / "hook-state" / SESSION / "soft_blocks.json"
    before = state.read_bytes()
    code, err, out = run_hook("h30_stale_ancestors.py", f"mcp__hol4__{tool}",
                              {"workdir": str(stale_repo)}, session_id=SESSION)
    assert code == 0 and not err and not out
    assert state.read_bytes() == before
    # The actual navigation still follows the ordinary logged-override path.
    assert "OVERRIDDEN" in ctx(nav(run_hook, stale_repo)[2])


# --- H31 ---------------------------------------------------------------------

def test_h31_blocks_once_then_retry_passes(run_hook):
    call = lambda: run_hook("h31_skip_prefix_consent.py", "mcp__hol4__hol_state_at",
                            {"line": 10, "skip_prefix": True, "file": "/w/thy/fooScript.sml"},
                            session_id=SESSION)
    code, err, _ = call()
    assert code == 2 and "repeat" in err.lower(), err
    code, _, out = call()
    assert code == 0 and "OVERRIDDEN" in ctx(out) and "H31" in ctx(out), out


def test_h31_pregrant_in_earlier_message(run_hook):
    code, _, out = run_hook("h31_skip_prefix_consent.py", "mcp__hol4__hol_state_at",
                            {"line": 10, "skip_prefix": True}, user_msg="next",
                            history=["skip prefix ok for this file"], session_id=SESSION)
    assert code == 0 and "pre-granted" in ctx(out).lower(), out


# --- H32 ---------------------------------------------------------------------

def test_h32_untargeted_blocks_once_then_passes(run_hook, tmp_path):
    call = lambda: run_hook("h32_holmake_preflight.py", "mcp__hol4__holmake",
                            {"workdir": str(tmp_path)}, session_id=SESSION)
    code, err, _ = call()
    assert code == 2 and "target" in err, err
    code, _, out = call()
    assert code == 0 and "OVERRIDDEN" in ctx(out), out


def test_h32_cross_directory_stale_ancestor_is_not_blocked(run_hook, stale_repo):
    code, err, _ = run_hook("h32_holmake_preflight.py", "mcp__hol4__holmake",
                            {"workdir": str(stale_repo / "app"), "target": "appTheory"},
                            session_id=SESSION)
    assert code == 0, err


# --- hard hooks stay hard; commit reports overrides ---------------------------

def test_h14_ignores_git_ok_in_earlier_messages(run_hook):
    code, _, _ = run_hook("h14_git_destructive_consent.py", "Bash", {"command": "git commit -m x"},
                          user_msg="now commit", history=["git ok"], session_id=SESSION)
    assert code == 2


def test_h27_ignores_wip_ok_in_earlier_messages(run_hook, tmp_path):
    repo = tmp_path / "r"
    repo.mkdir()
    git = lambda *a: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *a],
                                    cwd=repo, check=True, capture_output=True)
    git("init", "-q")
    (repo / "fooScript.sml").write_text("Theorem t:\n  T\nProof\n  cheat\nQED\n")
    git("add", "fooScript.sml")
    code, _, _ = run_hook("h27_commit_audit_gate.py", "Bash", {"command": "git commit -m x"},
                          user_msg="git ok", history=["wip ok"], cwd=repo, session_id=SESSION)
    assert code == 2


def test_commit_reports_session_overrides(run_hook):
    call = lambda: run_hook("h28_shell_hol_build.py", "Bash", {"command": "Holmake --qof"},
                            session_id=SESSION)
    call()
    call()                                       # one override logged
    code, _, out = run_hook("h14_git_destructive_consent.py", "Bash",
                            {"command": "git commit -m x"}, user_msg="git ok", session_id=SESSION)
    assert code == 0
    assert "overrode" in ctx(out).lower() and "H28" in ctx(out), out
