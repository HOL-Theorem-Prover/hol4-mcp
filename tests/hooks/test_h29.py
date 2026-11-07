"""H29 (repeat hol_stop/hol_restart blocker) is keyed on the WORKDIR: a
repeat stop while still working in the same theory directory is the ritual
stop even when the working file inside it changed; a stop after moving to
another directory is a legitimate switch."""
import json
import time

import pytest


SESSION = "h29-session"


def seed(home, path, last=None):
    d = home / ".claude" / "hook-state" / SESSION
    d.mkdir(parents=True, exist_ok=True)
    (d / "hol4_file").write_text(path)
    if last:
        (d / "h29_last_stop").write_text(json.dumps(
            {"ts": time.time() - 60, "tool": "mcp__hol4__hol_stop", "file": last}))


def stop(run_hook, user_msg=""):
    return run_hook("h29_hol_stop_repeat.py", "mcp__hol4__hol_stop", {"session": "default"},
                    user_msg=user_msg, session_id=SESSION)


def test_first_stop_allowed_with_reminder(run_hook):
    seed(run_hook.home, "/w/thy/fooScript.sml")
    code, _, out = stop(run_hook)
    assert code == 0
    assert "H29" in json.loads(out)["hookSpecificOutput"]["additionalContext"]


def test_repeat_same_file_blocked(run_hook):
    seed(run_hook.home, "/w/thy/fooScript.sml", last="/w/thy/fooScript.sml")
    code, err, _ = stop(run_hook)
    assert code == 2
    assert "H29" in err


def test_repeat_same_workdir_other_file_blocked(run_hook):
    seed(run_hook.home, "/w/thy/barScript.sml", last="/w/thy/fooScript.sml")
    code, err, _ = stop(run_hook)
    assert code == 2, err
    assert "/w/thy" in err


def test_repeat_other_workdir_allowed(run_hook):
    seed(run_hook.home, "/w/other/bazScript.sml", last="/w/thy/fooScript.sml")
    code, _, _ = stop(run_hook)
    assert code == 0


def test_consent_allows(run_hook):
    seed(run_hook.home, "/w/thy/fooScript.sml", last="/w/thy/fooScript.sml")
    code, _, _ = stop(run_hook, user_msg="restart ok")
    assert code == 0


def stale_block(home, target, stale_dirs, age=60):
    d = home / ".claude" / "hook-state" / SESSION
    d.mkdir(parents=True, exist_ok=True)
    (d / "last_stale_block").write_text(json.dumps(
        {"ts": time.time() - age, "target": target, "stale_dirs": stale_dirs}))


def test_repeat_stop_right_after_a_stale_ancestor_block_passes(run_hook):
    seed(run_hook.home, "/w/thy/downScript.sml", last="/w/thy/fooScript.sml")
    stale_block(run_hook.home, "/w/thy/downScript.sml", ["/w/thy"])
    code, err, out = stop(run_hook)
    assert code == 0, err
    note = json.loads(out)["hookSpecificOutput"]["additionalContext"]
    assert "H30" in note and "build" in note, note


@pytest.mark.parametrize("block", [
    None,
    {"target": "/w/thy/downScript.sml", "stale_dirs": ["/w/thy"], "age": 3600},
    {"target": "/w/other/xScript.sml", "stale_dirs": ["/w/other"]},
])
def test_repeat_stop_without_a_matching_recent_block_is_blocked(run_hook, block):
    seed(run_hook.home, "/w/thy/downScript.sml", last="/w/thy/fooScript.sml")
    if block is not None:
        stale_block(run_hook.home, **block)
    code, err, _ = stop(run_hook)
    assert code == 2, err


def test_the_block_message_names_the_stop_before_a_rebuild(run_hook):
    seed(run_hook.home, "/w/thy/fooScript.sml", last="/w/thy/fooScript.sml")
    code, err, _ = stop(run_hook)
    assert code == 2 and "stale ancestor" in err, err
