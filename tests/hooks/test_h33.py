"""H33 (background-waiter blocker): the three self-defeating shapes — a
`pgrep -f` that matches its own command line, an `until`/`while … sleep`
poll loop, `sleep N` then a log read — block once, pass on an identical
retry with an override note, and pass outright with `waiter ok`; plain log
reads, escaped or `-x` pgrep, a bare sleep and unrelated commands pass."""
import json

import pytest


HOOK = "h33_background_waiter.py"
SESSION = "h33-session"

BLOCK_CASES = [
    pytest.param('until ! pgrep -f "Holmake --qof"; do sleep 5; done', id="pgrep-selfmatch-loop"),
    pytest.param("pgrep -f hol4-mcp", id="pgrep-f-plain"),
    pytest.param("while ! grep -q done build.log; do sleep 2; done", id="while-sleep-loop"),
    pytest.param("sleep 30 && tail -n 20 .hol/mcp-build-abc.log", id="sleep-then-tail"),
    pytest.param("bash -c 'until test -f done; do sleep 1; done'", id="loop-inside-bash-c"),
]

PASS_CASES = [
    pytest.param("tail -n 20 .hol/mcp-build-abc.log", id="plain-log-read"),
    pytest.param("pgrep -f '[H]olmake'", id="pgrep-bracket-escaped"),
    pytest.param("pgrep -x Holmake", id="pgrep-x"),
    pytest.param("pgrep Holmake", id="pgrep-no-f"),
    pytest.param("sleep 2", id="bare-sleep"),
    pytest.param("python3 -m pytest tests/ -q", id="unrelated"),
]


def ctx(out):
    return json.loads(out)["hookSpecificOutput"]["additionalContext"] if out.strip() else ""


@pytest.mark.parametrize("cmd", BLOCK_CASES)
def test_blocks(run_hook, cmd):
    code, err, _ = run_hook(HOOK, "Bash", {"command": cmd})
    assert code == 2
    assert "H33" in err and "waiter" in err.lower(), err


@pytest.mark.parametrize("cmd", PASS_CASES)
def test_allows(run_hook, cmd):
    code, err, _ = run_hook(HOOK, "Bash", {"command": cmd})
    assert code == 0, err


def test_block_message_does_not_ask_the_user(run_hook):
    code, err, _ = run_hook(HOOK, "Bash", {"command": "sleep 10; tail build.log"})
    assert code == 2
    assert "ask the user" not in err.lower() and "next message" not in err.lower(), err


def test_blocks_once_then_retry_passes_with_override(run_hook):
    call = lambda: run_hook(HOOK, "Bash", {"command": "sleep 10; tail build.log"},
                            session_id=SESSION)
    code, err, _ = call()
    assert code == 2 and "repeat" in err.lower(), err
    code, _, out = call()
    assert code == 0
    assert "OVERRIDDEN" in ctx(out) and "H33" in ctx(out), out


def test_different_waiter_blocks_again(run_hook):
    run_hook(HOOK, "Bash", {"command": "sleep 10; tail build.log"}, session_id=SESSION)
    code, _, _ = run_hook(HOOK, "Bash", {"command": "sleep 20; tail other.log"},
                          session_id=SESSION)
    assert code == 2


def test_pregrant_in_earlier_message(run_hook):
    code, _, out = run_hook(HOOK, "Bash", {"command": "sleep 10; tail build.log"},
                            user_msg="go on", history=["waiter ok for this build"],
                            session_id=SESSION)
    assert code == 0, out
    assert "pre-granted" in ctx(out).lower(), out


def test_other_tools_ignored(run_hook):
    code, err, out = run_hook(HOOK, "Edit", {"file_path": "x", "old_string": "sleep 5; tail f",
                                              "new_string": "y"})
    assert code == 0 and not err and not out
