"""Consent is read only from turns the user typed. Claude Code also writes the
compaction summary, request copies, hook and goal echoes and task notifications
as `role=user` lines; they quote consent phrases verbatim and must grant
nothing. Event shapes follow real Claude Code transcript lines."""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "hooks"))
from hook_payload import user_messages  # noqa: E402

QUOTING = "the user's standing rules: `git ok`, `wip ok`, `waiter ok`"


def _user(content, **fields):
    return {"type": "user", "userType": "external",
            "message": {"role": "user", "content": content}, **fields}


def _harness(text):
    return [
        pytest.param(_user(f"This session is being continued ... {text}",
                           isCompactSummary=True, isVisibleInTranscriptOnly=True),
                     id="compact-summary"),
        pytest.param({"type": "api-request-blob", "hash": "h", "sessionId": "s",
                      "message": {"role": "user", "content": [
                          {"type": "text", "text": f"<system-reminder>{text}</system-reminder>"}]}},
                     id="api-request-blob"),
        pytest.param(_user(f'A session-scoped Stop hook is now active with condition: "{text}"',
                           isMeta=True),
                     id="meta-stop-hook"),
        pytest.param(_user(f"Goal set: {text}", origin={"kind": "auto-continuation"}),
                     id="goal-echo"),
        pytest.param(_user(f"<task-notification>{text}</task-notification>",
                           origin={"kind": "task-notification", "producer": "session-task"}),
                     id="task-notification"),
        pytest.param(_user(f"<local-command-stdout>Goal set: {text}</local-command-stdout>"),
                     id="command-output"),
    ]


HARNESS = _harness(QUOTING)
NEUTRAL_HARNESS = _harness("Tool loaded.")

TYPED = [
    pytest.param(_user("go", origin={"kind": "human"}, promptSource="typed"), id="typed"),
    pytest.param(_user("go"), id="no-origin"),
    pytest.param({"role": "user", "content": "go"}, id="flat"),
    pytest.param(_user("<command-name>/compact</command-name>"), id="slash-command"),
]


@pytest.mark.parametrize("event", HARNESS)
def test_harness_lines_are_not_user_turns(tmp_path, event):
    transcript = tmp_path / "t.jsonl"
    transcript.write_text(json.dumps(event) + "\n")
    assert user_messages({"transcript_path": str(transcript)}) == []


@pytest.mark.parametrize("event", TYPED)
def test_typed_turns_are_user_turns(tmp_path, event):
    transcript = tmp_path / "t.jsonl"
    transcript.write_text(json.dumps(event) + "\n")
    assert len(user_messages({"transcript_path": str(transcript)})) == 1


@pytest.mark.parametrize("event", HARNESS)
def test_soft_pregrant_not_taken_from_harness_line(run_hook, event):
    code, err, out = run_hook("h33_background_waiter.py", "Bash",
                              {"command": "sleep 30 && tail -n 20 build.log"},
                              user_msg="go", after=[event])
    assert code == 2, (out, err)
    assert "pre-granted" not in out


@pytest.mark.parametrize("event", HARNESS)
def test_h14_refuses_when_only_a_harness_line_says_git_ok(run_hook, event):
    code, err, _ = run_hook("h14_git_destructive_consent.py", "Bash",
                            {"command": "git commit -m x"}, user_msg="go", after=[event])
    assert code == 2 and "H14" in err, err


@pytest.mark.parametrize("event", NEUTRAL_HARNESS)
def test_h14_accepts_git_ok_followed_by_harness_lines(run_hook, event):
    code, err, _ = run_hook("h14_git_destructive_consent.py", "Bash",
                            {"command": "git commit -m x"}, user_msg="git ok",
                            after=[event])
    assert code == 0, err


GOAL_COMMAND = _user("<command-name>/goal</command-name>\n"
                     "            <command-message>goal</command-message>\n"
                     "            <command-args>finish, then wait for my git ok</command-args>")


def test_slash_command_arguments_grant_nothing(run_hook):
    code, err, _ = run_hook("h14_git_destructive_consent.py", "Bash",
                            {"command": "git commit -m x"}, user_msg="go",
                            after=[GOAL_COMMAND])
    assert code == 2 and "H14" in err, err


def test_slash_command_ends_earlier_consent(run_hook):
    code, err, _ = run_hook("h14_git_destructive_consent.py", "Bash",
                            {"command": "git commit -m x"}, user_msg="git ok",
                            after=[GOAL_COMMAND])
    assert code == 2 and "H14" in err, err
