"""Harness for the Claude Code hooks in ``hooks/``.

Each hook is a standalone script that reads one JSON payload on stdin and
answers with an exit code (0 = allow, 2 = block) plus stderr (the block
message) or stdout (``hookSpecificOutput`` JSON for advisories). The
consent-gated hooks also read the newest user turn from the transcript file
named by ``transcript_path``. ``run_hook`` builds both and runs the script as
Claude Code would, under a private ``HOME`` so ``~/.claude/hook-state`` never
touches the real one.
"""
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

HOOKS_DIR = Path(__file__).resolve().parents[2] / "hooks"


def _transcript_line(role, content):
    return json.dumps({"type": role, "message": {"role": role, "content": content}})


@pytest.fixture
def run_hook(tmp_path):
    """Run ``hooks/<script>`` on a synthetic payload.

    Returns ``(exit_code, stderr, stdout)``. ``user_msg`` becomes the newest
    user turn in the transcript, after the earlier user turns in ``history``
    (each followed by an assistant turn); ``after`` holds raw transcript
    events (dicts) written after the newest user turn, for harness-written
    lines; ``tool_response`` (PostToolUse) is attached
    as ``tool_response``; ``extra`` merges into the payload; ``env`` merges
    into the subprocess environment. The private ``HOME`` is
    ``tmp_path/home``, so a test that needs to pre-seed hook state writes
    under ``tmp_path/home/.claude/hook-state/<session_id>/``.
    """
    home = tmp_path / "home"
    home.mkdir(exist_ok=True)

    def _run(script, tool_name, tool_input, user_msg="", *, event="PreToolUse",
             tool_response=None, extra=None, env=None, session_id="test-session",
             cwd=None, history=(), after=()):
        transcript = tmp_path / "transcript.jsonl"
        turns = []
        for earlier in history:
            turns.append(_transcript_line("user", earlier))
            turns.append(_transcript_line("assistant", [{"type": "text", "text": "ok"}]))
        turns.append(_transcript_line("user", user_msg))
        turns.append(_transcript_line("assistant", [{"type": "text", "text": "ok"}]))
        turns.extend(json.dumps(event) for event in after)
        transcript.write_text("\n".join(turns) + "\n")
        payload = {
            "hook_event_name": event,
            "tool_name": tool_name,
            "tool_input": tool_input,
            "session_id": session_id,
            "cwd": str(cwd or tmp_path),
            "transcript_path": str(transcript),
        }
        if tool_response is not None:
            payload["tool_response"] = tool_response
        if extra:
            payload.update(extra)
        proc_env = os.environ.copy()
        proc_env["HOME"] = str(home)
        if env:
            proc_env.update(env)
        proc = subprocess.run(
            [sys.executable, str(HOOKS_DIR / script)],
            input=json.dumps(payload), capture_output=True, text=True,
            env=proc_env, timeout=60,
        )
        return proc.returncode, proc.stderr, proc.stdout

    _run.home = home
    return _run
