"""H22 (SessionStart directive) must also report hook-wiring drift: a hook
script present in ``hooks/`` but absent from ``~/.claude/settings.json`` is
named at session start instead of sitting unwired unnoticed."""
import json
import subprocess
import sys
from pathlib import Path

import pytest

HOOKS_DIR = Path(__file__).resolve().parents[2] / "hooks"



def wired_settings(drop=None):
    block = json.loads(subprocess.run(
        [sys.executable, str(HOOKS_DIR / "install_hooks.py"), "--print"],
        capture_output=True, text=True, check=True).stdout)
    if drop:
        for event, entries in block["hooks"].items():
            block["hooks"][event] = [
                e for e in entries
                if not any(h["command"].endswith(drop) for h in e["hooks"])]
    return block


def write_settings(home, settings):
    d = home / ".claude"
    d.mkdir(exist_ok=True)
    (d / "settings.json").write_text(json.dumps(settings))


def context_of(stdout):
    if not stdout.strip():
        return ""
    return json.loads(stdout)["hookSpecificOutput"]["additionalContext"]


def hol4_dir(tmp_path):
    d = tmp_path / "proj"
    d.mkdir()
    (d / "Holmakefile").write_text("")
    return d


def test_hol4_dir_gets_directive(run_hook, tmp_path):
    write_settings(run_hook.home, wired_settings())
    code, _, out = run_hook("h22_hol4_context.py", "", {}, event="SessionStart",
                            cwd=hol4_dir(tmp_path))
    assert code == 0
    ctx = context_of(out)
    assert "hol4-proving" in ctx
    assert "NOT WIRED" not in ctx


def test_non_hol4_dir_silent_when_wired(run_hook, tmp_path):
    write_settings(run_hook.home, wired_settings())
    code, _, out = run_hook("h22_hol4_context.py", "", {}, event="SessionStart",
                            cwd=tmp_path)
    assert code == 0
    assert out.strip() == ""


def test_missing_hook_is_named_in_hol4_dir(run_hook, tmp_path):
    write_settings(run_hook.home, wired_settings(drop="h28_shell_hol_build.py"))
    code, _, out = run_hook("h22_hol4_context.py", "", {}, event="SessionStart",
                            cwd=hol4_dir(tmp_path))
    assert code == 0
    ctx = context_of(out)
    assert "hol4-proving" in ctx
    assert "NOT WIRED" in ctx and "h28_shell_hol_build.py" in ctx
    assert "install_hooks.py" in ctx


def test_missing_hook_is_named_outside_hol4_dir(run_hook, tmp_path):
    write_settings(run_hook.home, wired_settings(drop="h14_git_destructive_consent.py"))
    code, _, out = run_hook("h22_hol4_context.py", "", {}, event="SessionStart",
                            cwd=tmp_path)
    assert code == 0
    ctx = context_of(out)
    assert "NOT WIRED" in ctx and "h14_git_destructive_consent.py" in ctx
