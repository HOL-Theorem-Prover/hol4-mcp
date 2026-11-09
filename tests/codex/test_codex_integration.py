import json
import os
from pathlib import Path
import subprocess
import sys
import shlex
import time

import pytest


ROOT = Path(__file__).resolve().parents[2]
CODEX = ROOT / "integrations" / "codex"
ADAPTER = CODEX / "hook_adapter.py"


@pytest.fixture(params=[False, True], ids=["native", "fallback"])
def patch_adapter(request, monkeypatch):
    monkeypatch.syspath_prepend(str(CODEX))
    import hook_adapter
    if request.param:
        monkeypatch.setattr(hook_adapter.shutil, "which", lambda _: None)
    elif hook_adapter.shutil.which("apply_patch") is None:
        pytest.skip("native apply_patch executable unavailable")
    return hook_adapter


def test_preview_accepts_absolute_paths_without_writing(patch_adapter, tmp_path):
    source = tmp_path / "input.txt"
    source.write_text("old\n")
    patch = f"*** Begin Patch\n*** Update File: {source}\n@@\n-old\n+new\n*** End Patch\n"
    deltas = patch_adapter.preview_patch(patch, tmp_path)
    assert [(d.path, d.before, d.after) for d in deltas] == [(source, "old\n", "new\n")]
    assert source.read_text() == "old\n"


def test_preview_move_checks_destination_and_source(patch_adapter, tmp_path):
    source = tmp_path / "input.txt"
    target = tmp_path / "movedScript.sml"
    source.write_text("old\n")
    target.write_text("previous target\n")
    patch = "*** Begin Patch\n*** Update File: input.txt\n*** Move to: movedScript.sml\n@@\n-old\n+new\n*** End Patch\n"
    deltas = patch_adapter.preview_patch(patch, tmp_path)
    assert {d.path: (d.before, d.after) for d in deltas} == {
        source: ("old\n", ""), target: ("previous target\n", "new\n"),
    }
    assert source.read_text() == "old\n"
    assert target.read_text() == "previous target\n"


@pytest.mark.parametrize("body,expected", [
    ("@@ second\n same\n-old\n+new", "first\nsame\nold\nsecond\nsame\nnew\n"),
    ("@@\n same\n-old\n+new\n*** End of File", "first\nsame\nold\nsecond\nsame\nnew\n"),
    ("@@\n+last", "first\nsame\nold\nsecond\nsame\nold\nlast\n"),
])
def test_preview_hunk_placement(patch_adapter, tmp_path, body, expected):
    source = tmp_path / "input.txt"
    before = "first\nsame\nold\nsecond\nsame\nold\n"
    source.write_text(before)
    patch = f"*** Begin Patch\n*** Update File: input.txt\n{body}\n*** End Patch\n"
    deltas = patch_adapter.preview_patch(patch, tmp_path)
    assert deltas[0].after == expected
    assert source.read_text() == before


@pytest.mark.parametrize("before,body,expected", [
    ("old\n  old  \n", "@@\n-old\n+new\n*** End of File", "old\nnew\n"),
    ("old", "@@\n-old\n+new", "new\n"),
    ("old\n", "@@\n-old", ""),
    ("a\nb\n", "@@\n-a\n+x\n@@\n-b\n+y", "x\ny\n"),
])
def test_preview_preserves_patch_semantics(patch_adapter, tmp_path, before, body, expected):
    source = tmp_path / "input.txt"
    source.write_text(before)
    patch = f"*** Begin Patch\n*** Update File: input.txt\n{body}\n*** End Patch\n"
    deltas = patch_adapter.preview_patch(patch, tmp_path)
    assert deltas[0].after == expected
    assert source.read_text() == before


@pytest.fixture
def run_codex_hook(tmp_path):
    plugin_data = tmp_path / "plugin-data"
    real_home = tmp_path / "real-home"
    real_home.mkdir()

    def run(script, payload, *args, env=None):
        environment = os.environ.copy()
        environment.update({
            "PLUGIN_ROOT": str(ROOT),
            "PLUGIN_DATA": str(plugin_data),
            "HOME": str(real_home),
            "PYTHONDONTWRITEBYTECODE": "1",
        })
        if env:
            environment.update(env)
        return subprocess.run(
            [sys.executable, str(script), *args],
            input=json.dumps(payload), text=True, capture_output=True,
            env=environment, timeout=60, check=False,
        )

    run.plugin_data = plugin_data
    run.real_home = real_home
    return run


def payload(tmp_path, tool_name, tool_input, event="PreToolUse", session="codex-test"):
    return {
        "session_id": session,
        "turn_id": "turn-1",
        "transcript_path": None,
        "cwd": str(tmp_path),
        "hook_event_name": event,
        "tool_name": tool_name,
        "tool_input": tool_input,
    }


def test_apply_patch_is_previewed_and_banned_tactic_blocks_without_editing(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    before = "Theorem foo:\n  T\nProof\n  simp []\nQED\n"
    script.write_text(before)
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 Proof
-  simp []
+  TRY (simp [])
 QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h1_banned_tactics.py",
    )
    assert result.returncode == 2
    assert "H1" in result.stderr and "TRY" in result.stderr
    assert script.read_text() == before


def test_apply_patch_h17_ignores_inherited_noncanonical_suspend(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    before = (
        "open HolKernel Parse boolLib bossLib;\n\n"
        "Theorem old:\n  T\nProof\n  `T` by suspend \"legacy\"\nQED\n"
    )
    script.write_text(before)
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 open HolKernel Parse boolLib bossLib;
+Theorem new_lemma: T Proof simp[] QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h17_then_suspend.py",
    )
    assert result.returncode == 0, result.stderr
    assert script.read_text() == before


def test_apply_patch_h17_blocks_new_noncanonical_suspend(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    before = "Theorem foo:\n  T\nProof\n  simp[]\nQED\n"
    script.write_text(before)
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 Proof
-  simp[]
+  `T` by suspend "new_bad"
 QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h17_then_suspend.py",
    )
    assert result.returncode == 2
    assert "H17" in result.stderr and "new_bad" in result.stderr
    assert script.read_text() == before


def test_apply_patch_advisory_is_returned_as_valid_codex_json(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    script.write_text("Theorem foo:\n  T\nProof\n  cheat\nQED\n")
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 QED
+Resume foo[left]:
+  cheat
+QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h10_resume_needs_finalise.py",
    )
    assert result.returncode == 0, result.stderr
    context = json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]
    assert "Finalise foo;" in context


def test_apply_patch_add_file_is_checked(run_codex_hook, tmp_path):
    patch = """*** Begin Patch
*** Add File: newScript.sml
+Theorem foo:
+  T
+Proof
+  FIRST [simp []]
+QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h1_banned_tactics.py",
    )
    assert result.returncode == 2
    assert "FIRST" in result.stderr
    assert not (tmp_path / "newScript.sml").exists()


@pytest.mark.parametrize("fallback", [False, True])
def test_move_into_script_runs_proof_policy(run_codex_hook, tmp_path, fallback):
    source = tmp_path / "draft.txt"
    before = "Theorem foo:\n  T\nProof\n  simp []\nQED\n"
    source.write_text(before)
    target = tmp_path / "newScript.sml"
    patch = f"""*** Begin Patch
*** Update File: {source}
*** Move to: {target}
@@
-  simp []
+  TRY (simp [])
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h1_banned_tactics.py", env={"PATH": ""} if fallback else None,
    )
    assert result.returncode == 2, result.stdout + result.stderr
    assert "H1" in result.stderr and "TRY" in result.stderr
    assert source.read_text() == before
    assert not target.exists()


def test_apply_patch_fallback_does_not_depend_on_codex_internal_binary(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    script.write_text("Theorem foo:\n  T\nProof\n  simp []\nQED\n")
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 Proof
-  simp []
+  ORELSE (simp []) (cheat)
 QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h1_banned_tactics.py", env={"PATH": ""},
    )
    assert result.returncode == 2
    assert "ORELSE" in result.stderr


def test_post_tool_result_reaches_existing_advisory(run_codex_hook, tmp_path):
    call = payload(
        tmp_path,
        "mcp__hol4__hol_state_at",
        {"file": str(tmp_path / "fooScript.sml"), "line": 10},
        event="PostToolUse",
    )
    call["tool_response"] = (
        "goal state\n[Timing: total=31000ms, replay=30001ms, "
        "startup=999ms, method=replay]"
    )
    result = run_codex_hook(ADAPTER, call, "h8_state_at_replay_cost.py")
    assert result.returncode == 0, result.stderr
    context = json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]
    assert "30.0s" in context and "replay" in context


def test_prompt_capture_supplies_stable_pregrant_history(run_codex_hook, tmp_path):
    prompt = {
        "session_id": "consent-session",
        "turn_id": "turn-1",
        "cwd": str(tmp_path),
        "hook_event_name": "UserPromptSubmit",
        "prompt": "skip prefix ok for this investigation",
    }
    captured = run_codex_hook(CODEX / "prompt_capture.py", prompt)
    assert captured.returncode == 0
    call = payload(
        tmp_path, "mcp__hol4__hol_state_at",
        {"file": str(tmp_path / "fooScript.sml"), "line": 10, "skip_prefix": True},
        session="consent-session",
    )
    result = run_codex_hook(ADAPTER, call, "h31_skip_prefix_consent.py")
    assert result.returncode == 0, result.stderr
    assert "pre-granted" in json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]


def test_hook_state_is_redirected_away_from_real_claude_home(run_codex_hook, tmp_path):
    call = payload(
        tmp_path, "mcp__hol4__hol_state_at",
        {"file": str(tmp_path / "fooScript.sml"), "line": 10, "skip_prefix": True},
        session="isolated-session",
    )
    result = run_codex_hook(ADAPTER, call, "h31_skip_prefix_consent.py")
    assert result.returncode == 2
    assert not (run_codex_hook.real_home / ".claude").exists()
    isolated = run_codex_hook.plugin_data / "runtime-home" / ".claude" / "hook-state"
    assert isolated.is_dir()


def test_session_context_is_codex_native(run_codex_hook, tmp_path):
    (tmp_path / "Holmakefile").write_text("")
    start = {
        "session_id": "start-session",
        "cwd": str(tmp_path),
        "hook_event_name": "SessionStart",
        "source": "startup",
    }
    result = run_codex_hook(CODEX / "session_context.py", start)
    assert result.returncode == 0
    context = json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]
    assert "hol4-proving" in context
    assert "Claude" not in context and "settings.json" not in context


def test_plugin_files_reference_only_existing_codex_components():
    manifest = json.loads((ROOT / ".codex-plugin" / "plugin.json").read_text())
    hooks = json.loads((ROOT / "hooks" / "hooks.json").read_text())
    assert manifest["skills"] == "./skills/"
    assert manifest["mcpServers"]["hol4"]["tool_timeout_sec"] >= 600
    # A developer's own .mcp.json may sit in the checkout; only a tracked one
    # would ship with the plugin.
    tracked = subprocess.run(["git", "ls-files", "--", ".mcp.json"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout
    assert not tracked.strip()
    commands = [
        handler["command"]
        for groups in hooks["hooks"].values()
        for group in groups
        for handler in group["hooks"]
    ]
    assert all("${PLUGIN_ROOT}" in command for command in commands)
    assert not any("h14_git_destructive_consent.py" in command for command in commands)
    assert not any("h22_hol4_context.py" in command for command in commands)


def test_wired_build_poll_and_cancel_do_not_consume_stale_navigation_override(run_codex_hook, tmp_path):
    root = tmp_path / "repo"
    (root / "lib/.hol/objs").mkdir(parents=True)
    (root / "app").mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    ancestor = root / "lib/libScript.sml"
    ancestor.write_text("Theory lib\nTheorem example:\n T\nProof\n simp[]\nQED\n")
    artifact = root / "lib/.hol/objs/libTheory.dat"
    artifact.write_text("old artifact")
    os.utime(artifact, (time.time() - 100, time.time() - 100))
    script = root / "app/appScript.sml"
    script.write_text("Theory app\nAncestors\n lib\nTheorem target:\n T\nProof\n simp[]\nQED\n")
    (root / "app/Holmakefile").write_text("INCLUDES = ../lib\n")
    wiring = json.loads((ROOT / "hooks/hooks.json").read_text())
    group = next(g for g in wiring["hooks"]["PreToolUse"] if g["matcher"] == "^mcp__hol4__")
    hooks = shlex.split(group["hooks"][0]["command"])[2:]
    nav = payload(root, "mcp__hol4__hol_state_at", {"file": str(script), "line": 6})
    denied = run_codex_hook(ADAPTER, nav, *hooks)
    assert denied.returncode == 2 and "libScript.sml" in denied.stderr, denied
    state = run_codex_hook.plugin_data / "runtime-home/.claude/hook-state/codex-test/soft_blocks.json"
    before = state.read_bytes()
    for tool, args in [
        ("holmake", {"workdir": str(root / "lib"), "target": "libTheory.uo"}),
        ("hol_build_status", {"job": "existing-job"}),
        ("hol_build_status", {"job": "existing-job", "cancel": True}),
    ]:
        result = run_codex_hook(ADAPTER, payload(root, "mcp__hol4__" + tool, args), *hooks)
        assert result.returncode == 0 and "OVERRIDDEN" not in result.stdout, result
        assert state.read_bytes() == before
    retried = run_codex_hook(ADAPTER, nav, *hooks)
    assert retried.returncode == 0 and "H30 OVERRIDDEN" in retried.stdout, retried
    assert not (run_codex_hook.real_home / ".claude").exists()


@pytest.mark.parametrize("script,event,tool", [
    ("h7_holmake_advisory.py", "PreToolUse", "mcp__hol4__holmake"),
    ("h1_banned_tactics.py", "PreToolUse", "Bash"),
])
def test_adapter_skips_hooks_outside_declared_scope(tmp_path, monkeypatch, script, event, tool):
    monkeypatch.syspath_prepend(str(CODEX))
    monkeypatch.setenv("PLUGIN_ROOT", str(ROOT))
    monkeypatch.setenv("PLUGIN_DATA", str(tmp_path / "plugin-data"))
    import hook_adapter

    def unexpected(*args, **kwargs):
        pytest.fail("out-of-scope hook must not be launched")

    monkeypatch.setattr(hook_adapter.subprocess, "run", unexpected)
    result = hook_adapter._run(script, payload(tmp_path, tool, {}, event=event))
    assert result.returncode == 0 and not result.stdout and not result.stderr


def test_adapter_preserves_matching_hook_refusal(tmp_path, monkeypatch):
    monkeypatch.syspath_prepend(str(CODEX))
    monkeypatch.setenv("PLUGIN_ROOT", str(ROOT))
    monkeypatch.setenv("PLUGIN_DATA", str(tmp_path / "plugin-data"))
    import hook_adapter
    call = payload(tmp_path, "Edit", {"new_string": "TRY (simp[])"})
    invocations = []

    def refused(*args, **kwargs):
        invocations.append(json.loads(kwargs["input"]))
        return subprocess.CompletedProcess(args[0], 2, "", "H1 refuses TRY")

    monkeypatch.setattr(hook_adapter.subprocess, "run", refused)
    result = hook_adapter._run("h1_banned_tactics.py", call)
    assert result.returncode == 2 and "H1" in result.stderr
    assert invocations == [call]
