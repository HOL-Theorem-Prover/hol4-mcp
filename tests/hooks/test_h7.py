"""H7 (holmake RULE A reminder) speaks only on the edit-then-rebuild
signature: the first build of a (workdir, target) and a retry with no script
edited since are silent; a rebuild after a *Script.sml edit gets the
reminder, worded for that loop."""
import json
import os
import time

import pytest


HOOK = "h7_holmake_advisory.py"
SESSION = "h7-session"


def build(run_hook, workdir, target="fooTheory"):
    return run_hook(HOOK, "mcp__hol4__holmake", {"workdir": str(workdir), "target": target},
                    event="PostToolUse", tool_response="Build succeeded.\n[3.0s]",
                    session_id=SESSION)


@pytest.fixture
def workdir(tmp_path):
    d = tmp_path / "thy"
    d.mkdir()
    (d / "fooScript.sml").write_text("Theory foo\nTheorem t:\n T\nProof\n simp[]\nQED\n")
    return d


def test_first_build_is_silent(run_hook, workdir):
    code, _, out = build(run_hook, workdir)
    assert code == 0
    assert out.strip() == "", out


def test_rebuild_without_edit_is_silent(run_hook, workdir):
    build(run_hook, workdir)
    code, _, out = build(run_hook, workdir)
    assert code == 0
    assert out.strip() == "", out


def test_rebuild_after_script_edit_gets_reminder(run_hook, workdir):
    build(run_hook, workdir)
    script = workdir / "fooScript.sml"
    script.write_text(script.read_text().replace("simp[]", "rw[]"))
    code, _, out = build(run_hook, workdir)
    assert code == 0
    ctx = json.loads(out)["hookSpecificOutput"]["additionalContext"]
    assert "H7" in ctx and "RULE A" in ctx
    assert "edit" in ctx.lower() and "rebuil" in ctx.lower()


def test_rebuild_after_successful_qed_navigation_is_silent(run_hook, workdir):
    build(run_hook, workdir)
    script = workdir / "fooScript.sml"
    script.write_text(script.read_text().replace("simp[]", "rw[]"))
    checked = run_hook(
        "h25_proof_text_sweep.py", "mcp__hol4__hol_state_at",
        {"file": str(script), "line": 6}, event="PostToolUse",
        tool_response="Theorem: t\nProof position\n\n=== Goals ===\nNo goals (proof complete)",
        session_id=SESSION,
    )
    assert checked[0] == 0
    assert build(run_hook, workdir)[2] == ""


def test_every_changed_proof_must_be_validated(run_hook, workdir):
    script = workdir / "fooScript.sml"
    script.write_text(script.read_text() + "\nTheorem u:\n T\nProof\n simp[]\nQED\n")
    build(run_hook, workdir)
    script.write_text(script.read_text().replace("simp[]", "rw[]"))
    run_hook(
        "h25_proof_text_sweep.py", "mcp__hol4__hol_check_proof",
        {"file": str(script)}, event="PostToolUse",
        tool_response="Theorem: t\nLines: 2-6\nStatus: OK (1ms, 1 steps)",
        session_id=SESSION,
    )
    output = build(run_hook, workdir)[2]
    assert "H7" in output


def test_assertion_only_rebuild_is_silent(run_hook, workdir):
    script = workdir / "fooScript.sml"
    script.write_text('Theory foo\nval _ = assert (K true) ();\n')
    build(run_hook, workdir)
    script.write_text(script.read_text() + 'val _ = assert (K true) 1;\n')
    assert build(run_hook, workdir)[2] == ""


def test_translation_prefix_edit_is_not_a_proof_edit(run_hook, workdir):
    build(run_hook, workdir)
    script = workdir / "fooScript.sml"
    script.write_text('val _ = translate foo_def;\n' + script.read_text())
    assert build(run_hook, workdir)[2] == ""


def test_edit_to_other_script_does_not_blame_target(run_hook, workdir):
    build(run_hook, workdir)
    (workdir / "barScript.sml").write_text("Theorem t:\n T\nProof\n rw[]\nQED\n")
    assert build(run_hook, workdir)[2] == ""


def test_touch_without_content_edit_is_silent(run_hook, workdir):
    build(run_hook, workdir)
    future = time.time() + 5
    os.utime(workdir / "fooScript.sml", (future, future))
    assert build(run_hook, workdir)[2] == ""


def test_other_target_is_a_first_build(run_hook, workdir):
    build(run_hook, workdir)
    (workdir / "barScript.sml").write_text("Theory bar\n")
    code, _, out = build(run_hook, workdir, target="barTheory")
    assert code == 0
    assert out.strip() == "", out
