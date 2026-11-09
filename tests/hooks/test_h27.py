"""H27 (audit gates at commit time) must judge only what the commit introduces:
an `--amend` that changes a statement line is not a proof edit, a lone `>-`
is H25's advisory and not a blocker, while a body edit adding `cheat` is."""
import subprocess
import importlib.util
from pathlib import Path

import pytest

_spec = importlib.util.spec_from_file_location(
    "git_commit_snapshot", Path(__file__).resolve().parents[2] / "hooks/git_commit_snapshot.py")
_snapshot_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_snapshot_module)


SCRIPT = """\
open HolKernel boolLib bossLib;

val _ = new_theory "foo";

Theorem foo_one:
  !x. x + 0 = x
Proof
  rw [] >> TRY (simp [])
  >> simp []
  >> fs []
QED

Theorem foo_two:
  !x. 0 + x = x
Proof
  rw [] >> strip_tac
  >- metis_tac []
QED

val _ = export_theory();
"""


def git(repo, *args):
    subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args],
                   cwd=repo, check=True, capture_output=True, text=True)


@pytest.fixture
def repo(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    (repo / "README").write_text("foo\n")
    git(repo, "add", "README")
    git(repo, "commit", "-q", "-m", "init")
    (repo / "fooScript.sml").write_text(SCRIPT)
    git(repo, "add", "fooScript.sml")
    git(repo, "commit", "-q", "-m", "A")
    return repo


def stage(repo, old, new):
    p = repo / "fooScript.sml"
    text = p.read_text()
    assert old in text
    p.write_text(text.replace(old, new))
    git(repo, "add", "fooScript.sml")


def run(run_hook, repo, command="git commit --amend --no-edit"):
    return run_hook("h27_commit_audit_gate.py", "Bash", {"command": command}, cwd=repo)


def test_amend_with_statement_only_retype_passes(run_hook, repo):
    stage(repo, "!x. x + 0 = x", "!y. y + 0 = y")
    code, err, _ = run(run_hook, repo)
    assert code == 0, err


def test_lone_dispatcher_is_not_a_blocker(run_hook, repo):
    stage(repo, "rw [] >> strip_tac\n  >- metis_tac []", "rw [ADD] >> strip_tac\n  >- metis_tac []")
    code, err, _ = run(run_hook, repo, "git commit -m 'retouch foo_two'")
    assert code == 0, err


def test_short_sibling_dispatch_ladder_is_not_a_blocker(run_hook, repo):
    stage(repo, "rw [] >> strip_tac\n  >- metis_tac []",
          "Cases_on `x`\n  >- simp []\n  >- metis_tac []")
    code, err, _ = run(run_hook, repo, "git commit -m 'dispatch foo_two'")
    assert code == 0, err


def test_retouched_line_keeps_its_inherited_finding(run_hook, repo):
    p = repo / "fooScript.sml"
    p.write_text(SCRIPT.replace(
        "val _ = export_theory();",
        "Theorem bar:\n  T\nProof\n  rw []\n  >> fs [fooTheory.x_def]\nQED\n\n"
        "val _ = export_theory();"))
    git(repo, "add", "fooScript.sml")
    git(repo, "commit", "-qm", "fixture")
    stage(repo, "fs [fooTheory.x_def]", "fs [barTheory.x_def]")
    code, err, _ = run(run_hook, repo, "git commit -m 'rename'")
    assert code == 0, err
    # A retouch that also creates a new adjacency is still judged new.
    stage(repo, "  >> fs [barTheory.x_def]",
          "  >> fs [barTheory.x_def]\n  >> gvs []\n  >> simp []")
    code, err, _ = run(run_hook, repo, "git commit -m 'rename'")
    assert code == 2 and "adjacent normalisers `gvs >> simp`" in err, err


def test_amend_body_edit_adding_cheat_is_refused(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    code, err, _ = run(run_hook, repo)
    assert code == 2
    assert "Gate 3" in err


def test_amend_judges_only_the_touched_theorem(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    code, err, _ = run(run_hook, repo)
    assert code == 2
    assert "foo_one" not in err, "untouched theorem must not be judged"


def test_body_edit_in_touched_theorem_is_swept(run_hook, repo):
    stage(repo, "  rw [] >> TRY (simp [])", "  rw [ADD] >> TRY (simp [])")
    code, err, _ = run(run_hook, repo, "git commit -m 'x'")
    assert code == 2
    assert "Gate 5" in err
    assert "adjacent normalisers" not in err, "unchanged inherited findings are not new defects"
    assert "foo_two" not in err


def test_inherited_style_in_touched_theorem_passes(run_hook, repo):
    stage(repo, "  >> fs []", "  >> fs []\n  >> ALL_TAC")
    code, err, _ = run(run_hook, repo)
    assert code == 0, err


def test_staged_cheat_not_hidden_by_unstaged_cleanup(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    (repo / "fooScript.sml").write_text(SCRIPT)
    code, err, _ = run(run_hook, repo)
    assert code == 2 and "Gate 3" in err


def test_unstaged_cheat_not_audited_for_index_commit(run_hook, repo):
    stage(repo, "!x. 0 + x = x", "!y. 0 + y = y")
    p = repo / "fooScript.sml"
    p.write_text(p.read_text().replace("  >- metis_tac []", "  >- cheat"))
    assert run(run_hook, repo)[0] == 0
    code, err, _ = run(run_hook, repo, "git commit -am 'checkpoint'")
    assert code == 2 and "Gate 3" in err


@pytest.mark.parametrize("flags", ["--only", ""])
def test_path_commit_excludes_other_staged_files(run_hook, repo, flags):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    (repo / "README").write_text("changed\n")
    code, err, _ = run(run_hook, repo, f"git commit {flags} -m note -- README")
    assert code == 0, err
    assert run(run_hook, repo, "git commit --include -m note -- README")[0] == 2


def test_only_reads_selected_worktree_content(run_hook, repo):
    p = repo / "fooScript.sml"
    p.write_text(SCRIPT.replace("  >- metis_tac []", "  >- cheat"))
    code, err, _ = run(run_hook, repo, "git commit -m x -- fooScript.sml")
    assert code == 2 and "Gate 3" in err


def test_message_is_not_parsed_as_flags(run_hook, repo):
    (repo / "fooScript.sml").write_text(SCRIPT.replace("  >- metis_tac []", "  >- cheat"))
    assert run(run_hook, repo, "git commit -m 'document --all and -a'")[0] == 0


def test_quoted_repo_path(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    spaced = repo.with_name("repo with spaces")
    repo.rename(spaced)
    code, err, _ = run(run_hook, spaced, f"git -C '{spaced}' commit -m x")
    assert code == 2 and "Gate 3" in err


def test_staging_and_commit_must_be_separate_calls(run_hook, repo):
    code, err, _ = run(run_hook, repo, "git add fooScript.sml && git commit -m x")
    assert code == 2 and "separate tool calls" in err


@pytest.mark.parametrize("command", [
    "bash -c 'git commit -m x'", "env git commit -m x",
    'git commit -m "$(git add fooScript.sml)"',
])
def test_unmodelled_shell_commit_cannot_silently_bypass_audit(run_hook, repo, command):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    code, err, _ = run(run_hook, repo, command)
    assert code == 2 and "cannot determine the proposed commit" in err


def test_literal_commit_prose_is_not_a_commit_or_substitution(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    assert run(run_hook, repo, "echo 'git commit -m x'")[0] == 0
    assert run(run_hook, repo, "git log --grep='git commit'")[0] == 0


def test_wip_ok_in_latest_message_overrides(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    command = "git commit -m checkpoint"
    code, err, _ = run(run_hook, repo, command)
    assert code == 2 and "say `wip ok`" in err
    code, err, _ = run_hook("h27_commit_audit_gate.py", "Bash", {"command": command},
                            cwd=repo, user_msg="git ok wip ok")
    assert code == 0, err
    # The override waives the whole audit, unmodelled command shapes included.
    code, err, _ = run_hook("h27_commit_audit_gate.py", "Bash",
                            {"command": "bash -c 'git commit -m x'"},
                            cwd=repo, user_msg="git ok wip ok")
    assert code == 0, err


HEREDOC_MESSAGE = '''git commit -m "$(cat <<'EOF'
fix: retouch

Body paragraph.
EOF
)"'''


def test_heredoc_message_is_audited_not_refused(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    code, err, _ = run(run_hook, repo, HEREDOC_MESSAGE)
    assert code == 2 and "Gate 3" in err, err
    stage(repo, "  >- cheat", "  >- metis_tac []")
    code, err, _ = run(run_hook, repo, HEREDOC_MESSAGE)
    assert code == 0, err
    # An unquoted heredoc is fine too, unless its body carries a substitution.
    assert run(run_hook, repo, HEREDOC_MESSAGE.replace("<<'EOF'", "<<EOF"))[0] == 0
    nested = HEREDOC_MESSAGE.replace("Body paragraph.", "$(git add fooScript.sml)")
    code, err, _ = run(run_hook, repo, nested.replace("<<'EOF'", "<<EOF"))
    assert code == 2 and "cannot determine the proposed commit" in err


def test_repository_without_scripts_is_not_gated(run_hook, tmp_path):
    plain = tmp_path / "plain"
    plain.mkdir()
    git(plain, "init", "-q")
    (plain / "README").write_text("x\n")
    git(plain, "add", "README")
    for command in ("git add README && git commit -m x", "bash -c 'git commit -m x'",
                    "git -c user.name=me commit -S -m x", "git commit -m x && git push"):
        code, err, _ = run_hook("h27_commit_audit_gate.py", "Bash",
                                {"command": command}, cwd=plain)
        assert code == 0, (command, err)
    # Outside any repository the audit is vacuous as well.
    code, err, _ = run_hook("h27_commit_audit_gate.py", "Bash",
                            {"command": "git commit -m x"}, cwd=tmp_path)
    assert code == 0, err


def test_gate_follows_cd_and_git_C_to_the_script_repository(run_hook, repo, tmp_path):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    for command in (f"git -C '{repo}' commit -m x && git push",
                    f"cd '{repo}' && git commit -m x && git push"):
        code, err, _ = run_hook("h27_commit_audit_gate.py", "Bash",
                                {"command": command}, cwd=tmp_path)
        assert code == 2 and "separate tool calls" in err, (command, err)


def test_gate_covers_repository_from_script_free_subdirectory(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    subdir = repo / "docs"
    subdir.mkdir()
    index = (repo / ".git/index").read_bytes()
    for cwd in (repo, subdir):
        code, err, _ = run(run_hook, cwd, "git commit -m checkpoint")
        assert code == 2 and "Gate 3" in err, (cwd, err)
    assert (repo / ".git/index").read_bytes() == index


@pytest.mark.parametrize("relative", [False, True])
def test_gate_resolves_all_git_C_options(run_hook, repo, tmp_path, relative):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    plain = tmp_path / "plain"
    plain.mkdir()
    git(plain, "init", "-q")
    destination = "../repo" if relative else str(repo)
    command = f"git -C '{plain}' -C '{destination}' commit -m checkpoint"
    code, err, _ = run(run_hook, tmp_path, command)
    assert code == 2 and "Gate 3" in err, err
    # Unsupported compound forms must still be refused in the final repository.
    code, err, _ = run(run_hook, tmp_path, command + " && git push")
    assert code == 2 and "separate tool calls" in err, err
    # Resolving to a non-HOL repository must not retain the first one's scope.
    command = f"git -C '{repo}' -C '{plain}' commit -m note && git push"
    assert run(run_hook, tmp_path, command)[0] == 0


def test_gate_uses_commit_repository_not_preceding_git_command(run_hook, repo, tmp_path):
    plain = tmp_path / "plain"
    plain.mkdir()
    git(plain, "init", "-q")
    command = f"git -C '{plain}' status && git -C '{repo}' commit -m checkpoint"
    code, err, _ = run(run_hook, tmp_path, command)
    assert code == 2 and "separate tool calls" in err, err


def test_repository_scan_includes_scripts_in_other_subdirectories(repo):
    nested = repo / "proofs"
    nested.mkdir()
    git(repo, "mv", "fooScript.sml", "proofs/fooScript.sml")
    docs = repo / "docs"
    docs.mkdir()
    assert _snapshot_module.tracks_scripts(str(docs))


def test_deleted_finalise_is_blocked(run_hook, repo):
    p = repo / "fooScript.sml"
    p.write_text('Theorem t:\n T\nProof\n suspend "a"\nQED\n'
                 'Resume t[a]:\n simp[]\nQED\nFinalise t;\n')
    git(repo, "add", "fooScript.sml")
    git(repo, "commit", "-qm", "fixture")
    p.write_text(p.read_text().replace("Finalise t;\n", ""))
    git(repo, "add", "fooScript.sml")
    code, err, _ = run(run_hook, repo)
    assert code == 2 and "Gate 2" in err


@pytest.mark.parametrize("args", [
    ["-m", "x"], ["-am", "x"], ["--amend", "--no-edit"],
    ["--only", "-m", "x", "--", "README"],
    ["--include", "-m", "x", "--", "README"],
    ["-m", "x", "--", "fooScript.sml"],
])
def test_snapshot_matches_real_git_commit_without_changing_index(repo, args):
    import shlex
    stage(repo, "  >- metis_tac []", "  >- cheat")
    source = repo / "fooScript.sml"
    source.write_text(source.read_text().replace("  >- cheat", "  >- simp[]"))
    (repo / "README").write_text("changed\n")
    index = (repo / ".git/index").read_bytes()
    _, files = _snapshot_module.snapshot(shlex.join(["git", "commit", *args]), str(repo))
    assert (repo / ".git/index").read_bytes() == index
    git(repo, "commit", *args)
    actual = subprocess.run(["git", "show", "HEAD:fooScript.sml"], cwd=repo,
                            check=True, capture_output=True, text=True).stdout
    expected = files.get("fooScript.sml", (SCRIPT, SCRIPT))[1]
    assert actual == expected
