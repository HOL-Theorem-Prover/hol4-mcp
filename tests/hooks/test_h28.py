"""H28 (shell Holmake/poly/hol blocker): command-position matching must not
fire on quoted strings, heredoc bodies, assignments or version/help queries,
and must keep firing on every real build/REPL invocation."""
import pytest


PASS_CASES = [
    pytest.param('pgrep -a -f "Holmake|hol.state|poly"', id="pgrep-quoted"),
    pytest.param('ps -ef | grep -iE "Holmake|polyml|poly "', id="ps-grep-quoted"),
    pytest.param("awk '$2 ~ /hol|poly/' procs.txt", id="awk-single-quoted"),
    pytest.param('grep -E "olmake| hol " log.txt', id="grep-quoted-space"),
    pytest.param("hol=$(grep -c x f); echo $hol", id="shell-assignment"),
    pytest.param("cat <<'EOF' > s.py\nhol = {'a': 1}\nprint(hol)\nEOF", id="heredoc-body"),
    pytest.param("echo $(poly -v)", id="poly-version"),
    pytest.param("Holmake --help", id="holmake-help"),
    # Already pass today: prose, paths, comments.
    pytest.param("ls .hol/logs/ && cat .hol/logs/holmake.log", id="log-path"),
    pytest.param("grep Holmake README.md", id="prose-argument"),
]

BLOCK_CASES = [
    pytest.param("Holmake --qof", id="holmake-qof"),
    pytest.param("nohup Holmake -j4 &", id="nohup-holmake"),
    pytest.param("cd d && Holmake fooTheory.dat", id="cd-holmake-target"),
    pytest.param("time Holmake", id="time-holmake"),
    pytest.param("hol < probe.sml", id="hol-stdin"),
    pytest.param("poly --script x.sml", id="poly-script"),
    pytest.param("HOLDIR=/x Holmake", id="env-assign-holmake"),
    pytest.param('echo "$(Holmake -j2)"', id="holmake-in-quoted-subst"),
    pytest.param("cat <<EOF\n$(Holmake)\nEOF", id="holmake-in-unquoted-heredoc"),
]


@pytest.mark.parametrize("cmd", PASS_CASES)
def test_allows(run_hook, cmd):
    code, err, _ = run_hook("h28_shell_hol_build.py", "Bash", {"command": cmd})
    assert code == 0, err


@pytest.mark.parametrize("cmd", BLOCK_CASES)
def test_blocks(run_hook, cmd):
    code, err, _ = run_hook("h28_shell_hol_build.py", "Bash", {"command": cmd})
    assert code == 2
    assert "H28" in err


def test_consent_phrase_allows(run_hook):
    code, _, _ = run_hook("h28_shell_hol_build.py", "Bash", {"command": "Holmake"},
                          user_msg="fine, shell holmake ok")
    assert code == 0
