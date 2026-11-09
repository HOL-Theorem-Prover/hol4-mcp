"""Discovery tracing is explicit, actionable, and absent from regular builds."""
import json
import os
from pathlib import Path
import re
import shlex
import sys
import pytest

from hol4_mcp.build_evidence import traced_build, build_failure_heading
from hol4_mcp import hol_mcp_server as srv


def test_regular_build_does_no_trace_setup(tmp_path, monkeypatch):
    def unexpected(*args, **kwargs):
        raise AssertionError("regular build must not look for a tracer")
    monkeypatch.setattr("hol4_mcp.build_evidence.shutil.which", unexpected)
    command = ["Holmake", "target"]
    assert traced_build(command, tmp_path, False, {}) == (command, "")
    assert list(tmp_path.iterdir()) == []


async def test_missing_tracer_fails_before_build(tmp_path, monkeypatch):
    monkeypatch.setattr("hol4_mcp.build_evidence.shutil.which", lambda *a, **k: None)
    (tmp_path / "Holmakefile").write_text("result:\n\ttouch result\n")
    result = await srv.holmake(str(tmp_path), target="result", trace_discovery=True)
    assert "no build was started" in result, result
    assert not (tmp_path / "result").exists()


async def test_trace_exposes_failed_chdir_and_namespace(tmp_path):
    missing = tmp_path / "disappeared-directory"
    python = shlex.quote(sys.executable)
    worker = tmp_path / "worker.py"
    worker.write_text(f"import os\nos.chdir({str(missing)!r})\n")
    (tmp_path / "Holmakefile").write_text(f"result:\n\t{python} worker.py\n")
    result = await srv.holmake(str(tmp_path), target="result", trace_discovery=True, timeout=30)
    if "PTRACE_TRACEME: Operation not permitted" in result:
        assert "not a proof-failure verdict" in result
        pytest.skip("sandbox denies ptrace; run this integration test with tracing permission")
    assert "Build failed" in result, result
    trace = Path(re.search(r"Discovery trace: ([^;]+);", result).group(1))
    assert trace.exists(), result
    output = trace.read_text()
    assert re.search(r'chdir\("' + re.escape(str(missing)) + r'"\).*ENOENT', output), output[-4000:]
    metadata = json.loads(trace.with_suffix(".json").read_text())
    assert metadata["workdir"] == str(tmp_path)
    assert metadata["mount_namespace"] == os.readlink("/proc/self/ns/mnt")
    assert metadata["command"][-1] == "result"
    assert not missing.exists()  # diagnosis must not create/ignore the missing source


def test_traces_live_outside_the_project_and_only_the_newest_are_kept(tmp_path, monkeypatch):
    monkeypatch.setattr("hol4_mcp.build_evidence.shutil.which", lambda *a, **k: "/bin/true")
    from hol4_mcp import build_evidence
    from hol4_mcp import build_coordination as coordination
    (tmp_path / "root").mkdir()
    monkeypatch.setattr(coordination, "storage_root", lambda: tmp_path / "root")
    for _ in range(build_evidence.TRACES_KEPT + 2):
        _, note = traced_build(["Holmake", "target"], tmp_path / "project", True, {})
        trace = Path(re.search(r"Discovery trace: ([^;]+);", note).group(1))
        assert trace.parent == tmp_path / "root" / "discovery"
        trace.write_text("trace")
    kept = sorted((tmp_path / "root" / "discovery").glob("*.log"))
    assert len(kept) == build_evidence.TRACES_KEPT
    assert all(p.with_suffix(".json").exists() for p in kept)
    assert not (tmp_path / "project").exists()
    assert "do not retrace retries" in note


def test_tracer_permission_failure_is_not_a_proof_verdict():
    output = "/usr/bin/strace: is_exitkill_supported: PTRACE_TRACEME: Operation not permitted"
    result = build_failure_heading(1, output, True)
    assert "not a proof-failure verdict" in result and "permissions" in result
    assert build_failure_heading(1, "genuine theorem failure", False) == "Build failed (exit code 1)."
