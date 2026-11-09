"""Build safety must hold across independent MCP server lifetimes."""

import asyncio
import json
import os
from pathlib import Path
import re
import shlex
import signal
import sys

import pytest

from hol4_mcp import hol_mcp_server as srv
from hol4_mcp import build_coordination as coordination


async def _wait_for_job_finished(job, timeout=10):
    async def finished():
        while srv._build_jobs[job].finished is None:
            await asyncio.sleep(.01)
    await asyncio.wait_for(finished(), timeout)


async def _foreign_build(workdir, target="result", tempdir=None):
    code = ("import asyncio,sys; from hol4_mcp import hol_mcp_server as s; "
            "print(asyncio.run(s.holmake(sys.argv[1],target=sys.argv[2],timeout=10)))")
    proc = await asyncio.create_subprocess_exec(
        sys.executable, "-c", code, str(workdir), target,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
        start_new_session=True,
        env={**os.environ, "TMPDIR": str(tempdir)} if tempdir is not None else None,
    )
    try:
        stdout, stderr = await asyncio.wait_for(proc.communicate(), 30)
        assert proc.returncode == 0, stderr.decode(errors="replace")
        return stdout.decode()
    finally:
        await srv._kill_process_group(proc)


async def _exiting_controller(workdir, target):
    code = '''import asyncio,json,os,re,sys
from pathlib import Path
from hol4_mcp import hol_mcp_server as s
async def main():
    result = await s.holmake(sys.argv[1],target=sys.argv[2],detach=True)
    match = re.search(r"job=(\\S+)",result)
    assert match,result
    job = match.group(1)
    while not (Path(sys.argv[1]) / "started").exists():
        if s._build_jobs[job].proc.returncode is not None:
            raise RuntimeError(await s.hol_build_status(job))
        await asyncio.sleep(.01)
    print(json.dumps({"job":job,"pid":s._build_jobs[job].proc.pid}),flush=True)
    os._exit(0)
asyncio.run(main())
'''
    proc = await asyncio.create_subprocess_exec(
        sys.executable, "-c", code, str(workdir), target,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
        start_new_session=True,
    )
    try:
        stdout, stderr = await asyncio.wait_for(proc.communicate(), 30)
        assert proc.returncode == 0, stderr.decode(errors="replace")
        return json.loads(stdout)
    finally:
        await srv._kill_process_group(proc)


def _shared_fixture(tmp_path, artifact="ready"):
    shared = tmp_path / "shared"
    shared.mkdir()
    output = f".hol/objs/{artifact}" if artifact.endswith(".ui") else artifact
    python = shlex.quote(sys.executable)
    (shared / "worker.py").write_text(
        "from pathlib import Path\nimport time\n"
        f"out = Path({output!r})\nout.parent.mkdir(parents=True,exist_ok=True)\n"
        "out.write_text('partial')\nPath('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "out.write_text('complete')\n")
    (shared / "Holmakefile").write_text(f"{artifact}:\n\t{python} worker.py\n")
    peer = tmp_path / "peer"
    peer.mkdir()
    (peer / "Holmakefile").write_text(
        f"INCLUDES = ../shared\nresult: ../shared/{artifact}\n\t{python} -c "
        f"\"from pathlib import Path; Path('result').write_text(Path('../shared/{output}').read_text())\"\n")
    return shared, peer, shared / output


async def _started(root):
    async def wait():
        while not (root / "started").exists():
            await asyncio.sleep(.01)
    await asyncio.wait_for(wait(), 10)


@pytest.mark.parametrize("private_tmp", [False, True])
async def test_separate_server_refuses_late_reader_and_can_retry(tmp_path, private_tmp):
    shared, peer, output = _shared_fixture(tmp_path)
    result = await srv.holmake(str(shared), target="ready", detach=True)
    job = re.search(r"job=(\S+)", result).group(1)
    tempdir = tmp_path / "private-tmp" if private_tmp else None
    if tempdir is not None:
        tempdir.mkdir()
    try:
        await _started(shared)
        result = await _foreign_build(peer, tempdir=tempdir)
        assert result.startswith("ERROR:") and "overlap" in result.lower(), result
        assert job in result and str(shared) in result, result
        assert not (peer / "result").exists()
        (shared / "release").touch()
        await _wait_for_job_finished(job)
        result = await _foreign_build(peer, tempdir=tempdir)
        assert "Build succeeded" in result, result
        assert (peer / "result").read_text() == "complete"
    finally:
        (shared / "release").touch()
        await srv.hol_build_status(job, cancel=True)


@pytest.mark.parametrize("artifact", ["ready", "ready.ui"])
async def test_failed_output_remains_suspect_in_a_new_server(tmp_path, artifact):
    shared, peer, output = _shared_fixture(tmp_path, artifact)
    result = await srv.holmake(str(shared), target=artifact, detach=True)
    job = re.search(r"job=(\S+)", result).group(1)
    try:
        await _started(shared)
        await srv.hol_build_status(job, cancel=True)
        result = await _foreign_build(peer)
        assert result.startswith("ERROR:") and "partial" in result.lower(), result
        assert job in result and str(output) in result, result
        assert not (peer / "result").exists()
        output.unlink()
        (shared / "release").touch()
        result = await _foreign_build(peer)
        assert "Build succeeded" in result, result
        assert (peer / "result").read_text() == "complete"
    finally:
        (shared / "release").touch()
        await srv.hol_build_status(job, cancel=True)


async def test_orphaned_job_keeps_its_reservation_then_certifies_itself(tmp_path):
    shared, peer, output = _shared_fixture(tmp_path)
    foreign = await _exiting_controller(shared, "ready")
    try:
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert result.startswith("ERROR:") and "overlap" in result.lower(), result
        assert foreign["job"] in result, result
        assert not (peer / "result").exists()
        (shared / "release").touch()
        # The vanished controller cannot certify the job, but the job's wrapper
        # records Holmake's exit status as it ends; the next build to meet the
        # output applies it instead of treating the output as unverified.
        async def released():
            while True:
                result = await srv.holmake(str(peer), target="result", timeout=10)
                if "overlap" not in result.lower():
                    return result
                await asyncio.sleep(.02)
        result = await asyncio.wait_for(released(), 10)
        assert "Build succeeded" in result, result
        assert (peer / "result").read_text() == "complete"
        record = coordination.read_job(foreign["job"])
        assert record and record["finalized"]["returncode"] == 0, record
    finally:
        (shared / "release").touch()
        try:
            os.killpg(foreign["pid"], signal.SIGTERM)
        except ProcessLookupError:
            pass


async def test_foreign_builds_in_one_directory_conflict_only_on_a_shared_unit(tmp_path):
    shared, peer, output = _shared_fixture(tmp_path)
    (shared / "Holmakefile").write_text(
        (shared / "Holmakefile").read_text() + "\nother:\n\ttouch other\n")
    foreign = await _exiting_controller(shared, "ready")
    try:
        # An independent target in the writer's own directory is admitted.
        result = await srv.holmake(str(shared), target="other", timeout=10)
        assert "Build succeeded" in result, result
        assert (shared / "other").exists()
        # The unit being written is not, and the refusal names its holder.
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert result.startswith("ERROR:") and "overlap" in result.lower(), result
        assert foreign["job"] in result and "server pid" in result, result
    finally:
        (shared / "release").touch()
        try:
            os.killpg(foreign["pid"], signal.SIGTERM)
        except ProcessLookupError:
            pass


async def test_adopted_job_reports_running_then_done(tmp_path):
    shared, peer, output = _shared_fixture(tmp_path)
    foreign = await _exiting_controller(shared, "ready")
    try:
        status = await srv.hol_build_status(foreign["job"])
        assert status.startswith("running (adopted"), status
        (shared / "release").touch()

        async def done():
            while True:
                status = await srv.hol_build_status(foreign["job"])
                if status.startswith("done"):
                    return status
                await asyncio.sleep(.02)
        status = await asyncio.wait_for(done(), 10)
        assert "Build succeeded" in status and "adopted" in status, status
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert "Build succeeded" in result, result
        assert (peer / "result").read_text() == "complete"
    finally:
        (shared / "release").touch()
        try:
            os.killpg(foreign["pid"], signal.SIGTERM)
        except ProcessLookupError:
            pass


async def test_adopted_job_can_be_cancelled_and_its_output_stays_suspect(tmp_path):
    shared, peer, output = _shared_fixture(tmp_path)
    foreign = await _exiting_controller(shared, "ready")
    try:
        status = await srv.hol_build_status(foreign["job"], cancel=True)
        assert status.startswith("cancelled (adopted"), status
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert result.startswith("ERROR:") and "partial" in result.lower(), result
        assert foreign["job"] in result and str(output) in result, result
        output.unlink()
        (shared / "release").touch()
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert "Build succeeded" in result, result
        assert (peer / "result").read_text() == "complete"
    finally:
        (shared / "release").touch()
        try:
            os.killpg(foreign["pid"], signal.SIGTERM)
        except ProcessLookupError:
            pass


async def test_separate_servers_share_read_only_dependencies_in_parallel(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    (shared / "ready").write_text("complete")
    (shared / "Holmakefile").write_text("ready:\n\tfalse\n")
    python = shlex.quote(sys.executable)
    roots = [tmp_path / "a", tmp_path / "b"]
    for root in roots:
        root.mkdir()
        (root / "worker.py").write_text(
            "from pathlib import Path\nimport time\nPath('started').touch()\n"
            "while not Path('release').exists(): time.sleep(.01)\n"
            "assert Path('../shared/ready').read_text() == 'complete'\nPath('result').touch()\n")
        (root / "Holmakefile").write_text(
            f"INCLUDES = ../shared\nresult: ../shared/ready\n\t{python} worker.py\n")
    result = await srv.holmake(str(roots[0]), target="result", detach=True)
    job = re.search(r"job=(\S+)", result).group(1)
    foreign = None
    try:
        await _started(roots[0])
        foreign = await _exiting_controller(roots[1], "result")
        assert "running" in await srv.hol_build_status(job)
        assert not any((root / "result").exists() for root in roots)
        for root in roots:
            (root / "release").touch()
        async def completed():
            while not all((root / "result").exists() for root in roots):
                await asyncio.sleep(.01)
        await asyncio.wait_for(completed(), 10)
    finally:
        for root in roots:
            (root / "release").touch()
        await srv.hol_build_status(job, cancel=True)
        if foreign:
            try:
                os.killpg(foreign["pid"], signal.SIGTERM)
            except ProcessLookupError:
                pass
