"""A build whose MCP server died leaves `running` records behind. A later
server adopts the build from its job record when its exit status is known,
names it as lost when nothing can tell, and retires a lost build's records on
request."""
import asyncio
import fcntl
import os
import shlex
import sys

import pytest

from hol4_mcp import build_coordination as coordination
from hol4_mcp import hol_mcp_server as srv
from hol4_mcp.build_coordination import _RecordOwner


def _shared_project(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    python = shlex.quote(sys.executable)
    (shared / "writer.py").write_text(
        "from pathlib import Path\nimport time\n"
        "Path('ready').write_text('partial')\nPath('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "Path('ready').write_text('complete')\n")
    (shared / "Holmakefile").write_text(f"ready:\n\t{python} writer.py\n")
    peer = tmp_path / "peer"
    peer.mkdir()
    (peer / "Holmakefile").write_text(
        "INCLUDES = ../shared\nresult: ../shared/ready\n\t" + python +
        " -c \"from pathlib import Path; "
        "Path('result').write_text(Path('../shared/ready').read_text())\"\n")
    return shared, peer


async def _wait_for(predicate, timeout):
    async def poll():
        while not predicate():
            await asyncio.sleep(.05)
    await asyncio.wait_for(poll(), timeout)


async def test_a_synchronous_build_whose_server_died_is_adopted(tmp_path):
    shared, peer = _shared_project(tmp_path)
    server = (
        "import asyncio, sys\n"
        "from hol4_mcp import hol_mcp_server as srv\n"
        f"asyncio.run(srv.holmake({str(shared)!r}, target='ready', timeout=60))\n")
    child = await asyncio.create_subprocess_exec(sys.executable, "-c", server)
    try:
        await _wait_for(lambda: (shared / "started").exists(), 30)
    finally:
        child.kill()
        await child.wait()
    (shared / "release").touch()
    await _wait_for(lambda: (shared / "ready").read_text() == "complete", 10)
    await asyncio.sleep(2)
    result = await srv.holmake(str(peer), target="result", timeout=30)
    assert "Build succeeded" in result, result
    assert (peer / "result").read_text() == "complete"


def _lost_record(tmp_path, token="bbbbbbbbbbbb"):
    """A running record whose build left no job record, for a file that
    exists although it did not when the build started."""
    artifact = tmp_path / "lost" / ".hol" / "objs" / "gone.ui"
    artifact.parent.mkdir(parents=True)
    owner = _RecordOwner(token, f"build={token} workdir={artifact.parent}")
    coordination._write_state(artifact, "running", None, owner)
    artifact.write_text("rebuilt outside the MCP")
    return artifact, token


def test_the_refusal_names_a_lost_build_and_how_to_retire_it(tmp_path):
    artifact, token = _lost_record(tmp_path)
    record = coordination._suspect(artifact)
    assert record is not None and record["token"] == token
    text = coordination._suspect_refusal([(artifact, record)])
    assert "lost" in text and token in text, text
    assert f'hol_build_status(job="{token}", retire=True)' in text, text


def test_a_build_holding_its_lock_is_neither_lost_nor_retired(tmp_path):
    artifact, token = _lost_record(tmp_path)
    fd = coordination._open_lock(coordination._unit_lock(coordination.artifact_unit(artifact)))
    fcntl.flock(fd, fcntl.LOCK_EX)
    try:
        assert coordination.lost_build(token, [artifact]) is None
        with pytest.raises(ValueError):
            coordination.retire_build(token)
        assert coordination._suspect(artifact) is not None
    finally:
        os.close(fd)


async def test_retiring_a_lost_build_moves_its_records_aside(tmp_path):
    artifact, token = _lost_record(tmp_path)
    reply = await srv.hol_build_status(token, retire=True)
    assert "retired" in reply, reply
    assert coordination._suspect(artifact) is None
    backups = list(coordination.storage_root().glob(f"retired/{token}-*"))
    assert backups and any(backups[0].rglob("*.running.json")), reply
