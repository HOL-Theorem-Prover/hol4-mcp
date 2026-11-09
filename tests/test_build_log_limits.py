"""Small log excerpts must bound disk reads, including multibyte text."""
from pathlib import Path
import shlex
import sys
import time
from types import SimpleNamespace

import pytest

from hol4_mcp import hol_mcp_server as srv


def _watch_reads(monkeypatch, path, budget):
    original = Path.open
    requests = []

    class Watched:
        def __init__(self, stream):
            self.stream = stream

        def __enter__(self):
            return self

        def __exit__(self, *args):
            return self.stream.__exit__(*args)

        def __getattr__(self, name):
            return getattr(self.stream, name)

        def read(self, size=-1):
            requests.append(size)
            if budget is not None:
                assert 0 <= size <= budget, f"unbounded/oversized log read: {size}"
            return self.stream.read(size)

    def watched(candidate, *args, **kwargs):
        stream = original(candidate, *args, **kwargs)
        return Watched(stream) if candidate == path else stream

    monkeypatch.setattr(Path, "open", watched)
    return requests


@pytest.mark.parametrize("limit", [4, 3, 0])
async def test_hol_log_reads_byte_tail_or_explicit_unlimited(tmp_path, monkeypatch, limit):
    path = tmp_path / ".hol/logs/exampleTheory"
    path.parent.mkdir(parents=True)
    data = b"x" * (1024 * 1024) + "αβγ".encode()
    path.write_bytes(data)
    requests = _watch_reads(monkeypatch, path, limit or None)
    result = await srv.hol_log(str(tmp_path), "example", limit=limit)
    if limit:
        assert f"last {limit} bytes" in result
        assert result.split("\n", 1)[1] == data[-limit:].decode(errors="replace")
        assert sum(requests) <= limit
    else:
        assert result == data.decode()
        assert requests == [-1]


@pytest.mark.parametrize("tail", [4, 0])
async def test_build_status_reads_only_requested_bytes(tmp_path, monkeypatch, tail):
    path = tmp_path / "build.log"
    path.write_bytes(b"x" * (1024 * 1024) + "αβγ".encode())
    entry = srv._BuildJob(proc=SimpleNamespace(returncode=0), workdir=tmp_path,
                          target="result", log=path, started=time.time(),
                          finished=time.time())
    entry.done.set()
    monkeypatch.setitem(srv._build_jobs, "log-limit", entry)
    requests = _watch_reads(monkeypatch, path, tail)
    result = await srv.hol_build_status("log-limit", tail=tail)
    assert "Build succeeded" in result
    if tail:
        assert result.endswith("βγ")
        assert sum(requests) <= tail
    else:
        assert requests == []


@pytest.mark.parametrize("limit", [4, 0])
async def test_failed_build_log_uses_same_byte_limit(tmp_path, monkeypatch, limit):
    path = tmp_path / ".hol/logs/exampleTheory"
    python = shlex.quote(sys.executable)
    (tmp_path / "worker.py").write_text(
        "from pathlib import Path\n"
        "p = Path('.hol/logs/exampleTheory'); p.parent.mkdir(parents=True,exist_ok=True)\n"
        "p.write_text('x' * (1024 * 1024) + 'αβγ')\nraise RuntimeError('failed recipe')\n")
    (tmp_path / "Holmakefile").write_text(f"result:\n\t{python} worker.py\n")
    requests = _watch_reads(monkeypatch, path, limit or None)
    result = await srv.holmake(str(tmp_path), "result", log_limit=limit)
    assert "Build failed" in result and "=== Build Logs ===" in result, result
    if limit:
        assert f"last {limit} bytes" in result and "\nβγ\n" in result
        assert sum(requests) <= limit
    else:
        assert "truncated" not in result and "αβγ" in result
        assert requests == [-1]
