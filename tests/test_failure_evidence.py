"""Complete failure evidence is retained without success-path disk traffic."""
import asyncio
import json
from types import SimpleNamespace
from unittest.mock import AsyncMock

import pytest

from hol4_mcp.hol_session import HOLSession
from hol4_mcp.hol_mcp_server import _failure_evidence_lines


def test_success_does_not_create_logs_or_change_reply(tmp_path, monkeypatch):
    def unexpected(**kwargs):
        raise AssertionError("success path must not create a log directory")

    monkeypatch.setattr("hol4_mcp.failure_evidence.tempfile.mkdtemp", unexpected)
    session = HOLSession(str(tmp_path))
    output = '{"goal":"Rtype_error", "error":null}\n' * 4000
    assert session._note_diagnostics("goals_json();", output) is output
    assert session.failure_evidence.directory is None
    assert session.failure_evidence.latest is None


def test_full_multiline_response_and_request_retained(tmp_path):
    session = HOLSession(str(tmp_path))
    session.request_context = {"phase": "top-level SML/translation", "start_line": 4}
    command = 'val x = "large source";\n' * 4000
    output = "OK..\n" * 4000 + "Exception-\n HOL_ERR\n  detailed payload\n raised\n"
    assert session._note_diagnostics(command, output) is output
    evidence = session.failure_evidence.latest
    with open(evidence["path"]) as stream:
        record = json.load(stream)
    assert record["command"] == command and record["response"] == output
    assert record["context"]["phase"] == "top-level SML/translation"
    assert session.failure_evidence.directory.stat().st_mode & 0o777 == 0o700
    assert evidence["path"] in "".join(_failure_evidence_lines(session))


def test_log_write_failure_does_not_change_hol_error(tmp_path, monkeypatch):
    def unavailable(**kwargs):
        raise OSError("disk unavailable")

    monkeypatch.setattr("hol4_mcp.failure_evidence.tempfile.mkdtemp", unavailable)
    session = HOLSession(str(tmp_path))
    output = 'Exception- Fail "original HOL failure" raised'
    assert session._note_diagnostics("command", output) is output
    assert "disk unavailable" in "".join(_failure_evidence_lines(session))


async def test_cancelled_request_saves_partial_response(tmp_path, monkeypatch):
    session = HOLSession(str(tmp_path))
    session.process = SimpleNamespace(pid=123, returncode=None)
    monkeypatch.setattr(session, "_drain_pipe", AsyncMock())
    monkeypatch.setattr(session, "_write_command", AsyncMock())

    async def pending(timeout):
        session._buffer = b"partial response before cancellation"
        await asyncio.Event().wait()

    monkeypatch.setattr(session, "_read_response", pending)
    with pytest.raises(asyncio.TimeoutError):
        await asyncio.wait_for(session.send("val slow = 1;"), .01)
    evidence = session.failure_evidence.latest
    with open(evidence["path"]) as stream:
        record = json.load(stream)
    assert record["kind"] == "cancelled"
    assert "partial response" in record["response"]
    assert record["command"] == "val slow = 1;"


async def test_live_hol_failure_evidence(tmp_path):
    async with HOLSession(str(tmp_path)) as session:
        output = await session.send('raise Fail "evidence integration";', timeout=5)
        evidence = session.failure_evidence.latest
        assert evidence and evidence["kind"] == "HOL error"
        with open(evidence["path"]) as stream:
            record = json.load(stream)
        assert record["response"] == output
        assert "evidence integration" in output
        assert "42" in await session.send("40 + 2;", timeout=5)


async def test_compiler_specific_is_registered_as_baked_in(tmp_path):
    async with HOLSession(str(tmp_path)) as session:
        output = await session.send('load "CompilerSpecific";', timeout=5)
        assert "Cannot find file CompilerSpecific.ui" not in output
        assert session.failure_evidence.latest is None


def test_evidence_is_capped_and_discarded_at_exit(monkeypatch):
    from hol4_mcp import failure_evidence as module

    monkeypatch.setattr(module, "_directories", [])
    monkeypatch.delenv("HOL4_MCP_KEEP_EVIDENCE", raising=False)
    evidence = module.FailureEvidence()
    for n in range(module.KEEP + 5):
        evidence.record(f"cmd {n}", "Exception- raised", "HOL error")
    names = sorted(p.name for p in evidence.directory.iterdir())
    assert len(names) == module.KEEP
    assert f"failure-{module.KEEP + 5}.json" in names and "failure-1.json" not in names
    assert evidence.latest["path"].endswith(f"failure-{module.KEEP + 5}.json")
    directory = evidence.directory
    monkeypatch.setenv("HOL4_MCP_KEEP_EVIDENCE", "1")
    module._discard_all()
    assert directory.exists()
    monkeypatch.delenv("HOL4_MCP_KEEP_EVIDENCE")
    module._discard_all()
    assert not directory.exists()
