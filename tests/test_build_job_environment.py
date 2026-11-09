"""Parallelism must follow the environment actually passed to Holmake."""
import asyncio

import pytest

from hol4_mcp import hol_mcp_server as srv


@pytest.mark.parametrize("inherited,supplied,explicit,expected", [
    ("2", "3", None, 3),
    ("2", "3", 4, 4),
    ("3", None, None, 3),
    ("invalid", "2", None, 2),
    ("invalid", "invalid", 2, 2),
    (None, None, 1, 1),
    (None, None, None, None),
])
async def test_job_setting_precedence_in_real_build(tmp_path, monkeypatch, inherited, supplied, explicit, expected):
    if inherited is None:
        monkeypatch.delenv("HOL4_MCP_HOLMAKE_JOBS", raising=False)
    else:
        monkeypatch.setenv("HOL4_MCP_HOLMAKE_JOBS", inherited)
    (tmp_path / "Holmakefile").write_text("result:\n\ttouch result\n")
    original = asyncio.create_subprocess_exec
    launches = []

    async def capture(*args, **kwargs):
        if "--no_preexecs" in args:
            launches.append((args, kwargs["env"]))
        return await original(*args, **kwargs)

    monkeypatch.setattr(asyncio, "create_subprocess_exec", capture)
    env = {"HOL4_MCP_HOLMAKE_JOBS": supplied} if supplied is not None else None
    result = await srv.holmake(str(tmp_path), "result", env=env, jobs=explicit)
    assert "Build succeeded" in result, result
    assert (tmp_path / "result").exists()
    command, environment = launches[0]
    if expected is None:
        assert "-j" not in command, command   # unset: Holmake's own default
    else:
        assert "-j" in command, command       # jobs=1 must cap Holmake's own default
        assert int(command[command.index("-j") + 1]) == expected, command
    assert environment.get("HOL4_MCP_HOLMAKE_JOBS") == (supplied or inherited)


@pytest.mark.parametrize("supplied", [False, True])
async def test_invalid_job_environment_is_actionable_and_does_not_spawn(tmp_path, monkeypatch, supplied):
    monkeypatch.setenv("HOL4_MCP_HOLMAKE_JOBS", "1" if supplied else "not-a-number")
    (tmp_path / "Holmakefile").write_text("result:\n\ttouch result\n")

    async def unexpected(*args, **kwargs):
        pytest.fail("invalid configuration must be rejected before spawning")

    monkeypatch.setattr(asyncio, "create_subprocess_exec", unexpected)
    env = {"HOL4_MCP_HOLMAKE_JOBS": "not-a-number"} if supplied else None
    result = await srv.holmake(str(tmp_path), "result", env=env)
    assert result.startswith("ERROR:") and "HOL4_MCP_HOLMAKE_JOBS" in result, result
    assert not (tmp_path / "result").exists()
