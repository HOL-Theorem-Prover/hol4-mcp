"""`holmake` and Poly/ML's out-of-store failure: every build passes
Holmake's own --retry-oos=1, and a sequential build (jobs=1) that runs out of
store is re-run once by the server, synchronous or detached. A stand-in
Holmake hands dependency discovery to the real one and fails a build run with
the out-of-store message the given number of times."""
import asyncio
import re
import stat

import pytest

from hol4_mcp import hol_mcp_server as srv
from hol4_mcp.hol_session import HOLDIR

SCRIPT = ('open HolKernel Parse boolLib bossLib;\n'
          'val _ = new_theory "aa";\nval _ = export_theory();\n')


@pytest.fixture
def flaky_holmake(tmp_path, monkeypatch):
    """Returns ``(workdir, runs)``; ``runs()`` lists each build run's args."""
    def make(failures):
        holdir = tmp_path / "fakeHOL"
        (holdir / "bin").mkdir(parents=True)
        fake = holdir / "bin" / "Holmake"
        fake.write_text(
            "#!/bin/sh\n"
            f'case " $* " in *" --json "*) exec "{HOLDIR}/bin/Holmake" "$@";; esac\n'
            f'echo "$*" >> "{tmp_path}/runs"\n'
            f'if [ "$(wc -l < "{tmp_path}/runs")" -le {failures} ]; then\n'
            '  echo "Run out of store - interrupting threads"; exit 1\nfi\n'
            f'exec "{HOLDIR}/bin/Holmake" "$@"\n')
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
        monkeypatch.setattr(srv, "HOLDIR", holdir)
        work = tmp_path / "work"
        work.mkdir()
        (work / "aaScript.sml").write_text(SCRIPT)

        def runs():
            path = tmp_path / "runs"
            return path.read_text().splitlines() if path.exists() else []
        return work, runs
    return make


async def test_sequential_build_is_rerun_once_after_running_out_of_store(flaky_holmake):
    work, runs = flaky_holmake(failures=1)
    result = await srv.holmake(str(work), target="aaTheory", jobs=1, timeout=120)
    assert result.startswith("Build succeeded"), result
    assert "re-run once after Poly/ML ran out of store" in result.splitlines()[0], result
    assert len(runs()) == 2 and all("--retry-oos=1" in r for r in runs()), runs()


async def test_second_out_of_store_failure_is_reported_as_is(flaky_holmake):
    work, runs = flaky_holmake(failures=2)
    result = await srv.holmake(str(work), target="aaTheory", jobs=1, timeout=120)
    assert not result.startswith("Build succeeded"), result
    assert "Run out of store" in result and len(runs()) == 2, (result, runs())


async def test_parallel_build_leaves_the_retry_to_holmake(flaky_holmake):
    work, runs = flaky_holmake(failures=1)
    result = await srv.holmake(str(work), target="aaTheory", jobs=2, timeout=120)
    assert not result.startswith("Build succeeded"), result
    assert len(runs()) == 1 and "--retry-oos=1" in runs()[0], runs()


async def test_detached_sequential_build_is_rerun_once(flaky_holmake):
    work, runs = flaky_holmake(failures=1)
    started = await srv.holmake(str(work), target="aaTheory", jobs=1, detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        status = await srv.hol_build_status(job, wait=120)
        assert status.startswith("done") and "Build succeeded" in status, status
        assert "re-run once after Poly/ML ran out of store" in status, status
        assert len(runs()) == 2, runs()
    finally:
        await srv.hol_build_status(job, cancel=True)


def test_summary_reports_holmakes_own_retries():
    output = "1 job(s) were re-run after Poly/ML reported running out of store\n"
    assert "1 job(s) re-run after Poly/ML ran out of store" in srv._build_summary(output)
