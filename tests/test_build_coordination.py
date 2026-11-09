"""Exercise shared build behavior with the installed Holmake, not a mock lock."""
import asyncio
import json
import os
from pathlib import Path
import re
import shlex
import sys
import time

import pytest

from hol4_mcp import hol_mcp_server as srv
from hol4_mcp import build_coordination as coordination
from hol4_mcp.build_coordination import (
    BuildClaim, artifact_unit, completed_outputs, job_tag, job_verdicts,
)


MONITOR_OUTPUT = """\
Scanning $(HOLDIR)/src/boss
Scanned 2 directories
Building 3 theory files
Starting work on aTheory
Starting work on bTheory
aTheory                                                  (3s)   [1/3]OK
bTheory                  ../other                       (12s)   [2/3]CHEATED
Starting work on cTheory
cTheory                                                  (1s)   RETRY
Starting work on cTheory
Starting work on dTheory
dTheory                                                  (0s)   FAIL<1>
Starting work on result
result                                                   (0s)   OK
"""


def test_completed_outputs_follows_the_monitor_verdicts():
    tags = {t: {Path(f"/w/{t}.dat")}
            for t in ("aTheory", "bTheory", "cTheory", "dTheory", "eTheory", "result")}
    compiled = {Path("/w/aTheory.uo")}
    done = completed_outputs(tags, compiled, MONITOR_OUTPUT, 1)
    assert done == {Path("/w/aTheory.dat"), Path("/w/bTheory.dat"),
                    Path("/w/result.dat"), Path("/w/aTheory.uo")}
    # A signal exit certifies verdict lines only, never the in-process compiles.
    for signalled in (-15, 143):
        done = completed_outputs(tags, compiled, MONITOR_OUTPUT, signalled)
        assert Path("/w/aTheory.dat") in done and Path("/w/aTheory.uo") not in done
    assert completed_outputs(tags, compiled, "", None) == set()


PADDED_MONITOR_OUTPUT = """\
Starting work on word_elimTheory
word_elimTheory              $(CAKEMLDIR)/compiler/backend  (8s)  [1/94]     OK
Starting work on clos_to_bvlProofTheory
clos_to_bvlProofTheory     $(CAKEMLDIR)/.../backend/proofs(320s) [45/94]     OK
Starting work on npbc_mo_fullProofTheory
npbc_mo_fullProofTheory          $(pseudo_bool)/.../proofs (53s)        FAIL<1>
"""


def test_completed_outputs_reads_padded_and_abutting_columns():
    tags = {t: {Path(f"/w/{t}.dat")}
            for t in ("word_elimTheory", "clos_to_bvlProofTheory",
                      "npbc_mo_fullProofTheory")}
    done = completed_outputs(tags, set(), PADDED_MONITOR_OUTPUT, 1)
    assert done == {Path("/w/word_elimTheory.dat"),
                    Path("/w/clos_to_bvlProofTheory.dat")}


def test_completed_outputs_reads_sequential_progress_lines():
    output = """\
/bin/cp /w/export/cake-sexpr-x64-64 cake-sexpr-64
Holmake: Linking /w/to_word32ProgScript.uo to produce theory-builder executable
Exporting theory "to_word32Prog" ... done.
Theory "to_word32Prog" took 12m47s to build
Holmake: [2/8] to_word32Prog
Holmake: [↓3] bigProg
Holmake: Linking /w/from_pancake32ProgScript.uo to produce theory-builder executable
Holmake: Failed script build for /w/from_pancake32ProgScript - exited with code 1
"""
    tags = {t: {Path(f"/w/{t}.dat")}
            for t in ("to_word32ProgTheory", "bigProgTheory",
                      "from_pancake32ProgTheory", "cake-sexpr-64")}
    assert completed_outputs(tags, set(), output, 1) == {
        Path("/w/to_word32ProgTheory.dat"), Path("/w/bigProgTheory.dat")}


SEQUENTIAL_CANCELLED_IN_SCRIPT = """\
Holmake: Building 3 theory files
Holmake: Linking /w/aaScript.uo to produce theory-builder executable
Exporting theory "aa" ... done.
Holmake: [1/3] aa
Holmake: Linking /w/bbScript.uo to produce theory-builder executable
<<HOL message: Created theory "bb">>
"""


def test_signalled_sequential_build_in_a_script_certifies_in_process_compiles():
    compiled = {Path("/w/.hol/objs/aaTheory.ui"), Path("/w/.hol/objs/aaTheory.uo")}
    tags = {"aaTheory": {Path("/w/aaTheory.dat")}, "bbTheory": {Path("/w/bbTheory.dat")}}
    for returncode in (-15, None):
        done = completed_outputs(tags, compiled, SEQUENTIAL_CANCELLED_IN_SCRIPT, returncode)
        assert done == compiled | {Path("/w/aaTheory.dat")}, (returncode, done)
    # Stopped after a progress line, a compile may have been mid-write.
    between = SEQUENTIAL_CANCELLED_IN_SCRIPT.rsplit("Holmake: Linking", 1)[0]
    assert completed_outputs(tags, compiled, between, -15) == {Path("/w/aaTheory.dat")}
    # A monitored build runs nodes in parallel: the rule does not apply.
    monitored = "Starting work on aaTheory\n" + SEQUENTIAL_CANCELLED_IN_SCRIPT
    assert not compiled & completed_outputs(tags, compiled, monitored, -15)


def _two_theory_graph(workdir):
    """`Holmake --json --dirs .` for aScript.sml and bScript.sml, b an
    ancestor-child of a, with the HOL nodes reduced to one."""
    def node(i, name, command, deps):
        return {"node_id": i, "target": str(workdir / name), "command": command,
                "needs_rebuild": bool(command), "dependencies": deps}
    build_a, build_b = f"BIC_Build {workdir}/aScript", f"BIC_Build {workdir}/bScript"
    return json.dumps([
        node(0, "aScript.sml", "", []), node(1, "hol.state", "", []),
        node(2, "aTheory.sml", build_a, [1, 0]), node(3, "aTheory.dat", build_a, [1, 0]),
        node(4, "aTheory.sig", build_a, [1, 0]),
        node(5, "aTheory.ui", "BIC_Compile", [1, 4]),
        node(6, "aTheory.uo", "BIC_Compile", [5, 3, 1, 2]),
        node(7, "bScript.sml", "", []),
        node(8, "bTheory.sml", build_b, [6, 1, 7]), node(9, "bTheory.dat", build_b, [6, 1, 7]),
        node(10, "bTheory.sig", build_b, [6, 1, 7]),
        node(11, "bTheory.ui", "BIC_Compile", [1, 10]),
        node(12, "bTheory.uo", "BIC_Compile", [11, 9, 1, 8]),
    ])


def test_signalled_monitored_build_certifies_compiles_a_started_job_needed(tmp_path):
    """Holmake starts a job only once its dependencies are built, so a killed
    parallel build has finished every in-process compile a started job needs."""
    claim = coordination.claim_from_graph(_two_theory_graph(tmp_path), tmp_path, "bTheory")
    a_compiled = {path for name in ("aTheory.ui", "aTheory.uo")
                  for path in coordination._artifact_paths(tmp_path / name)}
    b_compiled = claim.in_process - a_compiled
    assert a_compiled < claim.in_process and len(b_compiled) == 4
    assert {path: claim.witnesses[path] for path in a_compiled} == {
        path: {"bTheory"} for path in a_compiled}
    assert not b_compiled & claim.witnesses.keys()

    log = ("Starting work on aTheory\naTheory   (3s)   [1/2]     OK\n"
           "Starting work on bTheory\n")
    for path in claim.outputs:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("written by the build")
    claim.before = {path: None for path in claim.outputs}
    record = coordination.job_record(claim, pid=os.getpid(), target="bTheory",
                                     log=tmp_path / "log", exit_file=tmp_path / "exit",
                                     trace_note="", started=time.time())
    record = json.loads(json.dumps(record))
    job_file = coordination.jobs_directory() / f"{record['token']}.json"
    try:
        coordination.finalize_job(record, -15, log)
        assert all(coordination._suspect(path, adopt=False) is None
                   for path in a_compiled | claim.tags["aTheory"])
        assert all(coordination._suspect(path, adopt=False) is not None
                   for path in b_compiled | claim.tags["bTheory"])
    finally:
        job_file.unlink(missing_ok=True)
        for path in claim.outputs:
            coordination._unlink_state(path, "failed")


@pytest.mark.parametrize("returncode", [None, -15, 0])
def test_finalize_job_certifies_what_the_log_says_finished(tmp_path, returncode):
    """A detached job finalized by a later server (no exit status: None), a
    cancelled one (-15) and a successful one all trust the log's progress lines."""
    objs = tmp_path / ".hol" / "objs"
    objs.mkdir(parents=True)
    finished, running = objs / "word_elimTheory.ui", objs / "data_spaceProofTheory.ui"
    for path in (finished, running):
        path.write_text("written by the build")
    record = {
        "token": f"{time.time_ns() & (16**12 - 1):012x}", "label": "test job",
        "outputs": [str(finished), str(running)],
        "before": {str(finished): None, str(running): None},
        "tags": {"word_elimTheory": [str(finished)],
                 "data_spaceProofTheory": [str(running)]},
        "in_process": [], "commands": {},
    }
    job_file = coordination.jobs_directory() / f"{record['token']}.json"
    try:
        coordination.finalize_job(record, returncode, "Holmake: [↓99] word_elim\n")
        assert coordination._suspect(finished, adopt=False) is None
        flagged = coordination._suspect(running, adopt=False)
        assert (flagged is None) == (returncode == 0), flagged
        if flagged is not None:
            assert flagged.get("returncode") == returncode, flagged
    finally:
        job_file.unlink(missing_ok=True)
        for path in (finished, running):
            coordination._unlink_state(path, "failed")


def test_suspect_refusal_lists_suspects_and_who_may_remove_them(tmp_path, monkeypatch):
    holdir = tmp_path / "HOL"
    monkeypatch.setattr(coordination, "HOLDIR", holdir)
    files = {name: holdir / "step" / ".hol" / "objs" / name
             for name in ("left.ui", "orphan.ui", "touched.ui")}
    outside = tmp_path / "proj" / "mine.ui"
    for path in [*files.values(), outside]:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("partial")

    def record(path, **extra):
        return {"path": str(path), "stamp": list(coordination._stamp(path)),
                "label": f"job=aaaaaaaaaaaa ({path.name})", "token": "aaaaaaaaaaaa", **extra}

    suspects = [(files["left.ui"], record(files["left.ui"], returncode=-15)),
                (files["orphan.ui"], record(files["orphan.ui"])),
                (files["touched.ui"], record(files["touched.ui"], returncode=1)),
                (outside, record(outside, returncode=1))]
    files["touched.ui"].write_text("changed since")
    text = coordination._suspect_refusal(suspects)
    for path, _ in suspects:
        assert f"possibly partial or unverified artifact: {path}" in text, text
    assert "no build is accepted while these exist" in text, text
    assert f"{files['left.ui']} is under $HOLDIR. It may be removed" in text, text
    for name in ("orphan.ui", "touched.ui"):
        assert f"{files[name]} is under $HOLDIR and is not provably" in text, text
    assert f"{outside} is under $HOLDIR" not in text, text


SEQUENTIAL_SHELL_OUTPUT = """\
touch first
quiet-recipe
Holmake: Linking /w/fooScript.uo to produce theory-builder executable
Exporting theory "foo" ... done.
Holmake: [1/2] foo
cp second third && false
cp: cannot stat 'second': No such file or directory
"""


def test_sequential_shell_targets_complete_once_a_later_target_began():
    commands = {"first": "touch first", "second": None, "third": "cp second third && false",
                "fourth": "touch fourth"}
    state = job_verdicts(SEQUENTIAL_SHELL_OUTPUT, commands)
    assert state["first"] == "OK" and state["fooTheory"] == "OK"
    assert "second" not in state     # a quiet recipe shows nothing to certify
    assert "third" not in state      # the last target to begin is the failure
    assert "fourth" not in state
    tags = {t: {Path(f"/w/{t}")} for t in commands} | {"fooTheory": {Path("/w/fooTheory.dat")}}
    done = completed_outputs(tags, set(), SEQUENTIAL_SHELL_OUTPUT, 1, commands)
    assert done == {Path("/w/first"), Path("/w/fooTheory.dat")}
    # With a monitor present the echo rule does not apply.
    assert "first" not in job_verdicts("Starting work on x\n" + SEQUENTIAL_SHELL_OUTPUT, commands)


def test_artifact_unit_groups_a_theory_with_its_object_files(tmp_path):
    objs = tmp_path / ".hol" / "objs"
    assert artifact_unit(tmp_path / "fooTheory.dat") == (tmp_path, "fooTheory")
    assert artifact_unit(objs / "fooTheory.uo") == (tmp_path, "fooTheory")
    assert artifact_unit(objs / "fooTheory.ui") == artifact_unit(tmp_path / "fooTheory.sig")
    assert artifact_unit(tmp_path / "barTheory.dat") != artifact_unit(tmp_path / "fooTheory.dat")
    assert artifact_unit(tmp_path / "cake-sexpr-64") == (tmp_path, "cake-sexpr-64")


def test_theory_builder_reads_files_under_a_closure_past_fd_setsize(tmp_path, monkeypatch):
    # A theory builder inherits every lock of its claim. Poly/ML select()s the
    # streams it reads, and glibc aborts that on a descriptor >= FD_SETSIZE,
    # so the inherited locks must leave the builder low descriptor numbers.
    import subprocess
    locks = tmp_path / "locks"
    locks.mkdir()
    monkeypatch.setattr(coordination, "_lock_storage", lambda: locks)
    script = tmp_path / "probe.sml"
    script.write_text('val _ = print "builder read its script\\n";\n')
    claims = coordination.BuildClaims()
    claim = BuildClaim(tmp_path, {tmp_path / f"unit{index}" for index in range(1100)}, set())
    try:
        assert claims.register(claim) is None
        child = subprocess.run(
            [str(srv.HOLDIR / "bin" / "hol"), "--gcthreads=1", "run", str(script)],
            pass_fds=claim.lock_fds, capture_output=True, text=True, timeout=120)
    finally:
        claims.finish(claim)
    assert child.returncode == 0, child.stdout + child.stderr
    assert "builder read its script" in child.stdout


def test_stale_in_memory_claim_is_reaped_by_the_next_registration(tmp_path):
    from types import SimpleNamespace
    claims = coordination.BuildClaims()
    stuck = BuildClaim(tmp_path, set(), set())
    stuck.proc = SimpleNamespace(returncode=1)       # exited; nothing ever finished it
    claims.active[stuck.token] = stuck
    never_spawned = BuildClaim(tmp_path, set(), set())
    never_spawned.created -= 600
    claims.active[never_spawned.token] = never_spawned
    fresh = BuildClaim(tmp_path, set(), set())
    try:
        assert claims.register(fresh) is None
        assert set(claims.active) == {fresh.token}
    finally:
        claims.finish(fresh)


def test_legacy_in_project_records_are_still_read_and_cleared(tmp_path):
    artifact = tmp_path / "ready"
    artifact.write_text("partial")
    legacy = coordination._legacy_state_file(artifact, "failed")
    legacy.parent.mkdir(parents=True)
    legacy.write_text(json.dumps({"path": str(artifact), "label": "job=oldone workdir=x",
                                  "token": "0123456789ab",
                                  "stamp": list(coordination._stamp(artifact))}))
    assert coordination._suspect(artifact)["token"] == "0123456789ab"
    coordination._unlink_state(artifact, "failed")
    assert not legacy.exists() and coordination._suspect(artifact) is None


def test_discovery_output_is_condensed_and_the_result_summarised():
    text = "Scanning a\nScanning b\nExecuting x/.hol_preexec:\nScanning c\n"
    assert srv._condense_discovery(text) == "Scanned 3 directories\nExecuting x/.hol_preexec:\n"
    text = "Scanning a\nScanned 1 directories\nBuilding 1 theory file\n"
    assert srv._condense_discovery(text) == "Scanned 1 directories\nBuilding 1 theory file\n"
    assert srv._build_summary(MONITOR_OUTPUT) == (
        " built 3: aTheory, bTheory, result; failed 1: dTheory.")
    assert srv._build_summary("nothing to do\n") == ""


async def test_independent_targets_in_one_directory_build_concurrently(tmp_path):
    python = shlex.quote(sys.executable)
    (tmp_path / "worker.py").write_text(
        "from pathlib import Path\nimport time\n"
        "Path('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "Path('slow').write_text('ok')\n")
    (tmp_path / "Holmakefile").write_text(
        f"slow:\n\t{python} worker.py\n\nfast:\n\ttouch fast\n")
    started = await srv.holmake(str(tmp_path), target="slow", detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        async def ready():
            while not (tmp_path / "started").exists():
                await asyncio.sleep(.01)
        await asyncio.wait_for(ready(), 10)
        # Nothing the two targets touch is shared: no refusal.
        result = await srv.holmake(str(tmp_path), target="fast", timeout=30)
        assert "Build succeeded" in result, result
        assert (tmp_path / "fast").exists() and not (tmp_path / "slow").exists()
        # The same unit is still exclusive while it is being written.
        result = await srv.holmake(str(tmp_path), target="slow", timeout=30)
        assert result.startswith("ERROR:") and "overlap" in result.lower(), result
        assert job in result and f"{tmp_path}/slow" in result, result
        (tmp_path / "release").touch()
        await _wait_for_job_finished(job)
        assert "Build succeeded" in await srv.hol_build_status(job)
    finally:
        (tmp_path / "release").touch()
        await srv.hol_build_status(job, cancel=True)


async def test_cancelled_sequential_build_keeps_the_theories_it_finished(tmp_path):
    header = "open HolKernel Parse boolLib bossLib;\n"
    (tmp_path / "aaScript.sml").write_text(
        header + 'val _ = new_theory "aa";\nval _ = export_theory();\n')
    (tmp_path / "bbScript.sml").write_text(
        header + 'open aaTheory;\nval _ = new_theory "bb";\nval _ = export_theory();\n')
    (tmp_path / "ccScript.sml").write_text(
        header + 'open bbTheory;\nval _ = new_theory "cc";\n'
        'val _ = TextIO.closeOut (TextIO.openOut "cc_started");\n'
        'val _ = while not (OS.FileSys.access ("release", [])) do\n'
        '          OS.Process.sleep (Time.fromMilliseconds 50);\n'
        'val _ = export_theory();\n')
    started = await srv.holmake(str(tmp_path), target="ccTheory", jobs=1, detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        async def ready():
            while not (tmp_path / "cc_started").exists():
                await asyncio.sleep(.05)
        await asyncio.wait_for(ready(), 120)
        status = await srv.hol_build_status(job, cancel=True)
        assert status.startswith("cancelled"), status
        result = await srv.holmake(str(tmp_path), target="bbTheory", jobs=1, timeout=120)
        assert "Build succeeded" in result and "partial" not in result.lower(), result
    finally:
        (tmp_path / "release").touch()
        await srv.hol_build_status(job, cancel=True)


async def test_project_mode_preflight_survives_a_starred_script_rule(tmp_path):
    (tmp_path / "holproject.toml").write_text('name = "starred"\n')
    project = tmp_path / "dir"
    project.mkdir()
    (project / "fooScript.sml").write_text(
        'open HolKernel Parse boolLib bossLib;\nval _ = new_theory "foo";\n'
        'val _ = export_theory();\n')
    (project / "Holmakefile").write_text(
        "INCLUDES = $(HOLDIR)/src/boss\n\ncake-x: *fooScript.sml\n\ttouch cake-x\n")
    result = await srv.holmake(str(project), target="fooTheory", timeout=120)
    assert "Build succeeded" in result, result
    assert "Scanning " not in result, result


async def test_build_status_waits_for_the_job_to_end(tmp_path):
    python = shlex.quote(sys.executable)
    (tmp_path / "worker.py").write_text(
        "from pathlib import Path\nimport time\n"
        "print('progress: step one', flush=True)\n"
        "Path('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "Path('result').write_text('ok')\n")
    (tmp_path / "Holmakefile").write_text(f"result:\n\t{python} worker.py\n")
    started = await srv.holmake(str(tmp_path), target="result", detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        async def ready():
            while not (tmp_path / "started").exists():
                await asyncio.sleep(.01)
        await asyncio.wait_for(ready(), 10)
        status = await srv.hol_build_status(job)
        assert status.startswith("running") and "[in progress: result" in status, status

        async def release_soon():
            await asyncio.sleep(.5)
            (tmp_path / "release").touch()
        releaser = asyncio.create_task(release_soon())
        t0 = time.monotonic()
        status = await srv.hol_build_status(job, wait=20)
        await releaser
        assert time.monotonic() - t0 < 15, "wait= must return as soon as the job ends"
        assert status.startswith("done") and "Build succeeded" in status, status
        assert "built 1: result" in status, status
    finally:
        (tmp_path / "release").touch()
        await srv.hol_build_status(job, cancel=True)


def test_job_tag_names_the_monitor_line():
    assert job_tag(Path("/w/fooTheory.dat"), "BIC_Build /w/foo") == "fooTheory"
    assert job_tag(Path("/w/fooTheory.sml"), "BIC_Build /w/foo") == "fooTheory"
    assert job_tag(Path("/w/fooTheory.uo"), "BIC_Compile") is None
    assert job_tag(Path("/w/result"), "touch result") == "result"
    assert job_tag(Path("/w/gen.sml"), "python gen.py") == "gen"


async def test_failed_build_keeps_the_prerequisite_its_monitor_reported_complete(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    python = shlex.quote(sys.executable)
    (shared / "Holmakefile").write_text(
        f"ready:\n\t{python} -c \"from pathlib import Path; Path('ready').write_text('complete')\"\n"
        f"broken: ready\n\t{python} -c \"from pathlib import Path; import sys; "
        "Path('broken').write_text('partial'); sys.exit(1)\"\n")
    result = await srv.holmake(str(shared), target="broken", timeout=30)
    assert "Build failed" in result, result
    assert (shared / "ready").read_text() == "complete"
    assert (shared / "broken").read_text() == "partial"

    def consumer(name, dependency):
        root = tmp_path / name
        root.mkdir()
        (root / "Holmakefile").write_text(
            f"INCLUDES = ../shared\nresult: ../shared/{dependency}\n\t{python} -c "
            f"\"from pathlib import Path; "
            f"Path('result').write_text(Path('../shared/{dependency}').read_text())\"\n")
        return root

    accepted = await srv.holmake(str(consumer("uses_ready", "ready")), target="result", timeout=30)
    assert "Build succeeded" in accepted, accepted
    refused = await srv.holmake(str(consumer("uses_broken", "broken")), target="result", timeout=30)
    assert refused.startswith("ERROR:") and "partial" in refused.lower(), refused


async def _wait_for_job_finished(job, timeout=10):
    async def finished():
        while srv._build_jobs[job].finished is None:
            await asyncio.sleep(.01)
    await asyncio.wait_for(finished(), timeout)


async def test_sibling_builds_do_not_consume_overlapping_writes(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    worker = shared / "writer.py"
    worker.write_text(
        "from pathlib import Path\nimport time\n"
        "guard = Path('writer-active')\n"
        "guard.mkdir()  # overlapping writers fail this test\n"
        "try:\n"
        " Path('ready').write_text('partial')\n"
        " time.sleep(.2)\n"
        " Path('ready').write_text('complete')\n"
        "finally:\n guard.rmdir()\n")
    python = shlex.quote(sys.executable)
    (shared / "Holmakefile").write_text(f"ready:\n\t{python} writer.py\n")
    branches = [tmp_path / "a", tmp_path / "b"]
    for branch in branches:
        branch.mkdir()
        (branch / "Holmakefile").write_text(
            "INCLUDES = ../shared\n"
            "result: ../shared/ready\n"
            "\t" + python + " -c \"from pathlib import Path; "
            "assert Path('../shared/ready').read_text() == 'complete'; "
            "Path('result').write_text('ok')\"\n")
    results = await asyncio.gather(*(
        srv.holmake(workdir=str(branch), target="result", timeout=30)
        for branch in branches))
    for branch, result in zip(branches, results):
        if "Build succeeded" not in result:
            assert result.startswith("ERROR:") and "overlap" in result.lower(), results
            result = await srv.holmake(workdir=str(branch), target="result", timeout=30)
            assert "Build succeeded" in result, result
    assert (shared / ".hol" / "locks" / "ready.lock").exists()
    assert all((branch / "result").read_text() == "ok" for branch in branches)


async def test_cancelling_one_detached_build_does_not_kill_independent_job(tmp_path):
    python = shlex.quote(sys.executable)
    roots = [tmp_path / "cancelled", tmp_path / "independent"]
    job_ids = []
    for root in roots:
        root.mkdir()
        (root / "worker.py").write_text(
            "from pathlib import Path\nimport time\n"
            "Path('started').touch()\n"
            "while not Path('release').exists(): time.sleep(.01)\n"
            "Path('result').write_text('ok')\n")
        (root / "Holmakefile").write_text(f"result:\n\t{python} worker.py\n")
        result = await srv.holmake(workdir=str(root), target="result", detach=True)
        job_ids.append(re.search(r"job=(\S+)", result).group(1))
    try:
        async def ready():
            while not all((root / "started").exists() for root in roots):
                await asyncio.sleep(.01)
        await asyncio.wait_for(ready(), 10)
        cancelled = await srv.hol_build_status(job_ids[0], cancel=True)
        assert "cancelled" in cancelled, cancelled
        other = await srv.hol_build_status(job_ids[1])
        assert "running" in other, other
        (roots[1] / "release").touch()
        await _wait_for_job_finished(job_ids[1])
        other = await srv.hol_build_status(job_ids[1])
        assert "Build succeeded" in other, other
    finally:
        for job in job_ids:
            await srv.hol_build_status(job, cancel=True)


async def test_build_does_not_delete_previous_or_peer_logs(tmp_path):
    logs = tmp_path / ".hol" / "logs"
    logs.mkdir(parents=True)
    prior = logs / "anotherTheory"
    prior.write_text("preserved diagnostic evidence")
    (tmp_path / "Holmakefile").write_text("result:\n\tfalse\n")
    result = await srv.holmake(workdir=str(tmp_path), target="result", timeout=10)
    assert "Build failed" in result, result
    assert prior.read_text() == "preserved diagnostic evidence"
    # An unchanged old failure must not be attributed to this request.
    assert "preserved diagnostic evidence" not in result


@pytest.mark.parametrize("detach", [False, True])
async def test_peer_starting_during_shared_write_is_refused_then_can_retry(tmp_path, detach):
    shared = tmp_path / "shared"
    shared.mkdir()
    python = shlex.quote(sys.executable)
    (shared / "writer.py").write_text(
        "from pathlib import Path\nimport time\n"
        "Path('ready').write_text('partial')\n"
        "Path('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "Path('ready').write_text('complete')\n")
    (shared / "Holmakefile").write_text(f"ready:\n\t{python} writer.py\n")
    job_ids = []
    try:
        for label in ("a", "b"):
            branch = tmp_path / label
            branch.mkdir()
            (branch / "Holmakefile").write_text(
                "INCLUDES = ../shared\nresult: ../shared/ready\n\t" + python +
                " -c \"from pathlib import Path; "
                "assert Path('../shared/ready').read_text() == 'complete'; "
                "Path('result').touch()\"\n")
            started = await srv.holmake(str(branch), target="result", detach=True if label == "a" else detach)
            if label == "b":
                assert started.startswith("ERROR:"), started
                assert "overlap" in started.lower() and job_ids[0] in started, started
                assert str(shared) in started, started
                assert not (branch / "result").exists()
                break
            job_ids.append(re.search(r"job=(\S+)", started).group(1))
            if label == "a":
                async def wait_started():
                    while not (shared / "started").exists():
                        await asyncio.sleep(.01)
                await asyncio.wait_for(wait_started(), 10)
        # No peer process may consume the first writer's partial output.
        (shared / "release").touch()
        for job in job_ids:
            await _wait_for_job_finished(job)
            status = await srv.hol_build_status(job)
            assert "Build succeeded" in status, status
        retried = await srv.holmake(str(tmp_path / "b"), target="result", timeout=10)
        assert "Build succeeded" in retried, retried
    finally:
        (shared / "release").touch()
        for job in job_ids:
            await srv.hol_build_status(job, cancel=True)


@pytest.mark.parametrize("artifact", ["ready", "ready.ui"])
async def test_cancelled_shared_writer_does_not_leave_silent_partial_dependency(tmp_path, artifact):
    shared = tmp_path / "shared"
    shared.mkdir()
    relative_output = f".hol/objs/{artifact}" if artifact.endswith(".ui") else artifact
    output = shared / relative_output
    python = shlex.quote(sys.executable)
    (shared / "writer.py").write_text(
        "from pathlib import Path\nimport time\n"
        f"output = Path({relative_output!r})\n"
        "output.parent.mkdir(parents=True, exist_ok=True)\n"
        "output.write_text('partial')\nPath('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "output.write_text('complete')\n")
    (shared / "Holmakefile").write_text(f"{artifact}:\n\t{python} writer.py\n")
    peer = tmp_path / "peer"
    peer.mkdir()
    (peer / "Holmakefile").write_text(
        f"INCLUDES = ../shared\nresult: ../shared/{artifact}\n\t" + python +
        " -c \"from pathlib import Path; "
        f"Path('result').write_text(Path('../shared/{relative_output}').read_text())\"\n")
    started = await srv.holmake(str(shared), target=artifact, detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        async def wait_started():
            while not (shared / "started").exists():
                await asyncio.sleep(.01)
        await asyncio.wait_for(wait_started(), 10)
        cancelled = await srv.hol_build_status(job, cancel=True)
        assert "cancelled" in cancelled, cancelled
        assert srv._build_jobs[job].done.is_set()
        assert job not in srv.build_claims.active
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert result.startswith("ERROR:") and "partial" in result.lower(), result
        assert str(output) in result and job in result, result
        assert not (peer / "result").exists(), "a successful peer consumed partial content"
        if artifact == "ready":
            # Native clean does not remove an arbitrary recipe's output.
            # A successful clean must not certify unchanged partial content.
            cleaned = await srv.holmake(str(shared), target="cleanAll", timeout=10)
            assert "Build succeeded" in cleaned, cleaned
            result = await srv.holmake(str(peer), target="result", timeout=10)
            assert result.startswith("ERROR:") and "partial" in result.lower(), result
        # An explicit repair makes the dependency safe to use again.
        output.unlink()
        (shared / "release").touch()
        repaired = await srv.holmake(str(shared), target=artifact, timeout=10)
        assert "Build succeeded" in repaired, repaired
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert "Build succeeded" in result, result
        assert (peer / "result").read_text() == "complete"
    finally:
        (shared / "release").touch()
        await srv.hol_build_status(job, cancel=True)


async def test_independent_writers_share_read_only_dependency_in_parallel(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    (shared / "ready").write_text("complete")
    (shared / "Holmakefile").write_text("ready:\n\tfalse\n")
    python = shlex.quote(sys.executable)
    roots = [tmp_path / "a", tmp_path / "b"]
    jobs = []
    try:
        for root in roots:
            root.mkdir()
            (root / "worker.py").write_text(
                "from pathlib import Path\nimport time\n"
                "assert Path('../shared/ready').read_text() == 'complete'\n"
                "Path('started').touch()\n"
                "while not Path('release').exists(): time.sleep(.01)\n"
                "Path('result').touch()\n")
            (root / "Holmakefile").write_text(
                f"INCLUDES = ../shared\nresult: ../shared/ready\n\t{python} worker.py\n")
            result = await srv.holmake(str(root), target="result", detach=True)
            assert "Build started" in result, result
            jobs.append(re.search(r"job=(\S+)", result).group(1))
        async def both_started():
            while not all((root / "started").exists() for root in roots):
                await asyncio.sleep(.01)
        await asyncio.wait_for(both_started(), 10)
        for job in jobs:
            assert "running" in await srv.hol_build_status(job)
        for root in roots:
            (root / "release").touch()
        for job in jobs:
            await _wait_for_job_finished(job)
            assert "Build succeeded" in await srv.hol_build_status(job)
    finally:
        for root in roots:
            (root / "release").touch()
        for job in jobs:
            await srv.hol_build_status(job, cancel=True)


@pytest.mark.parametrize("detach", [False, True])
async def test_build_preexec_generates_rules_once_and_retains_diagnostics(tmp_path, detach):
    python = shlex.quote(sys.executable)
    (tmp_path / "prepare.py").write_text(
        "from pathlib import Path\n"
        "with Path('preexec-count').open('a') as log: log.write('run\\n')\n"
        "print('fixture preexec diagnostic')\n"
        "Path('Holmakefile').write_text('result:\\n\\ttouch result\\n')\n")
    (tmp_path / ".hol_preexec").write_text(f"{python} prepare.py\n")
    result = await srv.holmake(str(tmp_path), target="result", timeout=10, detach=detach)
    job = None
    try:
        if detach:
            assert "Build started" in result, result
            job = re.search(r"job=(\S+)", result).group(1)
            await _wait_for_job_finished(job)
            result = await srv.hol_build_status(job)
        assert "Build succeeded" in result, result
        assert "fixture preexec diagnostic" in result, result
        assert "=== Dependency discovery / preexec output ===" in result, result
        assert "=== Build output (preexec already ran; disabled below) ===" in result, result
        assert (tmp_path / "result").exists()
        assert (tmp_path / "preexec-count").read_text().splitlines() == ["run"]
    finally:
        if job:
            await srv.hol_build_status(job, cancel=True)


async def test_synchronous_budget_includes_dependency_preflight(tmp_path):
    python = shlex.quote(sys.executable)
    (tmp_path / ".hol_preexec").write_text(f"{python} -c 'import time; time.sleep(.7)'\n")
    (tmp_path / "Holmakefile").write_text(
        f"result:\n\t{python} -c 'import time; from pathlib import Path; "
        "time.sleep(.7); Path(\"result\").touch()'\n")
    result = await srv.holmake(str(tmp_path), target="result", timeout=1)
    assert "timed out" in result.lower(), result
    assert not (tmp_path / "result").exists(), "preflight silently extended the build budget"


async def test_detached_build_does_not_use_synchronous_timeout_for_preflight(tmp_path):
    python = shlex.quote(sys.executable)
    (tmp_path / ".hol_preexec").write_text(f"{python} -c 'import time; time.sleep(1.1)'\n")
    (tmp_path / "Holmakefile").write_text("result:\n\ttouch result\n")
    result = await srv.holmake(str(tmp_path), target="result", timeout=1, detach=True)
    job = None
    try:
        assert "Build started" in result, result
        job = re.search(r"job=(\S+)", result).group(1)
        await _wait_for_job_finished(job)
        assert "Build succeeded" in await srv.hol_build_status(job)
    finally:
        if job:
            await srv.hol_build_status(job, cancel=True)


async def test_recursive_clean_is_refused_while_peer_reads_shared_interfaces(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    (shared / "ready.sig").write_text("signature Ready = sig val marker : int end\n")
    (shared / "ready.sml").write_text("structure Ready : Ready = struct val marker = 1 end\n")
    (shared / "Holmakefile").write_text("")
    built = await srv.holmake(str(shared), target="ready.uo", timeout=10)
    assert "Build succeeded" in built, built
    interface_path = shared / ".hol/objs/ready.ui"
    interface = interface_path.read_text()
    reader = tmp_path / "reader"
    reader.mkdir()
    python = shlex.quote(sys.executable)
    (reader / "worker.py").write_text(
        "from pathlib import Path\nimport time\n"
        "Path('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        f"assert Path('../shared/.hol/objs/ready.ui').read_text() == {interface!r}\n"
        "Path('result').touch()\n")
    (reader / "Holmakefile").write_text(
        f"INCLUDES = ../shared\nresult: ../shared/ready.ui\n\t{python} worker.py\n")
    cleaner = tmp_path / "cleaner"
    cleaner.mkdir()
    (cleaner / "Holmakefile").write_text(
        "CLINE_OPTIONS = --recursive-clean\nINCLUDES = ../shared\n"
        "result: ../shared/ready.ui\n\ttouch result\n")
    started = await srv.holmake(str(reader), target="result", detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        async def ready():
            while not (reader / "started").exists():
                await asyncio.sleep(.01)
        await asyncio.wait_for(ready(), 10)
        result = await srv.holmake(str(cleaner), target="cleanAll", timeout=10)
        assert result.startswith("ERROR:") and "overlap" in result.lower(), result
        assert job in result, result
        assert interface_path.read_text() == interface
        (reader / "release").touch()
        await _wait_for_job_finished(job)
        assert "Build succeeded" in await srv.hol_build_status(job)
    finally:
        (reader / "release").touch()
        await srv.hol_build_status(job, cancel=True)
