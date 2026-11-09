"""Dependency freshness includes missing interfaces, not just existing .uo's."""
import os
import time
from types import SimpleNamespace
from unittest.mock import AsyncMock

import pytest

from hol4_mcp.hol_cursor import FileProofCursor


def cursor_at(tmp_path, load_path='val it = [] : string list'):
    session = SimpleNamespace(workdir=tmp_path, send=AsyncMock(return_value=load_path))
    return FileProofCursor(tmp_path / "targetScript.sml", session)


@pytest.mark.parametrize("suffix", ["uo", "ui", "dat"])
async def test_new_interface_detected(tmp_path, suffix):
    cursor = cursor_at(tmp_path)
    await cursor._record_dep_artifacts(["ancestorTheory"])
    assert cursor._check_dep_artifacts() is None
    (tmp_path / f"ancestorTheory.{suffix}").write_text("built")
    assert cursor._check_dep_artifacts() == "ancestorTheory"


@pytest.mark.parametrize("suffix", ["uo", "ui", "dat"])
async def test_removed_then_restored_interface_detected(tmp_path, suffix):
    artifact = tmp_path / f"ancestorTheory.{suffix}"
    artifact.write_text("built")
    cursor = cursor_at(tmp_path)
    await cursor._record_dep_artifacts(["ancestorTheory"])
    assert cursor._check_dep_artifacts() is None
    artifact.unlink()
    assert cursor._check_dep_artifacts() == "ancestorTheory"
    await cursor._record_dep_artifacts(["ancestorTheory"])
    artifact.write_text("rebuilt")
    assert cursor._check_dep_artifacts() == "ancestorTheory"


async def test_rebuilt_interface_detected(tmp_path):
    artifact = tmp_path / "ancestorTheory.uo"
    artifact.write_text("built")
    cursor = cursor_at(tmp_path)
    await cursor._record_dep_artifacts(["ancestorTheory"])
    stat = artifact.stat()
    os.utime(artifact, ns=(stat.st_atime_ns, stat.st_mtime_ns + 1_000_000))
    assert cursor._check_dep_artifacts() == "ancestorTheory"


async def test_relative_loadpath_and_shadowing(tmp_path):
    depdir = tmp_path / "deps"
    depdir.mkdir()
    (depdir / "ancestorTheory.uo").write_text("built")
    cursor = cursor_at(tmp_path, 'val it = ["deps"] : string list')
    await cursor._record_dep_artifacts(["ancestorTheory"])
    assert cursor._check_dep_artifacts() is None
    assert cursor._dep_artifacts["ancestorTheory"][depdir / "ancestorTheory.uo"]
    (tmp_path / "ancestorTheory.uo").write_text("shadowing")
    assert cursor._check_dep_artifacts() == "ancestorTheory"


async def test_missing_parent_creation_detected(tmp_path):
    cursor = cursor_at(tmp_path)
    await cursor._record_dep_artifacts(["ancestorTheory"])
    objects = tmp_path / ".hol" / "objs"
    objects.mkdir(parents=True)
    (objects / "ancestorTheory.uo").write_text("new shadowing artifact")
    assert cursor._check_dep_artifacts() == "ancestorTheory"


@pytest.mark.parametrize("link_before_snapshot", [True, False])
async def test_dangling_symlink_target_appearance_detected(tmp_path, link_before_snapshot):
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    target = elsewhere / "built.uo"
    link = tmp_path / "ancestorTheory.uo"
    cursor = cursor_at(tmp_path)
    if link_before_snapshot:
        link.symlink_to(target)
    await cursor._record_dep_artifacts(["ancestorTheory"])
    if not link_before_snapshot:
        link.symlink_to(target)
        assert cursor._check_dep_artifacts() is None
    # Creating the target does not change the link's parent directory.
    target.write_text("built")
    assert cursor._check_dep_artifacts() == "ancestorTheory"


async def test_warm_absence_checks_scale_with_directories_not_candidates(tmp_path, monkeypatch):
    import json

    dirs = [tmp_path / f"dir{i}" for i in range(40)]
    for directory in dirs:
        directory.mkdir()
    cursor = cursor_at(tmp_path, 'val it = ' + json.dumps(list(map(str, dirs))))
    artifact = tmp_path / "existingTheory.uo"
    artifact.write_text("built")
    past = time.time() - 10          # directories last modified well before the snapshot
    for directory in [tmp_path, *dirs]:
        os.utime(directory, (past, past))
    await cursor._record_dep_artifacts(["existingTheory"] +
                                      [f"missing{i}Theory" for i in range(200)])
    file_stats, directory_stats = [], []
    real_file_stamp = cursor._artifact_stamp
    real_directory_stamp = cursor._directory_stamp

    def file_stamp(path):
        file_stats.append(path)
        return real_file_stamp(path)

    def directory_stamp(path):
        directory_stats.append(path)
        return real_directory_stamp(path)

    monkeypatch.setattr(cursor, "_artifact_stamp", file_stamp)
    monkeypatch.setattr(cursor, "_directory_stamp", directory_stamp)
    assert cursor._check_dep_artifacts() is None
    assert file_stats == [artifact]
    assert len(directory_stats) == len(set(directory_stats)) == 2 * (len(dirs) + 1)
    # An unrelated directory-entry change is inspected, and once the change has
    # aged past the racy window the directory is cheap again.
    (dirs[0] / "unrelated").write_text("unrelated")
    assert cursor._check_dep_artifacts() is None
    os.utime(dirs[0], (past, past))
    assert cursor._check_dep_artifacts() is None
    file_stats.clear()
    assert cursor._check_dep_artifacts() is None
    assert file_stats == [artifact]
    # No timer window: a shadowing file is caught on the very next call.
    (dirs[0] / "missing100Theory.ui").write_text("built")
    assert cursor._check_dep_artifacts() == "missing100Theory"


async def test_fresh_directory_stamp_is_not_trusted(tmp_path, monkeypatch):
    """A directory modified within the racy window can gain an entry without its
    stamp changing (coarse filesystem timestamps), so its candidates are scanned."""
    cursor = cursor_at(tmp_path)
    await cursor._record_dep_artifacts(["ancestorTheory"])
    recorded, trusted = cursor._dep_parent_stamps[tmp_path]
    assert not trusted
    (tmp_path / "ancestorTheory.uo").write_text("built")
    monkeypatch.setattr(cursor, "_directory_stamp",
                        lambda path: recorded if path == tmp_path else None)
    assert cursor._check_dep_artifacts() == "ancestorTheory"


async def test_aged_directory_stamp_is_trusted(tmp_path):
    past = time.time() - 10
    os.utime(tmp_path, (past, past))
    cursor = cursor_at(tmp_path)
    await cursor._record_dep_artifacts(["ancestorTheory"])
    assert cursor._dep_parent_stamps[tmp_path][1]


def test_missing_interface_diagnostic_names_build_target(tmp_path):
    cursor = cursor_at(tmp_path)
    error = cursor._dep_load_error(
        "ancestorTheory", "Exception- Fail Cannot find file ancestorTheory.ui", 1, 300)
    assert "ancestorTheory.uo" in error
    assert "no target proof has run" in error


def test_oom_diagnostic_names_effective_heap(tmp_path):
    cursor = cursor_at(tmp_path)
    cursor.session.maxheap_mb = 12288
    error = cursor._dep_load_error("ancestorTheory", "Run out of store", 1, 300)
    assert "ancestorTheory" in error and "12288" in error
    assert "HOL4_MCP_MAXHEAP_MB" in error and "no target proof has run" in error
