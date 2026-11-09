"""Runtime assets must survive building a wheel from the source distribution."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import zipfile

import pytest


def test_sdist_wheel_preserves_runtime_assets(tmp_path):
    pytest.importorskip("hatchling", reason="packaging check needs the dev dependency hatchling")
    root = Path(__file__).resolve().parents[1]
    source = tmp_path / "source"
    source.mkdir()
    for name in ("pyproject.toml", "LICENSE"):
        shutil.copy2(root / name, source / name)
    shutil.copytree(root / "hol4_mcp", source / "hol4_mcp",
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    archives = tmp_path / "archives"
    archives.mkdir()
    subprocess.run(
        [sys.executable, "-c", "from hatchling.build import build_sdist; "
         "import sys; build_sdist(sys.argv[1])", str(archives)],
        cwd=source, env=os.environ.copy(), check=True, capture_output=True,
    )
    assets = list((root / "hol4_mcp/sml_helpers").glob("*.sml"))
    assets.append(root / "hol4_mcp/pi_extension/hol4-mcp.ts")
    extracted = tmp_path / "extracted"
    with tarfile.open(next(archives.glob("*.tar.gz"))) as archive:
        prefix = archive.getnames()[0].split("/")[0]
        for asset in assets:
            name = f"{prefix}/{asset.relative_to(root).as_posix()}"
            assert name in archive.getnames(), f"Missing runtime asset: {name}"
            assert archive.extractfile(name).read() == asset.read_bytes()
        archive.extractall(extracted, filter="data")
    subprocess.run(
        [sys.executable, "-c", "from hatchling.build import build_wheel; "
         "import sys; build_wheel(sys.argv[1])", str(archives)],
        cwd=extracted / prefix, env=os.environ.copy(), check=True, capture_output=True,
    )
    with zipfile.ZipFile(next(archives.glob("*.whl"))) as archive:
        for asset in assets:
            name = asset.relative_to(root).as_posix()
            assert name in archive.namelist(), f"Missing runtime asset: {name}"
            assert archive.read(name) == asset.read_bytes()
