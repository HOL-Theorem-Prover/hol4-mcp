"""Read-only warm-cursor microbenchmark; does not start HOL or run proofs.

Run with the editable installation's Python. --broad-root deliberately uses
every Holmakefile directory as a synthetic stress load path, not a claim about
the live HOL session's actual loadPath. Parsing is warmed before measurement.
"""
import argparse
import asyncio
import json
from pathlib import Path
import statistics
import time
from types import SimpleNamespace
from unittest.mock import AsyncMock

from hol4_mcp.hol_cursor import FileProofCursor, HOLDIR, get_script_dependencies


async def benchmark(args):
    dirs = [p.resolve() for p in args.load_dir]
    if args.broad_root:
        dirs.extend(sorted({p.parent for p in args.broad_root.rglob("Holmakefile")}))
    dirs.append(HOLDIR / "sigobj")
    for script in args.scripts:
        script = script.resolve()
        session = SimpleNamespace(
            workdir=script.parent,
            send=AsyncMock(return_value="val it = " + json.dumps(list(map(str, dirs)))))
        cursor = FileProofCursor(script, session)
        deps = await get_script_dependencies(script)
        await cursor._record_dep_artifacts(deps)
        cursor._reparse_if_changed()
        # This is a parser/freshness-only mock, not an initialized HOL session.
        # The first parse correctly requests initialization for its new prefix.
        cursor._needs_session_reinit = False
        optimized = cursor._check_dep_artifacts

        def original_scan():
            for dep, artifacts in cursor._dep_artifacts.items():
                for path, stamp in artifacts.items():
                    if cursor._artifact_stamp(path) != stamp:
                        return dep
            return None

        timings = {}
        for label, implementation in [("direct_candidate_scan", original_scan),
                                       ("directory_grouped", optimized)]:
            cursor._check_dep_artifacts = implementation
            samples = []
            for _ in range(args.repeat):
                start = time.perf_counter()
                assert not cursor._reparse_if_changed(), "File changed during benchmark"
                assert not cursor._needs_session_reinit, "Dependency changed during benchmark"
                samples.append((time.perf_counter() - start) * 1000)
            timings[label + "_median_ms"] = round(statistics.median(samples), 3)
        print(json.dumps({"file": str(script), "bytes": script.stat().st_size,
                          "dependencies": len(deps), "load_dirs": len(dirs),
                          "candidates": sum(map(len, cursor._dep_artifacts.values())),
                          "existing_artifacts": len(cursor._dep_present_artifacts),
                          "absent_parent_dirs": len(cursor._dep_absent_artifacts),
                          **timings}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scripts", type=Path, nargs="+")
    parser.add_argument("--load-dir", type=Path, action="append", default=[])
    parser.add_argument("--broad-root", type=Path)
    parser.add_argument("--repeat", type=int, default=15)
    asyncio.run(benchmark(parser.parse_args()))
