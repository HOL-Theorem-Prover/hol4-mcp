# Holmake builds of large CakeML-heap targets intermittently die with `Run out of store` (probably not MCP-specific)

**Status:** suspected; cause unknown. Seen 6 times (5 through the `holmake` tool,
1 from a plain shell), so the MCP is probably not the cause. The open question is
whether the tool should absorb the flake.
**Component:** `holmake` tool (`hol4_mcp/hol_mcp_server.py` `holmake`, which builds the
command `[holmake_bin, "--no_preexecs", "--qof", f"--heap-size={heap_size}"]` + `-j`).
**First seen:** 2026-10-20 · **Last seen:** 2026-10-25.

## Summary

Builds whose `HOLHEAP` is the CakeML `cake_compile_heap` sometimes fail with
`Run out of store - interrupting threads`. Most failures come within 5–20 s,
while ancestors are loading; one came at the very end of an 898 s build, while
the theory was being exported. The same command re-run minutes later usually
succeeds. The machine had plenty of free memory each time.

## Occurrences

| date | via | workdir (under `~/research/cakes/`) | target | heap / jobs | outcome | job / log |
|---|---|---|---|---|---|---|
| 10-20 | tool, detach | `cake-xlrup/examples/cnf/lrup/array/compilation` | `lrupCompileTheory` | 16384/4, 32768/2, 32768/1 | OOS after 4–5 s, at `quse …/basis/HashtableProgTheory.sml : Interrupt` | `c19ea3b6026e`, `015ad5082e75`, `55a3e2ad0a7b` (logs pruned) |
| 10-20 | shell | same | same | 32768/1 | **succeeded**, 32 s | — |
| 10-21 | shell | `xlrup-bench/...` | `xlrupCompileTheory` | 32768/2 | OOS after 5 s; identical re-run succeeded (72 s) | `xlrup-bench/work/rebuild-cleanup/xlrupCompile-variant.log` |
| 10-24 | tool, detach | `cake-pb/examples/pseudo_bool/cnf_encoding/array/compilation` | `cnfCompileTheory` (`--fast` prototype) | 40000/default | ran 898 s, wrote both `.S` files, then `Exporting theory "cnfCompile" ... Run out of store` / `Failure while writing theory!` | `1d6a5e8d9b45` (log pruned) |
| 10-25 | tool, detach | same | `cnfCompileTheory` | 40000/default | OOS after 20 s (log has only that line) | `a3f3e74012da` |
| 10-25 | tool, detach | same | `cnfCompileTheory` | 40000/default | OOS after 13 s, at `quse …/basis/UnsafeProgTheory.sml : Interrupt` | `4873bf4a08a7` |

Notes:
- Right before the 10-24 failure, `npbc_fullCompileTheory` (job `96609c7d254b`) built through
  the tool at heap 40000, export included. The same is true before the 10-25 pair (`621b4d6a3eca`).
- A later tool build of `cnfCompileTheory` succeeded (job `c6ad81cbef6d`, 2026-10-26, exit 0).
  Its job count is not recorded.
- Job logs live in `/var/tmp/hol4-mcp-1000/builds/<job>.log`. The older ones have already been pruned.

## Ruled out so far

- Resource limits: `RLIMIT_AS`/`DATA`/`RSS` are unlimited for the MCP server, as in the shell.
  There are no `POLY*` environment variables in the server.
- Memory pressure: `vm.overcommit_memory=0`, Committed_AS 22 GB of a 99 GB limit, and
  `free -g` showed 46–54 GB available right after the failures.
- A direct `hol --gcthreads=1 --maxheap 32768 run --holstate=<cake_compile_heap>` loading
  `lrup_arrayFullProgTheory` succeeded (17 s, 2.1 GB RSS).

## Untested

- Whether Poly/ML's heap sizing (`--heap-size` against the saved heap's own parameters) is the
  trigger, as opposed to real exhaustion.
- Whether the failure rate depends on `-j`, or on other heavy builds running at the same time.
- Other environment differences between the server and a shell.

## Impact

The failed build has to be re-run, which costs up to 15 min when the failure
comes during export. In 10-20 it blocked a checker rebuild until the build was
run from a shell.

## Workaround

Re-run the same build. Holmake also has a `retry_oos` option, not yet tried.

## Acceptance

Either a reproducer that isolates a cause, or a decision on whether `holmake`
should detect `Run out of store` and say it may be transient (or retry).
