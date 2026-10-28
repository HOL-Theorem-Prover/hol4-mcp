# Three fixes from the August defect register have no regression test

**Status:** confirmed test-coverage gap (no defect observed). The fixes landed;
only the tests that pin them are missing.
**Component:** `tests/`, `hol4_mcp/hol_mcp_server.py` (`hol_goals`, `hol_state_at`),
`hol4_mcp/hol_session.py` (`HOLSession.drain_stale`).
(Migrated 2026-10-28 from `MCP_BUGS.md` §6 "Not covered by a test". The finding
numbers refer to that register and to `MCP_BUGS_review.md`, both removed after
`62481d6`; read them with `git show 62481d6:<file>`.)

## Gaps

1. **Finding #1, advisory half.** `hol_goals` renders `_state_caveat_lines`, the same helper
   `hol_state_at` uses: the inside-step NOTE, the `⚠ NOT VALIDATED` self-cheat refusal,
   `[auto-cheated deps: …]`, and `[prefix-skip mode ON]`. No test checks that `hol_goals` keeps
   showing them. The `hol_goals` tests in `tests/test_repro_failure_output.py` and
   `tests/test_repro_concurrency.py` cover the timing footer and concurrency only.
2. **Finding #11, pipe-drain locking.** Both `session._drain_pipe()` calls that ran outside
   `HOLSession._lock` now go through `HOLSession.drain_stale`, which takes the lock. The field
   symptom, seen once, was `RuntimeError: read() called while another coroutine is already
   waiting for incoming data` on the failed-proof path. The only `drain_stale` references in
   `tests/` are mock stubs (`test_repro_checkpoints.py`, `test_broken_chain_partial_reload.py`).
3. **Improvement A-5, pending-reinit disclosure.** The disclosure is checked through
   `cursor.status` (`tests/test_repro_checkpoints.py`), not through `hol_state_at`, which is
   the tool a caller actually uses (its `[Session reinit: …]` line).

## Impact

A refactor could drop any of these without a test failing. Gap 1 would bring back
a silent-wrong-state defect (finding #1 was severity 1).

## Acceptance

One test per gap, each driving the tool function that callers use (FastMCP 3.x
tools can be called directly, as described in `AGENTS.md`):
1. `hol_goals(file=…, line=…)` at a position that triggers each caveat shows the same caveat
   lines as `hol_state_at`.
2. A failed-proof path that drains while another coroutine reads, with no `RuntimeError`.
3. After an edit that schedules a reinit, `hol_state_at` output contains the `[Session reinit: …]` line.
