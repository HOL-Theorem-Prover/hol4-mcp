# `--tactic-timeout` help text gives a default (5.0) that the server does not use

**Status:** confirmed by reading (2026-10-28). Cosmetic.
**Component:** `hol4_mcp/hol_mcp_server.py` (`serve_parser.add_argument("--tactic-timeout", …)`,
the `TACTIC_TIMEOUT` module constant) and `hol4_mcp/hol_cursor.py` (`FileProofCursor.__init__`
`tactic_timeout` default).
(Migrated 2026-10-28 from `MCP_TACTIC_COST_review.md` §2 "Extras found while reading";
`git show 62481d6:MCP_TACTIC_COST_review.md`.)

## Observed

- The help reads: `Max seconds per tactic during proof replay (default: 5.0, or HOL_TACTIC_TIMEOUT env)`.
- The effective default is `TACTIC_TIMEOUT = float(os.environ.get("HOL_TACTIC_TIMEOUT", …))`:
  `"60.0"` at HEAD, and `"600.0"` in the current uncommitted working tree.
- `FileProofCursor.__init__` has its own default (`5.0` at HEAD, `50.0` in the working tree),
  which the server's construction of the cursor overrides.

## Expected

The help states the value actually used, or derives it from `TACTIC_TIMEOUT`.

## Impact

Anyone reasoning about timeout budgets from `--help` is off by 12× (120× with the
working-tree values).

## Acceptance

A test that asserts the help text contains the effective default (for example,
format the help from `TACTIC_TIMEOUT`).
