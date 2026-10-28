# A timeout while computing the step plan is reported as `Failed to parse step plan: No JSON object found …`

**Status:** confirmed by reading (2026-10-28); recorded as a recurring field shape
in `MCP_BUGS.md` §4. Low severity: the raw `TIMEOUT` text does appear, but only
after a misleading headline.
**Component:** `hol4_mcp/hol_cursor.py` (all `goalfrag_step_plan_json` call sites:
`_reparse_steps_on_edit`, `enter_theorem`, and the others that catch `HOLParseError`
as `Failed to parse step plan: {e}`); `hol4_mcp/hol_file_parser.py`
`parse_step_plan_output` / `_find_json_line`.
(Migrated 2026-10-28 from `MCP_BUGS.md` §4 "Other recurring shapes worth fixing";
`git show 62481d6:MCP_BUGS.md`.)

## Mechanism

When the step-plan request runs out of time, `HOLSession.send` returns
`TIMEOUT after Ns - sent interrupt.` with no JSON. `parse_step_plan_output` →
`_find_json_line` then raises
`HOLParseError("No JSON object found in goalfrag_step_plan_json output. Raw output: <first 200 chars>")`,
and the caller wraps that as `Failed to parse step plan: …`. The resulting message
reads as a **parse** failure of the proof body, with the timeout visible only in
the raw-output preview.

## Expected

A timeout is reported as a timeout, for example
`TIMEOUT computing the step plan for <thm> (>Ns)`, and is not confused with a
malformed proof body. An agent seeing "parse" will go looking for unbalanced
delimiters (compare the plan-coverage error that `parse_step_plan_output` raises for
real truncation).

## Reproducer (to build)

Replace the session in a cursor test with a stub whose `send` returns
`"TIMEOUT after 1s - sent interrupt."` for the `goalfrag_step_plan_json` command, and
check that the resulting `StateAtResult.error` names a timeout, not a parse failure.

## Impact

Misleading diagnosis. Under the current defaults (step-plan timeout 300 s in the
working tree) this is rare.
