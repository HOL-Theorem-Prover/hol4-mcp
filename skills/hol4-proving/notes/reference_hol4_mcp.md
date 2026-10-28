---
name: reference_hol4_mcp
description: The running hol4-mcp server — install location (editable, so edits are live), the local-only `localfixes` branch (don't upstream), the minimum HOL, and the complaint inbox.
metadata:
  type: reference
---

# Install location
`~/hol4-mcp` is the running server's source tree, installed EDITABLE — an edit there is live for the running server, no reinstall step. How it is launched (interpreter, entry point, launcher config) is machine-specific: don't record it here, read the MCP config if you ever need it. Dev/test commands: `~/hol4-mcp/CLAUDE.md`.

# `localfixes` branch — don't upstream
`~/hol4-mcp` runs the `localfixes` branch, carrying user-curated commits intentionally NOT in `origin/master` (navigation/timeout fixes, diagnostics, guidance text, SDK monkey-patch). It is pushed to `origin/localfixes` as a backup; that is not a step towards merging. Don't propose cherry-picking them or opening a PR unless the user explicitly asks. When behaviour depends on a local-only commit, rely on `~/hol4-mcp` being live — that (not GitHub) is the source of truth for the running MCP.

# HOL requirement
The server needs HOL `master` with TacticParse's positioned combinators (`FOpenThen1`, `FOpenBy` and `FOpenSufficesBy` carrying spans), which `sml_helpers/tactic_prefix.sml` matches. Against an older HOL every session start fails with "the HOL at … is too old for hol4-mcp": update HOL and rebuild it; no tool call can work around it.

# Complaint inbox

Every agent must record each suspected MCP issue or usability rough edge in
`~/hol4-mcp/complaints/` as soon as it is encountered. Unconfirmed observations
belong here too; label them **suspected**, rather than presenting a cause as
established. Search existing reports first and append evidence to a matching
report; otherwise create `YYYY-MM-DD-short-description.md`.

Include the tool/operation, expected and observed behavior, relevant inputs
and output, and the impact on the task. Prefer a minimal reproducer or regression
test, with its command and result; if none is practical yet, say what remains
untested. Keep reports concise and exclude credentials or unrelated private
content. Recording a complaint does not require permission or authorize a
repair outside the current task. If the inbox cannot be written, include the
report in the user handoff and state the write failure.

During MCP maintenance, review the inbox at the start and before finishing.
Move useful reproducers into permanent tests. Once a report is fixed and tested,
disproved with evidence, or explicitly dismissed by the user, record that
disposition in the maintenance commit and remove the report. Retain unresolved
reports; periodically empty resolved material rather than maintaining a second
history here. Keep `complaints/.gitkeep` so the inbox remains tracked when empty.
