# `localfixes` branch

Local-only operating branch — **never push to remote**. Default checkout
for this clone. Each commit is one logical change; the history is `git log`
/ `git show <sha>` (this file does not mirror it). Policy and operating
pointers for the running server: `skills/hol4-proving/notes/reference_hol4_mcp.md`.

## Notes files

- `LOCAL_CHANGES.md` — this file.
- Resolved-history notes (the navigation/caching defect register
  `MCP_BUGS.md` with its companions `MCP_BUGS_review.md` and
  `MCP_TACTIC_COST_review.md`; `HOL_STATE_AT_RESUME_BUG_NOTES.md`;
  `PARENS_NAVIGATION_NOTES.md`) were removed after `62481d6`; read them with
  `git show 62481d6:<file>`. Test docstrings citing finding numbers refer to
  those files.
- `HOL_STATE_AT_DEF_EDIT_STALENESS_NOTES.md` — the `Unknown identifier`
  symptom after editing a `Definition` above the checkpoint; the two defects
  actually found are fixed (2026-08-28). The unreproduced original report is in
  `complaints/`.
- `complaints/` — the open-issue inbox (workflow:
  `skills/hol4-proving/notes/reference_hol4_mcp.md`, Complaint inbox).

## Upstreaming notes

- `91255af` + `9a6771d` — opened as PR #21 to upstream
  `HOL-Theorem-Prover/hol4-mcp`.
- `efb689d` should be obsoleted once mcp PR #2481 or #2493 merges.
- `83e42e2` is upstreamable as observability.
- `e134b5c`, `69ee385` are workflow opinions — discuss before upstreaming.
- `011c5b2` is personal preference for cake-while; do not upstream.
- `714b941` + `b43c34c` — try out locally first; if stable through the
  cake-while cleanup tasks, open as a separate PR. Has a documented
  trade-off (lose mid-arm navigation in parens-grouped LT chains).
- `67b6e2e` is a workflow opinion — discuss before upstreaming.
- The Resume goal-setup fix is a correctness fix (avoids a `Parse.Term`
  re-parse that crashes / silently renames under a clashing parse context).
  Upstreamable — discuss before opening a PR.
