# Development Notes

The package is installed editable into the Python environment that provides the
`hol4-mcp` executable, so source edits affect the running server without a
reinstall. Locate that interpreter rather than assuming a virtualenv path (it is
the one that can `import hol4_mcp`).

```bash
$PY -m pip install -e .
```

## Running tests

```bash
$PY -m pytest tests/ -q
```

Requires `pytest` and `pytest-asyncio` in that same environment. Run the suite
serially: the HOL process and build-coordination integration tests are not safe
under pytest-xdist.

## FastMCP

This project requires FastMCP >= 3.0. In 3.x, `@mcp.tool()` returns the
original function unchanged (no `.fn` unwrapping), so tool functions stay
directly callable in tests. Do not use `.fn` on tools.

## Hooks and skill

`hooks/h*.py` with `hooks/install_hooks.py` are the Claude Code integration of
the HOL4 proof-interaction policies; the skill they enforce is
`skills/hol4-proving/`. Both are globally reachable, not project-local — see
`hooks/README.md`. Keep their registration and `~/.claude` state contract
unchanged. Codex-specific translation and state isolation live under
`integrations/codex/`; its bundled wiring is `hooks/hooks.json`.

Before changing the skill, hook policy, or MCP server guidance, read
`skills/hol4-proving/notes/reference_hol4_docs.md`. Before changing this local
server, also read `skills/hol4-proving/notes/reference_hol4_mcp.md` and preserve
the local-only branch policy documented there.

## Complaint inbox

Whenever any agent encounters a suspected MCP bug or usability rough edge,
record it in `complaints/` immediately, even if unconfirmed, and tell the user
in one line. Follow the report and periodic cleanup workflow in
`skills/hol4-proving/notes/reference_hol4_mcp.md` (Complaint inbox).
