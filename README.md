# hol4-mcp

An [MCP](https://modelcontextprotocol.io/) server that gives LLM agents interactive access to the [HOL4](https://hol-theorem-prover.org/) theorem prover. Agents can start HOL sessions, navigate proofs, inspect goal states, and build theories — all through structured tool calls.

## Features

- **Proof cursor** — Navigate to any position in a proof file and see the goal state. The cursor tracks file edits, replays tactics incrementally, and uses PolyML checkpoints for fast state restoration.
- **Multi-theorem files** — Parse `*Script.sml` files to discover theorems, definitions, and resume blocks. Enter any theorem and step through its proof.
- **Holmake integration** — Build theories with progress reporting and failure diagnostics (build logs, error context).
- **Session management** — Multiple named HOL sessions with idle timeout, automatic garbage collection, and SIGINT-based interrupt for runaway tactics.
- **Change detection** — Content hashing detects file edits automatically. No need to restart sessions after modifying proof files.
- **Pi extension** — Ships with a [pi](https://github.com/badlogic/pi-mono) extension that registers all tools dynamically.

## Requirements

- [HOL4](https://hol-theorem-prover.org/) installed, with `HOLDIR` environment variable set (defaults to `~/HOL`)
- Python ≥ 3.11
- [uv](https://github.com/astral-sh/uv) (recommended) or pip

## Installation

```bash
# From source
uv pip install -e .

# Or from wheel
uv pip install hol4-mcp
```

### Pi

[Pi](https://github.com/badlogic/pi-mono) uses an extension (not MCP config). Install it:

```bash
hol4-mcp install-pi
```

This copies `hol4-mcp.ts` to `~/.pi/agent/extensions/`. No other configuration needed — the extension spawns the MCP server as a subprocess on first tool use, discovers tools dynamically, and cleans up on session exit.

Make sure `hol4-mcp` is on your `PATH` and `HOLDIR` is set in your shell environment.

The agent sees a single `hol4_mcp` tool with actions `list`, `call`, `interrupt`, and `restart`.

### Claude Code

Add to `.mcp.json` in your project root (or `~/.claude/mcp.json` globally):

```json
{
  "mcpServers": {
    "hol4": {
      "command": "hol4-mcp",
      "args": ["--transport", "stdio"],
      "env": {
        "HOLDIR": "/path/to/HOL"
      }
    }
  }
}
```

### Claude Desktop

Add to `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS) or `%APPDATA%\Claude\claude_desktop_config.json` (Windows):

```json
{
  "mcpServers": {
    "hol4": {
      "command": "hol4-mcp",
      "args": ["--transport", "stdio"],
      "env": {
        "HOLDIR": "/path/to/HOL"
      }
    }
  }
}
```

### Other MCP clients

Run the server directly:

```bash
# stdio (default, for MCP clients)
hol4-mcp

# HTTP or SSE
hol4-mcp serve --transport http --port 8000
```

## Tools

### Session lifecycle

| Tool | Description |
|------|-------------|
| `hol_start` | Start a HOL REPL session in a working directory |
| `hol_stop` | Terminate a session |
| `hol_restart` | Restart session (preserves workdir and env) |
| `hol_sessions` | List active sessions with age, status, and cursor info |
| `hol_setenv` | Set environment variables and auto-restart |

### Proof navigation

| Tool | Description |
|------|-------------|
| `hol_state_at` | Get proof state at a file position (line/col). Auto-inits session and cursor from `file=` parameter. |
| `hol_check_proof` | Check if a theorem's proof completes. Reports pass/fail, timing, and failure location. |
| `hol_file_status` | Get file overview: theorem list, cheat count, per-proof timing. |

### Raw interaction

| Tool | Description |
|------|-------------|
| `hol_send` | Send raw SML to HOL (for DB queries, type checking, term parsing) |
| `hol_interrupt` | Send SIGINT to abort a runaway tactic |

### Build

| Tool | Description |
|------|-------------|
| `holmake` | Run `Holmake --qof` with progress reporting and failure log extraction |
| `hol_log` | Read a specific theory's build log |
| `hol_logs` | List available build logs |

## Typical workflow

```
1. hol_state_at(line=15, col=1, file="myScript.sml")
   → Shows goals at that proof position

2. Edit the file (add/change tactics)

3. hol_state_at(line=18, col=1)
   → Auto-detects file change, re-parses, replays to new position

4. hol_check_proof(theorem="my_theorem")
   → Verifies proof completes, reports timing

5. holmake(workdir=".")
   → Final build verification
```

## Architecture

```
hol4_mcp/
├── hol_mcp_server.py    # MCP tool definitions, session registry, FastMCP app
├── hol_session.py       # HOL subprocess management (start/stop/send/interrupt)
├── hol_cursor.py        # File proof cursor (parsing, replay, checkpoints)
├── hol_file_parser.py   # Parse *Script.sml for theorems/definitions/resumes
├── sml_helpers/
│   ├── etq.sml          # Legacy goaltree mode helpers
│   └── tactic_prefix.sml # TacticParse-based tactic replay (used by cursor)
└── pi_extension/
    └── hol4-mcp.ts      # Pi extension (MCP client over stdio)
```

**Key internals:**

- **HOLSession** — Wraps an `hol --zero` subprocess. Null-byte framing for response detection. Process-group signals for clean interrupt/kill.
- **FileProofCursor** — Parses theorems from file, loads dependencies via `holdeptool.exe`, replays tactics using HOL's `TacticParse.sliceTacticBlock`, and manages PolyML `SaveState` checkpoints for fast state restoration (~1.4MB per theorem checkpoint vs ~132MB base).
- **Change detection** — SHA-256 content hashing. On file change, invalidates checkpoints/traces from the first changed line forward. Pre-theorem changes (imports, ancestors) trigger full session reinit.

## Development

```bash
# Install dev dependencies
uv pip install --python .venv/bin/python -e ".[dev]"

# Run tests
.venv/bin/python -m pytest tests/ -q

# Run server with debug logging
hol4-mcp serve -v
```

## License

MIT — see [LICENSE](LICENSE).
