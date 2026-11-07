# hol4-mcp

An [MCP](https://modelcontextprotocol.io/) server that gives LLM agents interactive access to the [HOL4](https://hol-theorem-prover.org/) theorem prover. Agents can start HOL sessions, navigate proofs, inspect goal states, and build theories — all through structured tool calls.

## Features

- **Proof cursor** — Navigate to any position in a proof file and see the goal state. The cursor tracks file edits, replays tactics incrementally, and uses PolyML checkpoints for fast state restoration.
- **Multi-theorem files** — Parse `*Script.sml` files to discover theorems, definitions, and resume blocks. Enter any theorem and step through its proof.
- **Holmake integration** — Build theories synchronously or detached, with dependency-overlap guards against concurrent MCP builds and failure diagnostics (build logs, error context).
- **Session management** — Named HOL sessions (one live session at a time by default) with idle timeout, automatic garbage collection, and SIGINT-based interrupt for runaway tactics.
- **Change detection** — Content hashing detects file edits automatically. No need to restart sessions after modifying proof files.
- **Pi extension** — Ships with a [pi](https://github.com/badlogic/pi-mono) extension that registers all tools dynamically.

## Requirements

- [HOL4](https://hol-theorem-prover.org/) `master`, built, with `HOLDIR` environment variable set (defaults to `~/HOL`). The server needs TacticParse's positioned combinators (`FOpenThen1`, `FOpenBy` and `FOpenSufficesBy` carrying spans); against an older HOL, session start fails with "the HOL at … is too old for hol4-mcp".
- Python ≥ 3.11
- [uv](https://github.com/astral-sh/uv) (recommended) or pip

### Interactive memory limit

HOL sessions default to a Poly/ML maximum heap of half the machine's RAM, at
least 8192 MB. To choose another, set `HOL4_MCP_MAXHEAP_MB=12288` in the server
environment or pass `env={"HOL4_MCP_MAXHEAP_MB": "12288"}` to `hol_start` or
`hol_setenv`. Values must be integers of at least 256 MB. Startup reports the
effective limit; changing the setting does not resize an already running
session (`hol_setenv` restarts it to apply). The environment belongs to the
session name: every later start of it uses it, automatic restarts included.
This option is independent of `holmake(heap_size=...)`.

### Time budgets

Each budget, in seconds, is read from the server environment at startup
(the dependency-load budget at each session init). Set them in the MCP launch
configuration's `env`; a value that is not a number is refused with an error
naming the variable.

| Variable | Default | Bounds |
|---|---|---|
| `HOL4_MCP_TACTIC_TIMEOUT` | 60 | one tactic during replay (alias `HOL_TACTIC_TIMEOUT`; `--tactic-timeout` overrides) |
| `HOL4_MCP_STATE_AT_TIMEOUT` | 300 | one `hol_state_at`/`hol_goals` navigation (alias `HOL_STATE_AT_TIMEOUT`; `--state-at-timeout` overrides) |
| `HOL4_MCP_MAX_STATE_AT_TIMEOUT` | 3600 | the largest per-call `timeout=` accepted |
| `HOL4_MCP_THEOREM_TIMEOUT` | 1200 | one earlier theorem's whole proof while loading the prefix |
| `HOL4_MCP_PREFIX_LOAD_TIMEOUT` | 3000 | loading the current file up to the target |
| `HOL4_MCP_DEP_LOAD_TIMEOUT` | 300 | one dependency `load` at session init |
| `HOL4_MCP_HOLMAKE_TIMEOUT` | 600 | a synchronous `holmake`, when `timeout=` is not given |
| `HOL4_MCP_MAX_HOLMAKE_TIMEOUT` | 1800 | the cap applied to `holmake`'s `timeout=` |
| `HOL4_MCP_DETACHED_DISCOVERY_TIMEOUT` | 1800 | dependency discovery before a detached build starts |

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

### Codex

This checkout is also a native Codex plugin. Its
`.codex-plugin/plugin.json` bundles three pieces:

- the `hol4` stdio MCP server, with an 1800-second tool timeout for long proof
  replays and builds;
- the `hol4-proving` skill under `skills/`;
- Codex-native lifecycle hooks from `hooks/hooks.json`.

Install this directory through a local Codex plugin marketplace, enable the
`hol4-mcp` plugin, then open `/hooks` and trust its reviewed hook definitions.
`hol4-mcp` must be on Codex's `PATH`; export `HOLDIR` when HOL is not at
`~/HOL`. Plugin hook state is kept under Codex's `PLUGIN_DATA` and does not use
the real `~/.claude` directory.

For an MCP-only setup without installing the plugin, add this to
`~/.codex/config.toml` (or a trusted project's `.codex/config.toml`):

```toml
[mcp_servers.hol4]
command = "hol4-mcp"
args = ["--transport", "stdio"]
env_vars = ["HOLDIR"]
startup_timeout_sec = 30
tool_timeout_sec = 1800
```

The MCP-only setup exposes the tools, but not the bundled proof skill or
lifecycle hooks. See `integrations/codex/README.md` for the adapter boundary.
For the local release bundle and installation commands, see
[`integrations/codex/README.md`](integrations/codex/README.md#installing-the-local-release).

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
| `hol_goals` | Goal count and structured goal slices at the cursor position, without a full goal dump |
| `hol_check_proof` | Check if a theorem's proof completes. Reports pass/fail, timing, and failure location. |

### Raw interaction and search

| Tool | Description |
|------|-------------|
| `hol_send` | Send raw SML to HOL for small probes (a term, a type, a one-tactic check). Not for driving a proof: develop in the file and navigate with `hol_state_at`. |
| `hol_search` | Search the theorem database by name and/or term pattern |
| `hol_interrupt` | Stop the call running on a session (a runaway tactic, a stuck load); that call returns `INTERRUPTED` |

### Build

| Tool | Description |
|------|-------------|
| `holmake` | Run `Holmake --qof` on a named target, with dependency-overlap guards against concurrent MCP builds and failure log extraction; `detach=True` for long builds |
| `hol_build_status` | State, log tail and cancellation of a detached `holmake` job, including one started by an earlier server process |
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

Recovery after a transient auto-cheated load is explicit:
`hol_check_proof(theorem="my_theorem", fresh=True)` discards the session's old
bindings, checkpoints and verdicts and replays the full prefix in a new HOL
process. Use it once the file proof is ready; it does not waive oracle checks.
Ordinary navigation and checks retain incremental replay and cached results.

Dependency freshness checks stat existing artifacts directly and group absent
load-path candidates by parent directory. Unchanged directories need one stat,
not one per absent candidate; new/shadowing artifacts are checked without a
timer delay. The opt-in `scripts/benchmark_dependency_freshness.py` measures
warm read/hash/freshness overhead on real scripts without running their proofs.

During long prefix work, `hol_sessions` reports the active dependency, preceding
theorem or current-file SML/translation span, elapsed time and command budget.
Status inspection does not replay HOL commands or reap busy sessions.

Failure evidence is written only on failures: complete submitted SML and
returned response, phase metadata when available, workdir, PID and heap limit.
The reported JSON path (also shown by `hol_sessions`) lives in a private
temporary directory holding the newest 20 per session; the directory is removed
when the server exits unless `HOL4_MCP_KEEP_EVIDENCE` is set. These files can
contain project source.
Replies are decoded/framed and normally ANSI-normalized, not a byte-level pipe
capture; interrupted requests retain the available partial response. Failed
diagnostic writes never change the proof result. Admission history is reported
separately from kernel oracle evidence; history alone is not a dependency list.

For an opaque filesystem/discovery failure, an explicit
`holmake(..., trace_discovery=True)` records Linux syscall/path evidence and
execution-context metadata under `/var/tmp/hol4-mcp-<uid>/discovery/` (the
newest five traces are kept; one traced run is the whole diagnostic). It
requires `strace` and tracing permission, adds overhead, and is off for
regular builds. Build coordination keeps everything else it needs — artifact
records, locks, detached-job logs and exit statuses — in the same per-user
directory, never in a project tree. A tracer
permission/setup failure is not reported as a proof-failure verdict. Missing
directories are not silently ignored or created, and a filesystem failure is
not retried. A build that fails with Poly/ML's out-of-store message is re-run
once (per job by Holmake in a parallel build, whole for `jobs=1`).

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
- **FileProofCursor** — Parses theorems from file, loads dependencies via `holdeptool.exe`, replays tactics using HOL's `TacticParse.sliceTacticBlock`, and rewinds past an edit to the state after an earlier theorem. After every theorem it records an in-memory point (HOL's `Context.snapshot`, the loaded-module set, and the prior bindings of the names the file binds next); a rewind restores one in milliseconds. The heap keeps the newest 256 points. A PolyML `SaveState` file is kept after every 16th point and after any span calling a library that keeps state in plain SML refs (CakeML's translator, `cv_trans`); a rewind across such a span, or across a module load, loads the nearest file instead. Files whose chain grows past the last anchor's size are saved as children of the base, and files nothing can need are deleted after each load.
- **Change detection** — SHA-256 content hashing. On file change, invalidates checkpoints/traces from the first changed line forward. Pre-theorem changes (imports, ancestors) trigger full session reinit.

## Agent guidance (`skills/`, `hooks/`)

The repo also carries the guidance an agent needs to *use* this server:

- `skills/hol4-proving/` — the shared HOL4 proof-interaction ruleset (`SKILL.md`)
  and its technique notes (`notes/`). Claude Code can expose it globally with
  `ln -s "$PWD/skills/hol4-proving" ~/.claude/skills/hol4-proving`; the Codex
  plugin bundles the same canonical directory directly.
- `hooks/h*.py` — the established Claude Code hooks and
  `hooks/install_hooks.py` wiring. See `hooks/README.md`.
- `hooks/hooks.json` and `integrations/codex/` — the additive Codex lifecycle
  wiring and payload adapter. The adapter reuses the policy scripts while
  isolating their state from Claude.

Editing either? `skills/hol4-proving/notes/reference_hol4_docs.md` defines which
layer owns which fact and the quality bar every entry must pass.

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
