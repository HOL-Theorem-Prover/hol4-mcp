# Codex integration

This directory is an adapter layer; the MCP server itself is client-neutral.

## Installing the local release

The `0.1.0+codex.20261003` release is a local snapshot, not an upstream release.
Use the supplied wheel and plugin bundle together. Python 3.11 or newer and a
built HOL4 installation are required; set `HOLDIR` if HOL is outside `~/HOL`.

Extract the plugin bundle into `~/hol4-mcp` (or another permanent directory).
From that directory, install the supplied wheel into a dedicated environment:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install dist/hol4_mcp-0.1.0+codex.20261003-py3-none-any.whl
export PATH="$PWD/.venv/bin:$PATH"
```

Start Codex from a shell with this `PATH` and your `HOLDIR`. Register the bundled
local marketplace and install its plugin:

```bash
codex plugin marketplace add "$PWD"
codex plugin add hol4-mcp@hol4-local
```

Restart Codex, enable/trust the bundled hooks through `/hooks`, and ask it to
start a HOL session and evaluate `1 + 1;`. Keep the extracted directory: the
marketplace points to it. The marketplace layout follows the
[official OpenAI plugin documentation](https://developers.openai.com/plugins/build/plugins).
For server tools alone, use the MCP configuration in the root README instead.

Build dependency coordination and recovery behavior are described by the
`holmake` tool. This release includes the dependency-overlap guards.

## Boundary

| Concern | Codex implementation | Shared/Claude implementation |
|---|---|---|
| Package discovery | `.codex-plugin/plugin.json` | unchanged |
| MCP launch | inline `mcpServers.hol4` manifest entry | server process and tools |
| Proof workflow | bundled `skills/hol4-proving/` | canonical skill content |
| Lifecycle registration | `hooks/hooks.json` | `h*.py` policy scripts |
| Edit payload | temporary `apply_patch` preview | Edit-style before/after checks |
| User consent history | stable `UserPromptSubmit.prompt` capture | transcript-reading helpers |
| Writable state | `PLUGIN_DATA/runtime-home` | path conventions only |

- `hook_adapter.py` translates Codex `apply_patch` events into before/after
  edit payloads understood by the established HOL4 policy scripts.
- `prompt_capture.py` records the stable `UserPromptSubmit.prompt` field so
  consent-aware policies do not depend on Codex's intentionally unstable
  transcript format.
- `session_context.py` asks Codex to load the bundled `hol4-proving` skill when
  a session starts in a HOL4 project.

Codex supplies `PLUGIN_ROOT` and `PLUGIN_DATA`. The adapter runs existing hook
scripts with `HOME=$PLUGIN_DATA/runtime-home`; consequently their legacy
`~/.claude/hook-state` paths resolve inside plugin-owned Codex data. Nothing in
this integration reads or writes the user's actual Claude configuration or
hook state.

`hooks/hooks.json` is the native Codex lifecycle configuration. H14 and H33 are
omitted because they are general, user-specific Git/shell policy rather than
HOL4 policy. H22
is replaced by the Codex-native session hook because its other responsibility
is auditing Claude's `settings.json` wiring.

## Event flow

1. `UserPromptSubmit` records bounded prompt history under `PLUGIN_DATA`.
2. `PreToolUse` passes Bash and HOL4 MCP arguments through unchanged. For
   `apply_patch`, the adapter materializes only referenced files in a temporary
   directory and derives an Edit payload without touching the working tree.
3. Policies matching their declared `HOOK_EVENT` and `HOOK_MATCHER` run
   sequentially with an isolated HOME. Exit code 2 and stderr remain a hard
   block; advisory JSON is combined into one
   Codex-compatible response.
4. `PostToolUse` forwards `tool_response`, allowing the existing replay,
   failure, build, and proof-sweep advisories to work unchanged.

The adapter fails open on malformed or unsupported hook input, matching the
existing suite's policy. When possible, it surfaces an explicit Codex warning
instead of silently losing coverage.
