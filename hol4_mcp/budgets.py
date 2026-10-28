"""Time budgets, in seconds, each settable by an environment variable.

Every budget reads `HOL4_MCP_<NAME>`. `HOL_TACTIC_TIMEOUT` and
`HOL_STATE_AT_TIMEOUT` are accepted as aliases of the tactic and state_at
budgets; the `HOL4_MCP_` name wins when both are set.
"""

import math
import os


def env_seconds(name: str, default: float, alias: str | None = None) -> float:
    """The budget in `name` (else `alias`), or `default` when neither is set."""
    for var in (name, alias):
        raw = os.environ.get(var) if var else None
        if raw is None:
            continue
        try:
            value = float(raw)
        except ValueError:
            value = math.nan
        if not math.isfinite(value):
            raise ValueError(f"{var} must be a number of seconds, got {raw!r}")
        return value
    return default


# Max seconds per tactic during proof replay; the CLI's --tactic-timeout
# overrides it.
TACTIC_TIMEOUT = env_seconds("HOL4_MCP_TACTIC_TIMEOUT", 60.0, alias="HOL_TACTIC_TIMEOUT")

# Overall wall-clock budget for a single state_at navigation; the CLI's
# --state-at-timeout overrides it. The per-tactic timeout bounds each tactic,
# but a large prefix replay or a long \\-chain can still sum to many minutes;
# this caps the TOTAL so state_at can never hang unbounded. Generous by default
# so a legitimate large-prefix replay completes; raise per-call with the tool's
# timeout= argument when a prefix is genuinely huge.
STATE_AT_TIMEOUT = env_seconds("HOL4_MCP_STATE_AT_TIMEOUT", 300.0, alias="HOL_STATE_AT_TIMEOUT")

# Largest per-call timeout= accepted. Anything above it is a unit mistake
# (milliseconds passed as seconds), not a budget.
MAX_STATE_AT_TIMEOUT = env_seconds("HOL4_MCP_MAX_STATE_AT_TIMEOUT", 3600.0)

# Per-theorem whole-proof replay budget. Legitimately-slow proofs (e.g. large
# induction bodies ~80-100s) must validate per-theorem rather than being
# silently auto-cheated, so this is well above the tactic budget.
PER_THEOREM_TIMEOUT = env_seconds("HOL4_MCP_THEOREM_TIMEOUT", 1200.0)

# Budget for loading the current file's content before the target theorem.
PREFIX_LOAD_TIMEOUT = env_seconds("HOL4_MCP_PREFIX_LOAD_TIMEOUT", 3000.0)


DEFAULT_DEP_LOAD_TIMEOUT = 300.0


def dep_load_timeout() -> float:
    """Budget for one dependency `load` at session init, read at each init."""
    return env_seconds("HOL4_MCP_DEP_LOAD_TIMEOUT", DEFAULT_DEP_LOAD_TIMEOUT)


# holmake: the default synchronous wait, and the largest one accepted.
HOLMAKE_TIMEOUT = int(env_seconds("HOL4_MCP_HOLMAKE_TIMEOUT", 600))
MAX_HOLMAKE_TIMEOUT = int(env_seconds("HOL4_MCP_MAX_HOLMAKE_TIMEOUT", 1800))

# Dependency discovery before a detached build starts.
DETACHED_DISCOVERY_TIMEOUT = int(env_seconds("HOL4_MCP_DETACHED_DISCOVERY_TIMEOUT", 1800))
