"""Small shared helpers for Codex plugin hook state.

All writable state is rooted in ``PLUGIN_DATA`` when Codex launches the plugin.
The fallback is useful for direct testing and manual hook wiring; it deliberately
uses Codex storage and never the user's ``~/.claude`` directory.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from typing import Any


def plugin_root() -> Path:
    configured = os.environ.get("PLUGIN_ROOT")
    if configured:
        return Path(configured).expanduser().resolve()
    return Path(__file__).resolve().parents[2]


def data_root() -> Path:
    configured = os.environ.get("PLUGIN_DATA")
    if configured:
        root = Path(configured).expanduser()
    else:
        codex_home = Path(os.environ.get("CODEX_HOME", Path.home() / ".codex"))
        root = codex_home / "hol4-mcp"
    root.mkdir(parents=True, exist_ok=True)
    return root.resolve()


def session_key(payload: dict[str, Any]) -> str:
    raw = str(payload.get("session_id") or "nosession")
    return hashlib.sha256(raw.encode("utf-8", errors="replace")).hexdigest()[:24]


def prompt_path(payload: dict[str, Any]) -> Path:
    directory = data_root() / "prompts"
    directory.mkdir(parents=True, exist_ok=True)
    return directory / f"{session_key(payload)}.json"


def load_prompts(payload: dict[str, Any]) -> list[str]:
    try:
        value = json.loads(prompt_path(payload).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    if not isinstance(value, list):
        return []
    return [item for item in value if isinstance(item, str)]


def save_prompts(payload: dict[str, Any], prompts: list[str]) -> None:
    path = prompt_path(payload)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(prompts, ensure_ascii=False), encoding="utf-8")
    os.replace(temporary, path)


def synthetic_transcript(payload: dict[str, Any]) -> Path:
    """Create the stable, minimal transcript shape expected by legacy hooks."""
    directory = data_root() / "transcripts"
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{session_key(payload)}.jsonl"
    lines = [
        json.dumps({"type": "user", "message": {"role": "user", "content": prompt}})
        for prompt in load_prompts(payload)
    ]
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
    os.replace(temporary, path)
    return path
