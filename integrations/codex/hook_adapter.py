#!/usr/bin/env python3
"""Adapt Codex hook events to the repository's established hook contract.

Codex reports file edits as one ``apply_patch`` command, whereas the existing
policy scripts consume Claude-style Edit/Write payloads. For PreToolUse edits,
this adapter applies the patch only in a temporary mirror, derives each
before/after pair, and presents it as an Edit event. Other tools pass through.

The child hook process receives a private HOME rooted under PLUGIN_DATA. This
keeps every existing ``~/.claude/hook-state`` reference inside Codex's plugin
data directory without changing the Claude implementation or its state.
"""

from __future__ import annotations

from dataclasses import dataclass
import ast
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any

from runtime import data_root, plugin_root, synthetic_transcript


PATCH_HEADER_RE = re.compile(r"^\*\*\* (Update|Add|Delete) File: (.+)$", re.MULTILINE)
MOVE_RE = re.compile(r"^\*\*\* Move to: (.+)$", re.MULTILINE)
PATH_HEADER_RE = re.compile(
    r"^(\*\*\* (?:(?:Update|Add|Delete) File|Move to): )(.+)$", re.MULTILINE
)


@dataclass(frozen=True)
class PatchRecord:
    operation: str
    source: str
    target: str


@dataclass(frozen=True)
class EditDelta:
    path: Path
    before: str
    after: str


def _safe_relative(raw: str) -> str:
    path = PurePosixPath(raw.strip())
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise ValueError(f"unsupported patch path: {raw!r}")
    return path.as_posix()


def _records(command: str) -> list[PatchRecord]:
    matches = list(PATCH_HEADER_RE.finditer(command))
    records: list[PatchRecord] = []
    for index, match in enumerate(matches):
        operation = match.group(1)
        source = _safe_relative(match.group(2))
        end = matches[index + 1].start() if index + 1 < len(matches) else len(command)
        body = command[match.end():end]
        move = MOVE_RE.search(body) if operation == "Update" else None
        target = _safe_relative(move.group(1)) if move else source
        records.append(PatchRecord(operation, source, target))
    return records


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _find_sequence(lines: list[str], wanted: list[str], start: int,
                   eof: bool = False) -> int:
    if not wanted:
        return len(lines)
    if eof and len(lines) - len(wanted) >= start:
        try:
            return _find_sequence(lines, wanted, len(lines) - len(wanted))
        except ValueError:
            pass
    for normalize in (lambda line: line, str.rstrip, str.strip):
        expected = [normalize(line) for line in wanted]
        for begin in range(start, len(lines) - len(wanted) + 1):
            if [normalize(line) for line in lines[begin:begin + len(wanted)]] == expected:
                return begin
    raise ValueError("patch context does not match the current file")


def _apply_hunks(before: str, body: str) -> str:
    """Small fallback for environments that do not expose the Codex patch CLI."""
    body = MOVE_RE.sub("", body)
    chunks = re.split(r"^(@@[^\n]*)$", body, flags=re.MULTILINE)
    lines = before.splitlines()
    cursor = 0
    anchor = None
    for chunk in chunks:
        if chunk.startswith("@@"):
            anchor = chunk[3:] if chunk.startswith("@@ ") else None
            continue
        patch_lines = [line for line in chunk.splitlines()
                       if line != "*** End of File" and line[:1] in {" ", "+", "-"}]
        if not patch_lines:
            continue
        if anchor:
            cursor = _find_sequence(lines, [anchor], cursor) + 1
            anchor = None
        old = [line[1:] for line in patch_lines if line.startswith((" ", "-"))]
        new = [line[1:] for line in patch_lines if line.startswith((" ", "+"))]
        begin = _find_sequence(lines, old, cursor, "*** End of File" in chunk.splitlines())
        lines[begin:begin + len(old)] = new
        cursor = begin + len(new)
    return "\n".join(lines) + ("\n" if lines else "")


def _fallback_apply(command: str, mirror: Path, records: list[PatchRecord]) -> None:
    """Apply the supported patch operations only inside the temporary mirror."""
    matches = list(PATCH_HEADER_RE.finditer(command))
    for index, (match, record) in enumerate(zip(matches, records)):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(command)
        body = command[match.end():end]
        source = mirror / record.source
        if record.operation == "Delete":
            source.unlink()
            continue
        elif record.operation == "Add":
            added = [line[1:] for line in body.splitlines() if line.startswith("+")]
            after = "\n".join(added) + ("\n" if added else "")
        else:
            after = _apply_hunks(source.read_text(encoding="utf-8"), body)
        (mirror / record.target).write_text(after, encoding="utf-8")
        if record.target != record.source:
            source.unlink()


def preview_patch(command: str, cwd: Path) -> list[EditDelta]:
    # Map EVERY path (including absolute paths, ../ paths and move targets)
    # to a private flat filename before invoking any patch implementation.
    # Neither implementation can then follow a header out of the mirror.
    aliases: dict[Path, str] = {}

    def remap(match: re.Match) -> str:
        path = Path(os.path.abspath(cwd / match.group(2)))
        alias = aliases.setdefault(path, f"file-{len(aliases)}")
        return match.group(1) + alias

    command = PATH_HEADER_RE.sub(remap, command)
    records = _records(command)
    if not records:
        return []
    executable = shutil.which("apply_patch")
    with tempfile.TemporaryDirectory(prefix="hol4-mcp-codex-patch-") as temporary:
        mirror = Path(temporary)
        before = {}
        for path, alias in aliases.items():
            if path.exists():
                (mirror / alias).write_bytes(path.read_bytes())
            before[path] = _read(mirror / alias)
        if executable is None:
            _fallback_apply(command, mirror, records)
        else:
            completed = subprocess.run(
                [executable], input=command, text=True, cwd=mirror,
                capture_output=True, timeout=30, check=False,
            )
            if completed.returncode != 0:
                raise ValueError(completed.stderr.strip() or completed.stdout.strip()
                                 or "unable to preview patch")
        return [
            EditDelta(path, before[path], _read(mirror / alias))
            for path, alias in aliases.items()
        ]


def _legacy_payload(payload: dict[str, Any], delta: EditDelta) -> dict[str, Any]:
    adapted = dict(payload)
    adapted["tool_name"] = "Edit"
    adapted["tool_input"] = {
        "file_path": str(delta.path),
        "old_string": delta.before,
        "new_string": delta.after,
        "replace_all": False,
    }
    return adapted


def _run(script_name: str, payload: dict[str, Any]) -> subprocess.CompletedProcess[str]:
    if Path(script_name).name != script_name or not re.fullmatch(r"h\d+_[A-Za-z0-9_]+\.py", script_name):
        raise ValueError(f"invalid hook script name: {script_name!r}")
    script = plugin_root() / "hooks" / script_name
    if not script.is_file():
        raise ValueError(f"hook script not found: {script_name}")
    # Inspect literal registration metadata without importing policy modules:
    # imports could write state or depend on the child's isolated HOME.
    metadata = {}
    for node in ast.parse(script.read_text(encoding="utf-8")).body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in {"HOOK_EVENT", "HOOK_MATCHER"}:
                    metadata[target.id] = ast.literal_eval(node.value)
    if not {"HOOK_EVENT", "HOOK_MATCHER"} <= metadata.keys():
        raise ValueError(f"hook registration metadata missing: {script_name}")
    matcher = metadata["HOOK_MATCHER"]
    if (metadata["HOOK_EVENT"] != (payload.get("hook_event_name") or "PreToolUse")
            or (matcher is not None and not re.fullmatch(matcher, payload.get("tool_name", "")))):
        return subprocess.CompletedProcess([sys.executable, str(script)], 0, "", "")
    runtime_home = data_root() / "runtime-home"
    runtime_home.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment["HOME"] = str(runtime_home)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    return subprocess.run(
        [sys.executable, str(script)], input=json.dumps(payload), text=True,
        capture_output=True, env=environment, timeout=60, check=False,
    )


def _messages(stdout: str) -> tuple[list[str], list[str]]:
    contexts: list[str] = []
    system_messages: list[str] = []
    for line in stdout.splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(value, dict):
            continue
        specific = value.get("hookSpecificOutput")
        if isinstance(specific, dict) and isinstance(specific.get("additionalContext"), str):
            contexts.append(specific["additionalContext"])
        if isinstance(value.get("systemMessage"), str):
            system_messages.append(value["systemMessage"])
    return contexts, system_messages


def _emit(event: str, contexts: list[str], system_messages: list[str]) -> None:
    contexts = list(dict.fromkeys(message for message in contexts if message))
    system_messages = list(dict.fromkeys(message for message in system_messages if message))
    output: dict[str, Any] = {}
    if contexts:
        output["hookSpecificOutput"] = {
            "hookEventName": event,
            "additionalContext": "\n\n".join(contexts),
        }
    if system_messages:
        output["systemMessage"] = "\n\n".join(system_messages)
    if output:
        print(json.dumps(output))


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0

    event = str(payload.get("hook_event_name") or "PreToolUse")
    try:
        payload["transcript_path"] = str(synthetic_transcript(payload))
    except Exception as error:
        # Keep the tool guard useful even if prompt-history persistence is
        # temporarily unavailable. Consent-aware children will fail open.
        payload["transcript_path"] = None
        transcript_warning = f"hol4-mcp Codex prompt history is unavailable: {error}"
    else:
        transcript_warning = ""
    invocations: list[dict[str, Any]]
    try:
        if payload.get("tool_name") == "apply_patch":
            command = (payload.get("tool_input") or {}).get("command", "")
            cwd = Path(payload.get("cwd") or os.getcwd()).resolve()
            invocations = [_legacy_payload(payload, delta)
                           for delta in preview_patch(command, cwd)]
        else:
            invocations = [payload]
    except Exception as error:
        _emit(event, [], [f"hol4-mcp Codex hook adapter could not inspect this edit: {error}"])
        return 0

    contexts: list[str] = []
    system_messages: list[str] = [transcript_warning] if transcript_warning else []
    blocks: list[str] = []
    for invocation in invocations:
        for script_name in sys.argv[1:]:
            try:
                completed = _run(script_name, invocation)
            except Exception as error:
                system_messages.append(f"hol4-mcp Codex hook {script_name} failed open: {error}")
                continue
            child_contexts, child_system = _messages(completed.stdout)
            contexts.extend(child_contexts)
            system_messages.extend(child_system)
            if completed.returncode == 2:
                reason = completed.stderr.strip()
                blocks.append(reason or f"{script_name} blocked the tool call")
            elif completed.returncode != 0:
                system_messages.append(
                    f"hol4-mcp Codex hook {script_name} exited {completed.returncode} and failed open."
                )

    if blocks:
        print("\n\n".join(dict.fromkeys(blocks)), file=sys.stderr)
        return 2
    _emit(event, contexts, system_messages)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
