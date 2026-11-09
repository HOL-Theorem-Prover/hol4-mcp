"""Failure-only request/response evidence; no filesystem work on success."""
import atexit
import json
import os
from pathlib import Path
import shutil
import tempfile

KEEP = 20                      # newest files retained per session
_directories: list[Path] = []  # every directory created by this process


def _discard_all() -> None:
    if os.environ.get("HOL4_MCP_KEEP_EVIDENCE"):
        return
    for directory in _directories:
        shutil.rmtree(directory, ignore_errors=True)


atexit.register(_discard_all)


class FailureEvidence:
    def __init__(self):
        self.directory: Path | None = None
        self.sequence = 0
        self.latest: dict | None = None

    def record(self, command: str, response: str, kind: str, **metadata) -> None:
        self.sequence += 1
        entry = {"id": self.sequence, "kind": kind, **metadata}
        try:
            if self.directory is None:
                # Private, unpredictable directory; logs can contain project
                # source. Removed at server exit unless HOL4_MCP_KEEP_EVIDENCE.
                self.directory = Path(tempfile.mkdtemp(prefix="hol4-mcp-evidence-"))
                _directories.append(self.directory)
            path = self.directory / f"failure-{self.sequence}.json"
            with path.open("x", encoding="utf-8") as stream:
                json.dump({**entry, "command": command, "response": response},
                          stream, ensure_ascii=False)
            entry["path"] = str(path)
        except (OSError, ValueError, TypeError) as exc:
            # Diagnostics must never turn a failed log write into a different
            # proof result or hide the original exception.
            entry["log_error"] = str(exc)
        self.latest = entry
        if self.directory is not None:
            try:
                (self.directory / f"failure-{self.sequence - KEEP}.json").unlink(missing_ok=True)
            except OSError:
                pass
