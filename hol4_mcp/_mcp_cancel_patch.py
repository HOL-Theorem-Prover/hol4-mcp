"""Spec-compliant cancellation patch for the mcp Python SDK.

The vendored RequestResponder.cancel() in mcp/shared/session.py sends a
JSON-RPC error response ("Request cancelled", code=0) for the cancelled
request id. The MCP spec says receivers SHOULD NOT respond to a cancelled
request. Claude Code's stdio MCP client follows the spec, retires the id
on receipt of notifications/cancelled, and treats the late error reply as
a stray response — closing the transport with
"Received a response for an unknown message ID: ... Request cancelled".

This module overrides RequestResponder.cancel to skip _send_response,
matching the behaviour proposed in upstream PRs #2481 and #2493 (still
open as of mcp 1.25.0). Once one of those merges, delete this file and
its import from hol_mcp_server.py.
"""

from __future__ import annotations

import sys


_APPLIED_FLAG = "_hol4_mcp_cancel_patched"


def apply() -> None:
    """Override RequestResponder.cancel in-place. Idempotent."""
    try:
        from mcp.shared.session import RequestResponder
    except ImportError:
        return

    if getattr(RequestResponder, _APPLIED_FLAG, False):
        return

    async def cancel(self) -> None:
        if not self._entered:
            raise RuntimeError("RequestResponder must be used as a context manager")
        if not self._cancel_scope:
            raise RuntimeError("No active cancel scope")
        self._cancel_scope.cancel()
        self._completed = True

    RequestResponder.cancel = cancel
    setattr(RequestResponder, _APPLIED_FLAG, True)
    print(
        "hol4-mcp: applied RequestResponder.cancel patch "
        "(suppress JSON-RPC reply on cancelled request)",
        file=sys.stderr,
    )


apply()
