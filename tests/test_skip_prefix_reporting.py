"""Unit tests for the prefix-skip navigation NOTICE (pure helper).

Exercises the module-level _prefix_skip_lines formatter in isolation — no live
HOL session or FastMCP tool wrapper needed.
"""

from hol4_mcp.hol_mcp_server import _prefix_skip_lines


class _FakeCursor:
    def __init__(self, skip_prefix=False, skipped=None):
        self._skip_prefix = skip_prefix
        self._skipped_thms = set(skipped or [])


def test_no_lines_when_skip_off():
    assert _prefix_skip_lines(_FakeCursor(skip_prefix=False)) == []


def test_no_lines_when_attr_absent():
    # A cursor that predates the feature (no attrs) must not crash or emit.
    class _Bare:
        pass
    assert _prefix_skip_lines(_Bare()) == []


def test_lines_when_skip_on():
    cur = _FakeCursor(skip_prefix=True, skipped={"a", "b", "c"})
    blob = "\n".join(_prefix_skip_lines(cur)).lower()
    assert "prefix-skip mode on" in blob
    assert "3" in blob                      # the count
    assert "cheat" in blob                  # explains the mechanism
    assert "not a verification" in blob     # honesty: not a real check


def test_count_zero_still_reports_mode():
    # Mode on but nothing cheated yet (e.g. target is the first theorem):
    # still announce the mode so the reader knows skip is active.
    cur = _FakeCursor(skip_prefix=True, skipped=set())
    blob = "\n".join(_prefix_skip_lines(cur)).lower()
    assert "prefix-skip mode on" in blob
    assert "0" in blob


def test_notice_never_points_at_holmake_as_required_step():
    # Consistent with the other verdicts: the notice may MENTION holmake as an
    # alternative real check, but must center the in-tool remedy (re-run without
    # skip_prefix). Assert the in-tool remedy is present.
    cur = _FakeCursor(skip_prefix=True, skipped={"x"})
    blob = "\n".join(_prefix_skip_lines(cur)).lower()
    assert "skip_prefix" in blob
