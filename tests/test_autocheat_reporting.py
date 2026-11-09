"""Unit tests for auto-cheat reason classification and target-self-cheat
verdict (MCP Bug A).

These exercise pure module-level helpers, so they do NOT need a live HOL
session or the FastMCP tool wrappers — they validate the reporting logic in
isolation.
"""

from pathlib import Path

from hol4_mcp.hol_cursor import (
    _error_reason,
    _line_is_error_marker,
    FileProofCursor,
    PER_THEOREM_TIMEOUT,
)
from hol4_mcp.hol_mcp_server import (
    _auto_cheated_deps_lines,
    _target_self_cheated_reason,
    _target_self_cheated_lines,
)


# --- _line_is_error_marker -------------------------------------------------

def test_marker_false_on_goal_terms_mentioning_error():
    # The exact fragment that misreported a slow proof as failed.
    assert not _line_is_error_marker("| (SOME (Rerr (Rabort Rtype_error)),s1) => T")
    assert not _line_is_error_marker("res <> SOME (Rerr (Rabort Rtype_error)) ∧")
    assert not _line_is_error_marker("no_ReturnException case in evaluate")
    # A bare goal conclusion that happens to mention error constructors.
    assert not _line_is_error_marker("⊢ evaluate (c,s) = (SOME (Rerr e), s')")


def test_marker_true_on_real_errors():
    assert _line_is_error_marker("Exception- HOL_ERR {message = ...} raised")
    assert _line_is_error_marker("HOL_ERR something")
    assert _line_is_error_marker("uncaught exception raised exception at top level")
    assert _line_is_error_marker("TIMEOUT after 120s - sent interrupt.")
    assert _line_is_error_marker("parse error at 12:5: unexpected token")
    assert _line_is_error_marker("Fail mk_thm: not allowed")


# --- _error_reason ---------------------------------------------------------

def test_error_reason_timeout():
    out = "TIMEOUT after 120s - sent interrupt.\nInitial goal:\n| (SOME (Rerr ...),s1) => T"
    r = _error_reason(out)
    assert r.upper().startswith("TIMEOUT")
    # Must NOT have grabbed the goal fragment.
    assert "Rerr" not in r


def test_error_reason_does_not_return_goal_fragment():
    # A failing proof prints its goal (mentioning Rerr/Rtype_error) BEFORE the
    # exception. The reason must NOT be that goal line.
    out = (
        "Initial goal:\n"
        "| (SOME (Rerr (Rabort Rtype_error)),s1) => T\n"
        "...lots of goal text...\n"
        "Exception- HOL_ERR {origin_function = \"DECIDE\"} raised\n"
    )
    r = _error_reason(out)
    assert "HOL_ERR" in r
    assert "Rtype_error" not in r


def test_error_reason_generic_when_no_marker():
    # Output with no recognizable error marker and only goal-ish text must
    # fall back to a generic 'could not validate', never a goal fragment.
    out = "| (SOME (Rerr (Rabort Rtype_error)),s1) => T\nsome other goal line\n"
    r = _error_reason(out)
    assert "Rtype_error" not in r
    assert "could not validate" in r


def test_error_reason_real_exception():
    out = "Exception- Fail \"oops\" raised\n"
    r = _error_reason(out)
    assert "error:" in r and ("Fail" in r or "Exception" in r)


def test_error_reason_preserves_multiline_hol_exception():
    output = ('OK..\nException-\n   HOL_ERR\n'
              '     (at Tactical.Q_TAC:\n'
              '        at Tactic.STRIP_TAC: not a conjunction or implication)\n'
              '   raised\nval unrelated = "not part of the exception"\n')
    reason = _error_reason(output)
    assert "Tactic.STRIP_TAC" in reason
    assert "not a conjunction or implication" in reason
    assert "OK.." not in reason and "unrelated" not in reason
    assert "\n" not in reason


def test_error_reason_multiline_is_bounded():
    output = "Exception-\n HOL_ERR\n" + "details " * 1000
    assert len(_error_reason(output, limit=80)) <= len("error: ") + 80


# --- budget ----------------------------------------------------------------

def test_budget_raised():
    assert PER_THEOREM_TIMEOUT >= 120


# --- _auto_cheated_deps_lines / target self-cheat --------------------------

class _FakeCursor:
    def __init__(self, failed):
        self._failed_proofs = failed


def test_deps_excludes_target():
    cur = _FakeCursor({"thmA": "timeout >120s loading whole proof",
                       "thmB": "error: HOL_ERR ..."})
    lines = _auto_cheated_deps_lines(cur, target_name="thmA")
    rendered = "\n".join(lines)
    assert "thmA" not in rendered          # target excluded
    assert "thmB" in rendered              # admission history still named
    assert "not a dependency list" in rendered


def test_deps_empty_when_only_target_failed():
    cur = _FakeCursor({"thmA": "timeout >120s loading whole proof"})
    # The only failed proof IS the target — there are no real deps to name.
    assert _auto_cheated_deps_lines(cur, target_name="thmA") == []


def test_target_self_cheated_reason():
    cur = _FakeCursor({"thmA": "timeout >120s loading whole proof"})
    assert _target_self_cheated_reason(cur, "thmA") is not None
    assert _target_self_cheated_reason(cur, "thmB") is None
    assert _target_self_cheated_reason(cur, None) is None


def test_self_cheat_lines_timeout_never_mentions_holmake():
    lines = _target_self_cheated_lines("timeout >120s loading whole proof")
    blob = "\n".join(lines).lower()
    assert "not validated" in blob
    assert "suspend" in blob               # in-workflow remedy
    assert "holmake" not in blob           # MUST NOT point at the file gate


def test_self_cheat_lines_error_never_mentions_holmake():
    lines = _target_self_cheated_lines("error: HOL_ERR ...")
    blob = "\n".join(lines).lower()
    assert "not validated" in blob
    assert "holmake" not in blob


# --- stale auto-cheat verdict invalidation on file change ------------------
# Regression for the MCP bug where _failed_proofs (the auto-cheat verdict
# cache) survived an ordinary body edit: a fixed Resume body kept reporting
# its first-load failure, and a sub-dispatcher's children kept showing
# "SKIPPED", until a full session restart. _invalidate_from_line now drops the
# verdict for the edited theorem (and anything after it) and for vanished names.

_TWO_THMS_V1 = (
    "Theorem aaa:\n  T\nProof\n  rw[]\nQED\n\n"
    "Theorem bbb:\n  T\nProof\n  rw[]\nQED\n"
)
# Same file, only bbb's tactic edited (rw[] -> simp[]); aaa byte-identical.
_TWO_THMS_V2 = (
    "Theorem aaa:\n  T\nProof\n  rw[]\nQED\n\n"
    "Theorem bbb:\n  T\nProof\n  simp[]\nQED\n"
)


def test_failed_proofs_dropped_for_edited_and_vanished_theorems(tmp_path):
    f: Path = tmp_path / "invScript.sml"
    f.write_text(_TWO_THMS_V1)
    cur = FileProofCursor(f, session=None)
    assert cur._reparse_if_changed() is True   # initial parse populates theorems

    # Simulate a prior load that auto-cheated all of these. "ghost" no longer
    # exists in the file (renamed/deleted between loads).
    cur._failed_proofs = {
        "aaa": "error: HOL_ERR ...",
        "bbb": "error: HOL_ERR ...",
        "ghost": "label not found at load — SKIPPED, never ran",
    }
    cur._loaded_to_line = 100

    # Edit ONLY bbb's proof body.
    f.write_text(_TWO_THMS_V2)
    assert cur._reparse_if_changed() is True

    # bbb changed -> its stale verdict must be dropped.
    assert "bbb" not in cur._failed_proofs
    # ghost is gone from the file -> its stale verdict must be dropped.
    assert "ghost" not in cur._failed_proofs
    # aaa is byte-identical and BEFORE the change -> its verdict is untouched
    # (we only re-derive verdicts for theorems that could have changed).
    assert "aaa" in cur._failed_proofs


def test_failed_proofs_fully_cleared_on_pre_theorem_edit(tmp_path):
    # An edit before the first theorem forces a session reinit, which already
    # clears _failed_proofs wholesale; guard that path stays correct too.
    f: Path = tmp_path / "invScript.sml"
    f.write_text(_TWO_THMS_V1)
    cur = FileProofCursor(f, session=None)
    assert cur._reparse_if_changed() is True
    cur._failed_proofs = {"aaa": "error: ...", "bbb": "error: ..."}
    cur._loaded_to_line = 100

    # Insert a comment line at the very top (before any theorem).
    f.write_text("(* header *)\n" + _TWO_THMS_V1)
    assert cur._reparse_if_changed() is True
    assert cur._failed_proofs == {}
