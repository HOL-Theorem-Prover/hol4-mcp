"""H31: `skip_prefix: true` on hol_state_at/hol_goals needs the user's
literal `skip prefix ok` (RULE K); false or absent passes."""
import pytest


HOOK = "h31_skip_prefix_consent.py"


@pytest.mark.parametrize("tool", ["mcp__hol4__hol_state_at", "mcp__hol4__hol_goals"])
def test_skip_prefix_without_consent_is_blocked(run_hook, tool):
    code, err, _ = run_hook(HOOK, tool, {"line": 10, "skip_prefix": True},
                            user_msg="keep going")
    assert code == 2, err
    assert "H31" in err and "RULE K" in err


def test_skip_prefix_with_consent_passes(run_hook):
    code, _, _ = run_hook(HOOK, "mcp__hol4__hol_state_at", {"line": 10, "skip_prefix": True},
                          user_msg="fine, skip prefix ok for this file")
    assert code == 0


def test_skip_prefix_false_or_absent_passes(run_hook):
    code, _, _ = run_hook(HOOK, "mcp__hol4__hol_state_at", {"line": 10, "skip_prefix": False})
    assert code == 0
    code, _, _ = run_hook(HOOK, "mcp__hol4__hol_state_at", {"line": 10})
    assert code == 0
