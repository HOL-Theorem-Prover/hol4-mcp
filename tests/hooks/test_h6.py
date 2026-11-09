"""H6 (failure reminder + symptom hint) is keyed on repeats: the first
failure on a theorem gets the symptom hint alone, a second consecutive
failure on the same theorem gets the RULE C reminder, and a failure on a
different theorem starts over."""
import json

import pytest


HOOK = "h6_check_proof_failure.py"
SESSION = "h6-session"


def failed(theorem, tactic="simp []"):
    return (f"Theorem: {theorem}\nLines: 5-9\n\nStatus: FAILED at step 1/2 (120ms)\n\n"
            f"=== Failing tactic ===\n{tactic}\n\nRemaining: 1 goal\n")


def check(run_hook, output):
    code, _, out = run_hook(HOOK, "mcp__hol4__hol_check_proof", {"theorem": "x"},
                            event="PostToolUse", tool_response=output, session_id=SESSION)
    assert code == 0
    return json.loads(out)["hookSpecificOutput"]["additionalContext"] if out.strip() else ""


def test_first_failure_gets_hint_only(run_hook):
    ctx = check(run_hook, failed("foo"))
    assert "H6" in ctx and "`simp` left goals" in ctx, ctx
    assert "RULE C" not in ctx, ctx


def test_second_consecutive_failure_gets_rule_c(run_hook):
    check(run_hook, failed("foo"))
    ctx = check(run_hook, failed("foo"))
    assert "RULE C" in ctx, ctx


def test_other_theorem_resets(run_hook):
    check(run_hook, failed("foo"))
    check(run_hook, failed("foo"))
    ctx = check(run_hook, failed("bar"))
    assert "RULE C" not in ctx, ctx


def test_first_failure_without_matching_symptom_is_silent(run_hook):
    ctx = check(run_hook, failed("foo", tactic="metis_tac []"))
    assert ctx == "", ctx


def test_success_is_silent(run_hook):
    ctx = check(run_hook, "Theorem: foo\nLines: 5-9\n\nStatus: OK (50ms, 2 steps)\n")
    assert ctx == ""


def test_current_file_prefix_failure_does_not_trigger_proof_restructuring(run_hook):
    output = ("Theorem: foo\nTIMEOUT: state_at exceeded its overall 300s budget. "
              "Active item: top-level SML/translation lines 2-900. "
              "The target tactics have not run.")
    for _ in range(3):
        assert check(run_hook, output) == ""
    # An actual target failure after setup still starts at its first failure.
    assert "RULE C" not in check(run_hook, failed("foo"))



INSIDE = ("Theorem: foo\nLine 9 col 3, Proof position\n\n=== Goal (1 of 2) ===\n  P x\n\n"
          "NOTE: target line 10 is INSIDE step 2 (lumped/parenthesized chain, lines 9-11); "
          "the state shown is this step's ENTRY at line 9, not the state at line 10. "
          "To navigate inside, split the arm with `>- suspend` into a Resume body.\n")
BUDGET = ("ERROR: TIMEOUT: state_at exceeded its overall 8s budget and was aborted (HOL interrupted; "
          "session recovered). Spent: prefix=1.2s (dependency load + earlier theorems), target=6.8s "
          "(this theorem's own tactics). The budget ran out in YOUR tactics: ...\n")
LABEL = ("Theorem: foo\nPROOF BROKEN at line 30 col 3\nERROR: Tactic failed at step 0\n\n"
         "=== Failing tactic ===\nResume body\n\nAncestor chain for suspension 'Arm': first broken ancestor: foo (dispatcher)\n"
         "No such label: Arm\n")
GREEN_NAV = "Theorem: foo\nLine 9 col 3, Proof position\n\n=== Goal (1 of 1) ===\n  P x\n\n[Timing: total=10ms, replay=0ms, startup=0ms, method=reused]\n"


def nav(run_hook, output):
    code, _, out = run_hook(HOOK, "mcp__hol4__hol_state_at", {"line": 10},
                            event="PostToolUse", tool_response=output, session_id=SESSION)
    assert code == 0
    return json.loads(out)["hookSpecificOutput"]["additionalContext"] if out.strip() else ""


def test_inside_step_row_gives_sub_suspend_recipe(run_hook):
    ctx = nav(run_hook, INSIDE)
    assert "H6" in ctx and "suspend" in ctx and "Resume foo[" in ctx and "QED" in ctx, ctx
    assert "RULE C" not in ctx, ctx


def test_budget_timeout_row_reads_prefix_and_target(run_hook):
    ctx = nav(run_hook, BUDGET)
    assert "H6" in ctx and "prefix=" in ctx and "target=" in ctx, ctx
    assert "never ran" in ctx or "your tactic" in ctx.lower(), ctx


def test_no_such_label_row_points_at_the_ancestor_chain(run_hook):
    ctx = nav(run_hook, LABEL)
    assert "H6" in ctx and "unquoted" in ctx.lower() and "dispatcher" in ctx.lower(), ctx


def test_green_navigation_is_silent(run_hook):
    assert nav(run_hook, GREEN_NAV) == ""
