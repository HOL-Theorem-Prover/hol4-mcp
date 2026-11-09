#!/usr/bin/env python3
"""
H6 -- PostToolUse hook injecting a reminder after a navigation/check tool
returns FAILED / TIMEOUT / PROOF BROKEN / "Tactic execution failed".

Fires on hol_check_proof AND on the navigation tools (hol_state_at,
hol_goals): those are the iteration-loop tools (RULE C reserves
hol_check_proof for end-of-theorem confirmation), so a session that follows
the rules meets every one of its failures through them.

Two parts, both advisory (exit 0 always), keyed on repeats per session
(state under ~/.claude/hook-state/<session_id>/h6_failures.json):

1. When the failing tactic matches the symptom table below, the corpus fact
   that explains that symptom -- on every failure. The facts are written down
   already and are still rediscovered by debugging, because the notes are
   indexed by CAUSE and the reader arrives with a SYMPTOM. The hook has the
   symptom in hand.
2. A RULE C reminder -- hol_check_proof is not a diagnosis tool, sub-suspend
   the failing arm instead of re-running it -- only from the SECOND
   consecutive failure on the same theorem, the moment the rule is actually
   being broken. A first failure with no symptom row is silent; a failure on
   another theorem, or a pass, starts the count over.

Calibration: the hint fires ONLY on a table match against a SHORT failing
step whose FIRST tactic is a listed one -- a token buried in a lumped opaque
arm is not evidence about that arm. Unmatched failures get part 1 alone. A
hint that is wrong at the moment of failure is worse than silence, because
it is read when trust is highest.

CHEAT (not verified) output is intentionally NOT a trigger -- reaching a
parked `cheat` is the expected result of the cheat-the-frontier pattern
(hol4-proving skill RULE I), not a failure.

Rule source: hol4-proving skill RULE C ('HOL4 - iteration loop').
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = ("mcp__hol4__hol_check_proof|mcp__hol4__hol_state_at"
                "|mcp__hol4__hol_goals")

import json
import os
import re
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import output_text  # noqa: E402

FAILURE_PATTERNS = [
    re.compile(r"TIMEOUT after \d+(\.\d+)?s"),
    re.compile(r"TIMEOUT: state_at exceeded"),
    re.compile(r"Status:\s*FAILED"),
    re.compile(r"Status:\s*INCOMPLETE"),
    re.compile(r"Status:\s*ERROR"),
    re.compile(r"<--\s*FAILED"),
    re.compile(r"Tactic execution failed"),
    re.compile(r"PROOF BROKEN"),
]

TOOLS = ("mcp__hol4__hol_check_proof", "mcp__hol4__hol_state_at",
         "mcp__hol4__hol_goals")

BANNER = "hol4-hook H6: {tool} returned FAILED / TIMEOUT / PROOF BROKEN."

REMINDER = """\
Per hol4-proving skill RULE C, hol_check_proof is NOT a diagnosis tool — do
not re-run it to localize the failure.
  - Failure inside an opaque `THEN1 (...)` / `>- (...)` / `\\`-chain (the usual
    case)? SUB-SUSPEND the failing arm NOW — FIRST move, not after a second
    attempt: `>~ [pat] >- suspend "Label"` (or `>- suspend "Label"`) +
    `Resume thm[Label]: cheat QED` after the parent QED. Then `hol_state_at`
    lands on the real goal — the file owns the prefix. This is the default
    (~99% of opaque breaks).
  - FLAT body, no `>-`/chain above the frontier? Read with `hol_state_at`.
  - Do NOT bisect by moving a `cheat` through the chain, and do NOT
    reconstruct the goal with `hol_send`/`e`/`sg`/`expandf` — a scratch goal
    diverges silently from the file form (RULE G), and the all-goals drivers
    (`expandf`/`Manager.expand`) are banned.

Re-running the same check, or re-probing line numbers around the break,
without sub-suspending leaves the failure hidden inside the opaque wrapper
(re-running hol_check_proof for this is also a RULE C violation)."""

OPAQUE_HINT = """\
The break is inside an OPAQUE step: the report's first line already names the
step and the sub-suspend recipe — do that, not another probe. Any goal shown
(show_partial) is the state ENTERING the step, not the failure point; probes
at nearby lines return that same entry goal. Alternative: probe IN PLACE —
the failed replay parks the proofManager at the pre-block goals, so small
`e` steps work there, with `b()` to undo. Detail:
[[feedback_replay_discipline]] §state_at navigation limit."""

# --- symptom table ----------------------------------------------------------
#
# Each row: (mode, tactic regex, hint). `mode` is the failure shape the hint
# is true of:
#   "raised"  -- replay stopped on a HOL_ERR / exception (the tactic itself
#                threw), so the tactic is the fault and the hint diagnoses it
#   "unsolved"-- no exception and no timeout, so the tactic ran and left goals
# A timeout never matches: the server already prints a looping-tactic advisory,
# and a second opinion on top of it is noise.

PATTERN_HINT = """\
A pattern tactic RAISED — its pattern no longer matches anything. Two causes,
both of which leave the proof text looking correct:
  - it pins a PROVER-GENERATED name (`h''`, `h'³'`, `v15`, `q'`) that an
    adjacent edit or a library change re-rolled (skill RULE H: bind a stable
    name AT the split with `namedCases_on`/`rename1`, or reach by SHAPE);
  - a TYPE-variable mismatch: the pattern and the goal's term PRINT
    IDENTICALLY and still fail to match — annotate the type at the call site.
Read the live goal with `hol_state_at` and compare, rather than trying
pattern variants. Detail: [[feedback_hol4_mcp_proving]] §Prover-generated
names, §Polymorphic constructors."""

MATCHER_HINT = """\
A matcher RAISED — it found nothing to match. Check in this order:
  - a free TYPE VARIABLE in the LEMMA'S OWN statement: it prints the same as
    the goal's instance and still will not unify — pin the type where the
    lemma is stated, not at the use site;
  - the constant was `[simp]`-tagged, so it is no longer an ATOM in the
    assumptions and every lemma taking it as a hypothesis silently stops
    matching;
  - the assumption is not yet in the lemma's shape — an assumption-simplifying
    normaliser (`gvs []`) before the matcher, not a bigger rewrite set.
Detail: [[feedback_hol4_mcp_proving]] §Matchers won't match, §Polymorphic
constructors, §`[simp]` tags."""

SIMP_HINT = """\
`simp` left goals. `simp` uses the assumptions AS THEY STAND (it *is*
`asm_simp_tac`); `fs`/`gvs`/`rw` SIMPLIFY the assumptions first. So a fact
that is "right there in the assumptions" but needs rewriting before it is
usable will never close under `simp`, and will under `gvs`. ⚠ `fs`/`gvs`/`rw`
also SPLIT a disjunctive assumption into one goal per disjunct — check that a
following `>-` still dispatches the branch you meant.
Detail: [[feedback_hol4_mcp_proving]] §Which normaliser."""

TABLE = [
    ("raised", re.compile(r"\b(qpat_x_assum|qpat_assum|rename1|qmatch_\w+)\b"),
     PATTERN_HINT),
    ("raised", re.compile(r"\b(drule\w*|irule\w*|match_mp_tac|mp_then)\b"),
     MATCHER_HINT),
    # `simp` family ONLY. `srw_tac` belongs with `rw` (bossLib: `srw_tac` is
    # BasicProvers.srw_tac, `rw` is PRIM_SRW_TAC), and for that family the hint
    # is not merely unhelpful but false.
    ("unsolved", re.compile(r"^(simp|simp_tac|asm_simp_tac)\b"),
     SIMP_HINT),
]

# --- output-shape rows ------------------------------------------------------
#
# Keyed on the SERVER'S OWN diagnostic line rather than the failing tactic, so
# they need no tactic block and fire whether or not the call counted as a
# failure. Each names the corpus fact for that output shape.

INSIDE_ROW = re.compile(r"NOTE: target line \d+ is INSIDE step (\d+)")
BUDGET_ROW = re.compile(r"TIMEOUT: state_at exceeded .*?prefix=([\d.]+)s.*?target=([\d.]+)s")
LABEL_ROW = re.compile(r"No such label")

INSIDE_HINT = """\
The position is INSIDE an opaque step, so the goal shown is the step's ENTRY,
not the state at your line. Do not edit against it. Sub-suspend the arm now:
replace the arm with `>- suspend "X"` and append `Resume {thm}[X]: cheat QED`
after the parent QED; then `hol_state_at` inside the Resume body lands on the
real goal with the file owning the prefix. Detail: [[feedback_hol4_mcp_proving]]
§Reading a `>-` / `THEN1` / `\\\\`-chain arm's goal."""

BUDGET_HINT = """\
Read the split: prefix={prefix}s went to dependency load + earlier theorems,
target={target}s to this theorem's own tactics. {verdict} Detail:
[[feedback_replay_discipline]] §TIMEOUT."""

BUDGET_VERDICT_TARGET = ("The budget ran out in YOUR tactics: a looping rewrite "
                         "(`simp[<recursive_def>]` without `Once`, a GSYM oscillation) "
                         "or a blown-up prover -- sub-suspend the arm and read the goal; "
                         "do not widen timeout=.")
BUDGET_VERDICT_PREFIX = ("Your tactics never ran: inspect the reported active phase. "
                         "Build ancestors only when missing/stale; current-file "
                         "translation needs prefix/checkpoint diagnosis, not a "
                         "rewrite of the target proof.")

LABEL_HINT = """\
`No such label`: a Resume whose suspension was never registered. Check, in
order: (1) the Resume header's label is UNQUOTED (`Resume thm[Arm]:`, not
`["Arm"]`) -- a quoted one reports as this same symptom; (2) the dispatcher's
own QED navigates to "No goals" -- a dispatcher that broke before its
`suspend` registers nothing, and the output's "Ancestor chain" line names
the first broken ancestor; fix that one first. Detail:
[[feedback_suspend_resume]]."""


def output_hints(text):
    """Hints keyed on the server's own diagnostic lines, in output order."""
    out = []
    m = INSIDE_ROW.search(text)
    if m:
        t = THEOREM_RE.search(text)
        out.append(INSIDE_HINT.format(thm=t.group(1) if t else "thm"))
    m = BUDGET_ROW.search(text)
    if m:
        target = float(m.group(2))
        verdict = BUDGET_VERDICT_TARGET if target >= 0.5 else BUDGET_VERDICT_PREFIX
        out.append(BUDGET_HINT.format(prefix=m.group(1), target=m.group(2), verdict=verdict))
    if LABEL_ROW.search(text):
        out.append(LABEL_HINT)
    return out


FAIL_HEADERS = ("=== Failing tactic ===",
                "=== Where replay stopped (raised exception) ===")
# The failing-tactic block ends at the first line that starts a new report
# section rather than continuing the tactic text.
BLOCK_END = re.compile(r"^\s*(===|Remaining:|Use hol_state_at|NOTE:|To localize:"
                       r"|Opaque tactic|Status:|ERROR:|TIMEOUT:)")
COMBINATOR = re.compile(r"\s*(>>|>-|>~|>>~|\\\\|THEN1|THEN)\s*")
MAX_STEP_CHARS = 200   # above this the step is a lump, not one tactic
# The server elides a huge failing body down to head+tail; what is left can fall
# under MAX_STEP_CHARS, so the marker — not the surviving length — is what says
# "this step is a lump".
ELIDED = re.compile(r"\.\.\.\s*\d+\s*lines elided\s*\.\.\.")


def failing_tactic(text):
    """The first tactic of the failing step, or None if there is no usable
    single-tactic step to key a hint on."""
    lines = text.split("\n")
    start = None
    for i, l in enumerate(lines):
        if l.strip() in FAIL_HEADERS:
            start = i + 1
            break
    if start is None:
        return None
    body = []
    for l in lines[start:]:
        if not l.strip() or BLOCK_END.match(l):
            break
        body.append(l.strip())
    step = " ".join(body)
    if not step or len(step) > MAX_STEP_CHARS or ELIDED.search(step):
        return None
    step = COMBINATOR.sub(" ", step, count=1).strip() if COMBINATOR.match(step) else step
    # Only the FIRST tactic of the step ran unconditionally; a token after a
    # combinator may never have been reached.
    return re.split(r">>|>-|>~|\\\\|\bTHEN1\b|\bTHEN\b", step)[0].strip()


def failure_mode(text):
    if "TIMEOUT" in text or "timed out" in text.lower():
        return "timeout"
    if ("HOL_ERR" in text or "Exception-" in text
            or "raised exception" in text.lower()):
        return "raised"
    return "unsolved"


OPAQUE = re.compile(r"in opaque step \d+|opaque step at lines|Opaque tactic — cannot inspect")


def matched_hint(text):
    tac = failing_tactic(text)
    if not tac:
        return None
    mode = failure_mode(text)
    for want, rx, hint in TABLE:
        if mode == want and rx.search(tac):
            return f"LIKELY CAUSE — the failing tactic is `{tac}`.\n{hint}"
    return None


STATE = os.path.expanduser("~/.claude/hook-state")
THEOREM_RE = re.compile(r"^Theorem:\s*([A-Za-z0-9_']+)", re.M)


def state_file(payload):
    return os.path.join(STATE, payload.get("session_id") or "nosession",
                        "h6_failures.json")


def load_state(path):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return {}


def save_state(path, state):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(state, fh)
    except OSError:
        pass


def theorem_of(payload, text):
    m = THEOREM_RE.search(text)
    if m:
        return m.group(1)
    return payload.get("tool_input", {}).get("theorem") or "?"


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    if tool not in TOOLS:
        return 0
    text = output_text(payload)
    path = state_file(payload)
    state = load_state(path)
    theorem = theorem_of(payload, text)
    short = tool.rsplit("__", 1)[-1]
    shape_hints = output_hints(text)
    if BUDGET_ROW.search(text) or "TIMEOUT after" in text:
        # H29 lets a stop/restart through shortly after a budget TIMEOUT.
        save_state(os.path.join(os.path.dirname(path), "last_timeout"), time.time())
    if "target tactics have not run" in text.lower():
        # The shared server already names the phase and gives its remedy.
        # Do not count prefix failures as repeated failed target-proof edits.
        if state.get("theorem") == theorem:
            save_state(path, {})
        return 0
    if not any(rx.search(text) for rx in FAILURE_PATTERNS):
        if state.get("theorem") == theorem:
            save_state(path, {})
        if not shape_hints:
            return 0
        parts = [f"hol4-hook H6: {short} output needs reading."] + shape_hints
        print(json.dumps({"hookSpecificOutput": {
            "hookEventName": "PostToolUse", "additionalContext": "\n\n".join(parts)}}))
        return 0
    count = state.get("count", 0) + 1 if state.get("theorem") == theorem else 1
    save_state(path, {"theorem": theorem, "count": count})
    banner = BANNER.format(tool=short)
    hint = matched_hint(text)
    opaque = OPAQUE_HINT if OPAQUE.search(text) else None
    parts = ([banner] + ([hint] if hint else []) + shape_hints
             + ([opaque] if opaque else []) + ([REMINDER] if count >= 2 else []))
    if len(parts) == 1:
        return 0
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": "\n\n".join(parts),
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
