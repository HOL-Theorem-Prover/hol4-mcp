"""H17 refuses, once, an edit that adds a Resume header HOL does not read as a
label path: a bare later entry (`t[a, b]`, which HOL takes for an attribute)
or a stacked `t[a][b]` (a parse error). An identical retry passes and is
logged; `key=value` entries and theorem attribute lists never fire."""
import json

import pytest

SESSION = "h17-session"
FILE = "/w/fooScript.sml"


def _edit(run_hook, old, new):
    return run_hook("h17_then_suspend.py", "Edit",
                    {"file_path": FILE, "old_string": old, "new_string": new},
                    session_id=SESSION)


def _ctx(out):
    return json.loads(out)["hookSpecificOutput"]["additionalContext"] if out.strip() else ""


@pytest.mark.parametrize("header", ["Resume t[num, unsigned]:", "Resume t[num][unsigned]:"])
def test_a_multi_label_header_is_refused_once(run_hook, header):
    code, err, _ = _edit(run_hook, "QED\n", f"QED\n\n{header}\n  cheat\nQED\n")
    assert code == 2, err
    assert "Resume t[unsigned]:" in err and "flat" in err, err
    code, _, out = _edit(run_hook, "QED\n", f"QED\n\n{header}\n  cheat\nQED\n")
    assert code == 0 and "OVERRIDDEN" in _ctx(out) and "H17" in _ctx(out), out


def test_a_written_file_with_a_multi_label_header_is_refused(run_hook):
    code, err, _ = run_hook("h17_then_suspend.py", "Write",
                            {"file_path": FILE,
                             "content": "Resume t[num,unsigned]:\n  cheat\nQED\n"},
                            session_id=SESSION)
    assert code == 2, err


@pytest.mark.parametrize("header", [
    "Resume t[num]:",
    "Resume willsplit2[q,smlname=q2sg]:",
    "Resume testTacMod[rtp_qpp,exclude_simps=AND_CLAUSES]:",
    "Theorem x[simp,local]:",
])
def test_a_valid_header_passes(run_hook, header):
    code, err, out = _edit(run_hook, "QED\n", f"QED\n\n{header}\n  cheat\nQED\n")
    assert code == 0 and not err and not out.strip(), (err, out)


def test_an_edit_that_keeps_an_existing_header_passes(run_hook):
    old = "Resume t[num,unsigned]:\n  cheat\nQED\n"
    code, err, out = _edit(run_hook, old, old.replace("cheat", "simp[]"))
    assert code == 0 and not err and not out.strip(), (err, out)
