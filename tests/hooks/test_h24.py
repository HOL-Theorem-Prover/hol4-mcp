"""H24 judges a binding's own right-hand side, not the text that follows it."""
import json


def advice(run_hook, old, new):
    code, _, out = run_hook("h24_custom_tactic_advisory.py", "Edit",
                            {"file_path": "/tmp/fooScript.sml",
                             "old_string": old, "new_string": new})
    assert code == 0
    return json.loads(out)["hookSpecificOutput"]["additionalContext"] if out else ""


def test_unchanged_theorem_transformation_before_edited_proof_is_silent(run_hook):
    binding = "val th2 = th1 |> SIMP_RULE (srw_ss()) [] |> GEN_ALL;\n"
    old = binding + "\nTheorem t:\n  T\nProof\n  simp []\nQED\n"
    new = binding + "\nTheorem t:\n  T\nProof\n  rw []\n  >> simp []\nQED\n"
    assert advice(run_hook, old, new) == ""


def test_new_tactic_bindings_are_reported(run_hook):
    assert "foo_tac" in advice(run_hook, "", "val foo_tac = rw [] >> simp [];\n")
    assert "foo" in advice(run_hook, "", "val foo =\n  rw []\n  >> simp [];\n")
    assert advice(run_hook, "", "val th = th1 |> GEN_ALL;\n") == ""
