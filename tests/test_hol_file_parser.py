"""Tests for HOL file parser."""

import pytest
from pathlib import Path

from hol4_mcp.hol_file_parser import (
    parse_theorems, parse_file, parse_p_output,
)

FIXTURES_DIR = Path(__file__).parent / "fixtures"


def test_parse_theorems():
    """Test parsing theorems from content."""
    content = r'''
Theorem foo[simp]:
  !x. P x ==> Q x
Proof
  rw[] \\
  cheat
QED

Triviality bar:
  A /\ B ==> B /\ A
Proof
  metis_tac[]
QED

Theorem baz[local,simp]:
  !n. n + 0 = n
Proof
  Induct_on `n` \\
  gvs[] \\
  cheat
QED
'''
    thms = parse_theorems(content)

    assert len(thms) == 3

    assert thms[0].name == "foo"
    assert thms[0].kind == "Theorem"
    assert thms[0].has_cheat == True
    assert thms[0].attributes == ["simp"]
    assert "rw[]" in thms[0].proof_body

    assert thms[1].name == "bar"
    assert thms[1].kind == "Triviality"
    assert thms[1].has_cheat == False

    assert thms[2].name == "baz"
    assert thms[2].attributes == ["local", "simp"]
    assert thms[2].has_cheat == True


def test_parse_theorems_with_prime_names():
    """Theorem/Definition names with trailing prime should be parsed."""
    content = r'''
Theorem compile_correct':
  T
Proof
  simp[]
QED

Definition helper_def':
  helper' x = x
Termination
  WF_REL_TAC `measure I`
End
'''
    thms = parse_theorems(content)
    names = [t.name for t in thms]
    assert "compile_correct'" in names
    assert "helper_def'" in names


def test_parse_fixture_file():
    """Test parsing the fixture HOL file."""
    f = FIXTURES_DIR / "testScript.sml"
    if not f.exists():
        pytest.skip(f"Fixture not found: {f}")

    thms = parse_file(f)
    assert len(thms) == 5

    assert thms[0].name == "add_zero"
    assert thms[0].has_cheat == False

    assert thms[1].name == "needs_proof"
    assert thms[1].has_cheat == True

    assert thms[2].name == "partial_proof"
    assert thms[2].has_cheat == True
    assert thms[2].proof_body  # has content before cheat

    assert thms[4].name == "helper_lemma"
    assert thms[4].kind == "Triviality"


def test_parse_theorems_in_comments_ignored():
    """Theorems inside comments (including nested) should be stripped."""
    content = r'''
(* Commented-out theorem:
Theorem ghost:
  T
Proof
  cheat
QED
*)

Theorem real_one:
  !x. x = x
Proof
  rw[]
QED

(* Nested comment: (* Theorem ghost2: T Proof cheat QED *) still comment *)

Theorem real_two:
  !y. y = y
Proof
  rw[]
QED

(*
Theorem ghost3:
  F
Proof
  (* nested (* deep *) comment *)
  cheat
QED
*)
'''
    thms = parse_theorems(content)
    names = [t.name for t in thms]
    assert names == ["real_one", "real_two"]
    # Line numbers should be correct despite comment stripping
    assert thms[0].start_line == 10
    assert thms[1].start_line == 18


def test_parse_resume_blocks():
    """Resume blocks should be parsed with suspension_name and label_name."""
    content = r'''
Theorem conj_comm[suspend]:
  !A B. A /\ B ==> B /\ A
Proof
  rpt strip_tac
QED

Resume conj_comm[1]:
  metis_tac[]
QED

Resume conj_comm[2,simp]:
  metis_tac[]
QED

Theorem simple_thm:
  !x. x = x
Proof
  simp[]
QED
'''
    thms = parse_theorems(content)
    names = [t.name for t in thms]
    assert "conj_comm" in names
    assert "conj_comm[1]" in names
    assert "conj_comm[2]" in names
    assert "simple_thm" in names
    assert len(thms) == 4

    # Check Resume block fields
    r1 = thms[1]
    assert r1.name == "conj_comm[1]"
    assert r1.kind == "Resume"
    assert r1.suspension_name == "conj_comm"
    assert r1.label_name == "1"
    assert r1.attributes == []
    assert r1.goal == ""  # Extracted at runtime
    assert "metis_tac" in r1.proof_body

    r2 = thms[2]
    assert r2.name == "conj_comm[2]"
    assert r2.kind == "Resume"
    assert r2.suspension_name == "conj_comm"
    assert r2.label_name == "2"
    assert r2.attributes == ["simp"]

    # Non-Resume theorems should NOT have suspension fields
    assert thms[0].suspension_name is None
    assert thms[0].label_name is None
    assert thms[3].suspension_name is None


def test_parse_resume_proof_body_offset():
    """Resume proof_body_offset should point to actual proof body."""
    content = '''Resume foo[lbl]:
  simp[] >> gvs[]
QED
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    thm = thms[0]
    assert thm.proof_body == "simp[] >> gvs[]"
    assert content[thm.proof_body_offset:thm.proof_body_offset + 15] == "simp[] >> gvs[]"


def test_parse_resume_in_comments_ignored():
    """Resume blocks inside comments should be ignored."""
    content = r'''
(* Resume ghost[lbl]:
  cheat
QED *)

Resume real_one[a]:
  simp[]
QED
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    assert thms[0].name == "real_one[a]"


def test_parse_resume_with_attrs():
    """Resume with extra attributes (smlname, exclude_simps)."""
    content = r'''
Theorem foo:
  T
Proof
  suspend "bar"
QED

Resume foo[bar,smlname=myname,exclude_simps=AND_CLAUSES]:
  simp[]
QED
'''
    thms = parse_theorems(content)
    resume = next(t for t in thms if t.kind == "Resume")
    assert resume.name == "foo[bar]"
    assert resume.suspension_name == "foo"
    assert resume.label_name == "bar"
    assert resume.attributes == ["smlname=myname", "exclude_simps=AND_CLAUSES"]


def test_parse_multiple_resume_same_theorem():
    """Multiple Resume blocks for the same theorem should all be parsed."""
    content = r'''
Theorem multi:
  T
Proof
  iff_tac >- suspend "l2r" >- suspend "r2l"
QED

Resume multi[l2r]:
  simp[]
QED

Resume multi[r2l]:
  simp[]
QED
'''
    thms = parse_theorems(content)
    names = [t.name for t in thms]
    assert "multi[l2r]" in names
    assert "multi[r2l]" in names


def test_parse_definition_termination():
    """Definition with Termination...End should be parsed as a theorem."""
    content = r'''
Definition factc_def:
  factc n =
    cv_if (cv_lt n (Num 1))
          (Num 1)
          (cv_mul n (factc (cv_sub n (Num 1))))
Termination
  WF_REL_TAC `measure cv_size`
  \\ Cases \\ simp [CaseEq "bool", c2b_def]
End

Theorem factc_is_fact:
  !n. factc (Num n) = Num (FACT n)
Proof
  Induct \\ once_rewrite_tac [factc_def, FACT] \\ simp [c2b_def]
QED

Definition simple_def:
  simple x = x + 1
End
'''
    thms = parse_theorems(content)
    names = [t.name for t in thms]
    # simple_def has no Termination block, should be skipped
    assert names == ["factc_def", "factc_is_fact"]

    defn = thms[0]
    assert defn.kind == "Definition"
    assert "WF_REL_TAC" in defn.proof_body
    assert defn.has_cheat == False
    assert defn.start_line == 2

    thm = thms[1]
    assert thm.kind == "Theorem"
    assert thm.name == "factc_is_fact"





def test_parse_p_output():
    """Test parsing p() output."""
    output = '''> p();
Induct_on `x` \\
gvs[] \\
simp[foo_def]
val it = () : unit
'''
    result = parse_p_output(output)
    assert result == '''Induct_on `x` \\
gvs[] \\
simp[foo_def]'''



def test_parse_p_output_empty():
    assert parse_p_output("") is None


def test_parse_p_output_only_prompts():
    assert parse_p_output("> p();\nval it = () : unit\n") is None


def test_parse_p_output_error():
    """Error output should return None, not be spliced as tactics."""
    error_output = """No goalstack is currently being managed.
Exception- HOL_ERR at proofManagerLib.p: raised"""
    assert parse_p_output(error_output) is None


def test_parse_p_output_error_prefix():
    """ERROR: sentinel outputs should return None."""
    assert parse_p_output("ERROR: HOL not running") is None
    assert parse_p_output("Error: HOL not running") is None


def test_parse_p_output_multiline_val_it():
    """Regression: multi-line 'val it =' format was returning None."""
    # Format 3: val it = on its own line, tactic on subsequent lines
    output = '''\
val it =
   completeInduct_on `LENGTH xs` \\
    rw[LET_THM] \\
     Cases_on `n >= LENGTH xs`
      >- (simp[])
      >- (gvs[])
: proof'''
    result = parse_p_output(output)
    assert result is not None, "Should parse multi-line val it format"
    assert 'completeInduct_on' in result
    assert ': proof' not in result  # Type annotation stripped
    assert 'val it' not in result   # val binding stripped


def test_parse_p_output_multiline_val_it_inline_proof():
    """Multi-line val it with : proof on last content line."""
    output = '''\
val it =
   simp[] \\
    gvs[]: proof'''
    result = parse_p_output(output)
    assert result is not None
    assert result.strip().endswith('gvs[]')
    assert ': proof' not in result


# Bug 3 regression tests: JSON parsing with preamble
from hol4_mcp.hol_file_parser import parse_linearize_with_spans_output, HOLParseError


def test_parse_linearize_with_preamble():
    """JSON parsing should work when HOL outputs preamble lines before JSON."""
    output = '''<<HOL message: loading stuff>>
<<HOL warning: some warning>>
{"ok":[{"t":"simp[]","s":0,"e":6,"a":false}]}
val it = () : unit'''
    result = parse_linearize_with_spans_output(output)
    assert len(result) == 1
    assert result[0][0] == "simp[]"


def test_parse_linearize_json_not_first_line():
    """JSON parsing should find JSON even if it's not on the first line."""
    output = '''Some random output
More output
{"ok":[{"t":"tac","s":0,"e":3,"a":true}]}'''
    result = parse_linearize_with_spans_output(output)
    assert len(result) == 1
    assert result[0][0] == "tac"
    assert result[0][3] is True  # use_eall


def test_parse_linearize_no_json():
    """Should raise HOLParseError when no valid JSON found."""
    output = '''No JSON here
Just some text
val it = () : unit'''
    with pytest.raises(HOLParseError, match="No valid JSON"):
        parse_linearize_with_spans_output(output)


def test_parse_linearize_malformed_json_then_valid():
    """Should skip malformed JSON lines and find valid one."""
    output = '''{not valid json
{"ok":[{"t":"good","s":0,"e":4,"a":false}]}'''
    result = parse_linearize_with_spans_output(output)
    assert len(result) == 1
    assert result[0][0] == "good"


# Bug 4 regression tests: proof_body_offset
def test_proof_body_offset_computed():
    """TheoremInfo should have correct proof_body_offset."""
    content = '''Theorem foo:
  !x. P x
Proof
  simp[]
QED
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    thm = thms[0]

    # proof_body_offset should point to 's' in 'simp[]' in the file
    assert content[thm.proof_body_offset:thm.proof_body_offset + 6] == "simp[]"


def test_proof_body_offset_with_leading_whitespace():
    """proof_body_offset should account for leading whitespace after Proof."""
    content = '''Theorem foo:
  P
Proof

  rw[]
QED
'''
    thms = parse_theorems(content)
    thm = thms[0]

    # Stripped body is "rw[]", offset should point to 'r'
    assert thm.proof_body == "rw[]"
    assert content[thm.proof_body_offset:thm.proof_body_offset + 4] == "rw[]"


def test_proof_body_offset_multiline():
    """proof_body_offset correct for multi-line proof body."""
    content = '''Theorem foo:
  !x. P x ==> Q x
Proof
  rpt strip_tac
  >> simp[]
  >> fs[]
QED
'''
    thms = parse_theorems(content)
    thm = thms[0]

    # Body starts with 'rpt strip_tac'
    assert thm.proof_body.startswith("rpt strip_tac")
    assert content[thm.proof_body_offset:thm.proof_body_offset + 13] == "rpt strip_tac"


# =============================================================================
# Keyword regex: [^\S\n]* prevents matching across lines (commit 8e70dba)
# =============================================================================


def test_keyword_no_cross_line_match_proof_qed():
    r"""Proof/QED with \s* would match blank lines left by comment stripping.

    [^\S\n]* ensures the keyword regex only matches horizontal whitespace,
    so blank lines between a comment and Proof/QED don't shift match positions.
    """
    # Simulate content where comment stripping left blank lines before keywords
    content = '''\
Theorem foo:
  T

Proof
  simp[]

QED
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    thm = thms[0]
    assert thm.name == "foo"
    # proof_end_line should point to the line AFTER QED, not a blank line
    lines = content.split('\n')
    qed_line_idx = next(i for i, l in enumerate(lines) if l.strip() == 'QED')
    assert thm.proof_end_line == qed_line_idx + 2  # 1-indexed, line after QED


def test_keyword_no_cross_line_match_termination_end():
    """Termination/End keywords must not match across blank lines."""
    content = '''\
Definition fact_def:
  fact (n:num) = if n = 0 then 1 else n * fact (n - 1)

Termination

  WF_REL_TAC `measure I`

End
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    thm = thms[0]
    assert thm.name == "fact_def"
    assert thm.kind == "Definition"
    lines = content.split('\n')
    end_line_idx = next(i for i, l in enumerate(lines) if l.strip() == 'End')
    assert thm.proof_end_line == end_line_idx + 2


def test_end_before_termination_skipped():
    """Definition...End without Termination should not match as Definition with proof.

    Regression from remote commit 6a49ce6: if End appears before Termination,
    it's a plain Definition, not one with a termination proof.
    """
    content = '''\
Definition simple_def:
  my_const = 42
End

Definition rec_def:
  rec_fn (n:num) = if n = 0 then 1 else n * rec_fn (n - 1)
Termination
  WF_REL_TAC `measure I`
End
'''
    thms = parse_theorems(content)
    # Only rec_def should be parsed (has Termination proof)
    assert len(thms) == 1
    assert thms[0].name == "rec_def"
