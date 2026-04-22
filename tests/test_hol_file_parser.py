"""Tests for HOL file parser."""

import pytest
from pathlib import Path

from hol4_mcp.hol_file_parser import (
    parse_theorems, parse_file, parse_p_output,
    parse_local_blocks,
    StepPlan, step_line_numbers, format_step_context,
    _needs_infix_parens, _frag_to_cmd,
    parse_step_plan_output,
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
    with pytest.raises(HOLParseError, match="No JSON object found"):
        parse_linearize_with_spans_output(output)


def test_parse_linearize_embedded_json():
    """JSON embedded after other output (e.g. metis progress) should be found."""
    output = 'metis: {"ok":[{"t":"tac","s":0,"e":3,"a":false}]}'
    result = parse_linearize_with_spans_output(output)
    assert len(result) == 1
    assert result[0][0] == "tac"


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


def test_proof_with_annotations():
    """Proof[...] annotations (e.g. exclude_simps) should be parsed correctly."""
    content = '''\
Theorem assign_WordFromInt:
  op = WordOp WordFromInt ==> assign_thm_goal
Proof[exclude_simps = INT_OF_NUM NUM_EQ0]
  rpt strip_tac
QED
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    thm = thms[0]
    assert thm.name == "assign_WordFromInt"
    assert thm.proof_body == "rpt strip_tac"
    assert thm.goal == "op = WordOp WordFromInt ==> assign_thm_goal"


def test_proof_with_empty_annotations():
    """Proof[] should also be handled."""
    content = '''\
Theorem foo:
  T
Proof[]
  simp[]
QED
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    assert thms[0].proof_body == "simp[]"


def test_proof_annotation_line_numbers():
    """Line numbers should be correct with Proof[...] annotations."""
    content = '''\
Theorem bar:
  T /\\ T
Proof[exclude_simps = foo bar]
  conj_tac >> simp[]
QED
'''
    thms = parse_theorems(content)
    assert len(thms) == 1
    thm = thms[0]
    assert thm.start_line == 1
    # proof_start_line is the line after Proof[...] (first line of proof body)
    lines = content.split('\n')
    proof_line_idx = next(i for i, l in enumerate(lines) if 'Proof[' in l)
    assert thm.proof_start_line == proof_line_idx + 2  # 1-indexed, line after Proof


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


# =============================================================================
# Local block parsing
# =============================================================================


def test_parse_local_blocks_same_line():
    """local open X in on one line (common HOL4 pattern)."""
    content = '''local open fooTheory barTheory in
  Theorem x: T Proof simp[] QED
  Theorem y: T Proof simp[] QED
end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 1
    assert blocks[0].local_line == 1
    assert blocks[0].in_line == 1
    assert blocks[0].end_line == 4


def test_parse_local_blocks_multi_line():
    """local and in on separate lines."""
    content = '''local
  open fooTheory
  open barTheory
in
  Theorem x: T Proof simp[] QED
end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 1
    assert blocks[0].local_line == 1
    assert blocks[0].in_line == 4
    assert blocks[0].end_line == 6


def test_parse_local_blocks_nested():
    """Nested local blocks."""
    content = '''local
  open fooTheory
in
  local open barTheory in
    Theorem x: T Proof simp[] QED
  end

  Theorem y: T Proof simp[] QED
end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 2
    inner = [b for b in blocks if b.local_line == 4][0]
    assert inner.in_line == 4
    assert inner.end_line == 6
    outer = [b for b in blocks if b.local_line == 1][0]
    assert outer.in_line == 3
    assert outer.end_line == 9


def test_parse_local_blocks_stripping():
    """Keywords inside comments/strings should not create false blocks."""
    content = '''(* local open fooTheory in *)
val x = "local open barTheory in"
local open bazTheory in
  Theorem x: T Proof simp[] QED
end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 1
    assert blocks[0].local_line == 3


def test_parse_local_blocks_multiple():
    """Multiple non-nested local blocks."""
    content = '''local open A in
  val x = 1
end

local open B in
  val y = 2
end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 2
    assert blocks[0].local_line == 1
    assert blocks[1].local_line == 5


def test_parse_local_blocks_cakeml_style():
    """CakeML-style multi-theorem local block."""
    content = '''local open fooTheory barTheory bazTheory in

Theorem thm1:
  !x. P x
Proof
  simp[]
QED

Theorem thm2:
  !y. Q y
Proof
  rw[]
QED

end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 1
    lb = blocks[0]
    assert lb.local_line == 1
    assert lb.in_line == 1
    lines = content.split('\n')
    end_idx = next(i for i, l in enumerate(lines) if l.strip() == 'end')
    assert lb.end_line == end_idx + 1


def test_parse_local_blocks_with_let_inside():
    """local block containing let...in...end must not close on let's end."""
    content = '''local
  val gim = 1
in
  fun lift_monoid_thm suffix = let
    val x = suffix
  in
    x + 1
  end

end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 1
    lb = blocks[0]
    assert lb.local_line == 1
    assert lb.in_line == 3
    assert lb.end_line == 10  # the 'end' on line 10 closes 'local', NOT line 8


def test_parse_local_blocks_with_multiple_lets_inside():
    """local block with multiple nested let blocks."""
    content = '''local
  val a = 1
in
  fun f x = let val y = x in y end
  fun g x = let val z = x in let val w = z in w end end

end
'''
    blocks = parse_local_blocks(content)
    assert len(blocks) == 1
    lb = blocks[0]
    assert lb.local_line == 1
    assert lb.in_line == 3
    assert lb.end_line == 7


class TestStepLineNumbers:
    """Tests for step_line_numbers."""

    def test_basic(self):
        # "line 0\n" = 7 chars, lines start at 0,7,14,21,28,35
        content = "line 0\nline 1\nline 2\nline 3\nline 4\nline 5\n"
        offset = 7  # proof starts at "line 1" (line 2)
        plan = [
            StepPlan(end=7, kind="expand", text="strip_tac"),   # proof body 0..7 -> abs 7..14
            StepPlan(end=14, kind="open", text="open_then1"),   # proof body 7..14 -> abs 14..21
            StepPlan(end=21, kind="expand", text="simp[]"),      # proof body 14..21 -> abs 21..28
        ]
        lines = step_line_numbers(plan, offset, content)
        assert len(lines) == 3
        # Step 0 starts at abs 7 (line 2)
        assert lines[0] == 2
        # Step 1 starts at abs 7+7=14 (line 3)
        assert lines[1] == 3
        # Step 2 starts at abs 7+14=21 (line 4)
        assert lines[2] == 4

    def test_empty(self):
        assert step_line_numbers([], 0, "") == []


class TestFormatStepContext:
    """Tests for format_step_context."""

    def _make_plan(self):
        return [
            StepPlan(end=10, kind="expand", text="rpt strip_tac"),
            StepPlan(end=20, kind="expand", text="Induct_on `x`"),
            StepPlan(end=30, kind="open", text="open_then1"),
            StepPlan(end=40, kind="expand", text="simp[]"),
            StepPlan(end=50, kind="expand", text="cheat"),      # fail_idx=4
            StepPlan(end=60, kind="close", text="close_paren"),
            StepPlan(end=70, kind="expand", text="fs[APPEND]"),
        ]

    def _make_lines(self, plan):
        # Pretend all on line 10 for simple tests (line-based filtering
        # only matters for context_before/after bounds)
        return [10] * len(plan)

    def test_failing_tactic_always_shown(self):
        plan = self._make_plan()
        lines = self._make_lines(plan)
        result = format_step_context(plan, fail_idx=4, step_lines=lines)
        assert result == ["", "=== Failing tactic ===", "cheat"]

    def test_fail_on_expand_shows_tactic_text(self):
        plan = self._make_plan()
        lines = self._make_lines(plan)
        # fail_idx=3 is an expand step (simp[])
        result = format_step_context(plan, fail_idx=3, step_lines=lines)
        assert result == ["", "=== Failing tactic ===", "simp[]"]

    def test_fail_on_open_shows_function_name(self):
        plan = self._make_plan()
        lines = self._make_lines(plan)
        # fail_idx=2 is an open step (open_then1)
        result = format_step_context(plan, fail_idx=2, step_lines=lines)
        assert result == ["", "=== Failing tactic ===", "open_then1"]

    def test_no_context_default(self):
        plan = self._make_plan()
        lines = self._make_lines(plan)
        result = format_step_context(plan, fail_idx=4, step_lines=lines)
        # Only failing tactic, no steps section
        assert "=== Steps around failure ===" not in result

    def test_context_shows_steps(self):
        plan = self._make_plan()
        lines = self._make_lines(plan)
        result = format_step_context(
            plan, fail_idx=4, step_lines=lines,
            context_before=1, context_after=1,
        )
        text = "\n".join(result)
        # Should include steps section
        assert "=== Steps around failure ===" in text
        # Failing step marked
        assert "<-- FAILED" in text

    def test_nesting_indentation(self):
        plan = self._make_plan()
        # Give distinct lines so context_before/after filters correctly
        lines = [5, 6, 7, 8, 9, 10, 11]
        result = format_step_context(
            plan, fail_idx=4, step_lines=lines,
            context_before=1, context_after=1,
        )
        # cheat (idx 4) is inside open/close, should be indented
        text = "\n".join(result)
        # Step 3 (simp[]) is after open, should be indented
        assert "  3: simp[]" in text
        # Step 4 (cheat) should be indented and marked FAILED
        assert "  4: cheat  <-- FAILED" in text
        # Step 5 (close_paren) still indented before depth decreases
        assert "  5: close_paren" in text

    def test_fail_idx_out_of_range(self):
        plan = self._make_plan()
        lines = self._make_lines(plan)
        assert format_step_context(plan, fail_idx=99, step_lines=lines) == []
        assert format_step_context(plan, fail_idx=-1, step_lines=lines) == []

    def test_empty_plan(self):
        assert format_step_context([], fail_idx=0, step_lines=[]) == []

    def test_line_based_filtering(self):
        """context_before/after use source lines, not step indices."""
        plan = [
            StepPlan(end=5, kind="expand", text="tac_alpha"),
            StepPlan(end=10, kind="expand", text="tac_beta"),
            StepPlan(end=15, kind="expand", text="tac_gamma"),  # fail_idx=2, line 30
            StepPlan(end=20, kind="expand", text="tac_delta"),
            StepPlan(end=25, kind="expand", text="tac_epsilon"),
        ]
        step_lines = [10, 20, 30, 40, 50]
        result = format_step_context(
            plan, fail_idx=2, step_lines=step_lines,
            context_before=15, context_after=15,
        )
        text = "\n".join(result)
        # Line range [15, 45]: steps at line 10 and 50 excluded
        assert "tac_beta" in text
        assert "tac_gamma" in text  # failing
        assert "tac_delta" in text
        assert "tac_alpha" not in text
        assert "tac_epsilon" not in text


class TestNeedsInfixParens:
    def test_bare_minus(self):
        assert _needs_infix_parens(">- strip_tac")

    def test_double_minus(self):
        assert _needs_infix_parens(">>- strip_tac")

    def test_triple_minus(self):
        assert _needs_infix_parens(">>>- strip_tac")

    def test_leading_space(self):
        assert _needs_infix_parens("  >- strip_tac")

    def test_normal_tactic(self):
        assert not _needs_infix_parens("strip_tac")

    def test_simp(self):
        assert not _needs_infix_parens("simp[]")

    def test_parenthesized(self):
        assert not _needs_infix_parens("(simp[] >- fs[])")


class TestFragToCmdInfix:
    def test_bare_infix_gets_parens(self):
        assert _frag_to_cmd("expand", ">- strip_tac") == "ef(goalFrag.expand((>- strip_tac)));"

    def test_normal_tactic_no_extra_parens(self):
        assert _frag_to_cmd("expand", "strip_tac") == "ef(goalFrag.expand(strip_tac));"

    def test_open_step_unchanged(self):
        assert _frag_to_cmd("open", "open_then1") == "ef(goalFrag.open_then1);"


# Real goalfrag_step_plan_json outputs captured from HOL4, used to test
# parse_step_plan_output + format_step_context with real parsed data.

_REAL_JSON = {
    # rpt strip_tac >> Induct_on `x` >- simp[] >- cheat >> fs[]
    "then_chain_with_thenlt": (
        '{"ok":[{"end":13,"type":"expand","text":"rpt strip_tac"},'
        '{"end":30,"type":"expand","text":"Induct_on `x`"},'
        '{"end":30,"type":"open","text":"open_then1"},'
        '{"end":40,"type":"expand","text":"simp[]"},'
        '{"end":40,"type":"close","text":"close_paren"},'
        '{"end":40,"type":"open","text":"open_then1"},'
        '{"end":49,"type":"expand","text":"cheat"},'
        '{"end":49,"type":"close","text":"close_paren"},'
        '{"end":57,"type":"expand","text":"fs[]"}]}'
    ),
    # >- strip_tac (no left operand — parsed as single Opaque)
    "bare_infix": (
        '{"ok":[{"end":12,"type":"expand","text":">- strip_tac"}]}'
    ),
    # simp[Once evaluate_def] >- strip_tac (properly decomposed)
    "thenlt_decomposed": (
        '{"ok":[{"end":23,"type":"expand","text":"simp[Once evaluate_def]"},'
        '{"end":23,"type":"open","text":"open_then1"},'
        '{"end":36,"type":"expand","text":"strip_tac"},'
        '{"end":36,"type":"close","text":"close_paren"}]}'
    ),
    # rpt strip_tac >> Cases_on `x` >- simp[] >- fs[]
    "two_arm_thenlt": (
        '{"ok":[{"end":13,"type":"expand","text":"rpt strip_tac"},'
        '{"end":29,"type":"expand","text":"Cases_on `x`"},'
        '{"end":29,"type":"open","text":"open_then1"},'
        '{"end":39,"type":"expand","text":"simp[]"},'
        '{"end":39,"type":"close","text":"close_paren"},'
        '{"end":39,"type":"open","text":"open_then1"},'
        '{"end":47,"type":"expand","text":"fs[]"},'
        '{"end":47,"type":"close","text":"close_paren"}]}'
    ),
    # strip_tac >- (simp[] >- fs[]) — inner >- not decomposed (parens make it atomic)
    "nested_in_parens": (
        '{"ok":[{"end":9,"type":"expand","text":"strip_tac"},'
        '{"end":9,"type":"open","text":"open_then1"},'
        '{"end":29,"type":"expand","text":"(simp[] >- fs[])"},'
        '{"end":29,"type":"close","text":"close_paren"}]}'
    ),
}


class TestParseStepPlan:
    """Test parse_step_plan_output with real HOL4 JSON output."""

    def test_then_chain_with_thenlt(self):
        plan = parse_step_plan_output(_REAL_JSON["then_chain_with_thenlt"])
        # 9 steps: 2 expands, open, expand, close, open, expand, close, expand
        assert len(plan) == 9
        assert plan[0] == StepPlan(end=13, kind="expand", text="rpt strip_tac")
        assert plan[1] == StepPlan(end=30, kind="expand", text="Induct_on `x`")
        assert plan[2] == StepPlan(end=30, kind="open", text="open_then1")
        assert plan[3] == StepPlan(end=40, kind="expand", text="simp[]")
        assert plan[4] == StepPlan(end=40, kind="close", text="close_paren")
        assert plan[5] == StepPlan(end=40, kind="open", text="open_then1")
        assert plan[6] == StepPlan(end=49, kind="expand", text="cheat")
        assert plan[7] == StepPlan(end=49, kind="close", text="close_paren")
        assert plan[8] == StepPlan(end=57, kind="expand", text="fs[]")

    def test_bare_infix(self):
        plan = parse_step_plan_output(_REAL_JSON["bare_infix"])
        assert len(plan) == 1
        assert plan[0] == StepPlan(end=12, kind="expand", text=">- strip_tac")

    def test_thenlt_decomposed(self):
        plan = parse_step_plan_output(_REAL_JSON["thenlt_decomposed"])
        assert len(plan) == 4
        assert plan[0] == StepPlan(end=23, kind="expand", text="simp[Once evaluate_def]")
        assert plan[1] == StepPlan(end=23, kind="open", text="open_then1")
        assert plan[2] == StepPlan(end=36, kind="expand", text="strip_tac")
        assert plan[3] == StepPlan(end=36, kind="close", text="close_paren")

    def test_two_arm_thenlt(self):
        plan = parse_step_plan_output(_REAL_JSON["two_arm_thenlt"])
        assert len(plan) == 8
        # First arm: open_then1, simp[], close
        assert plan[2] == StepPlan(end=29, kind="open", text="open_then1")
        assert plan[3] == StepPlan(end=39, kind="expand", text="simp[]")
        assert plan[4] == StepPlan(end=39, kind="close", text="close_paren")
        # Second arm: open_then1, fs[], close
        assert plan[5] == StepPlan(end=39, kind="open", text="open_then1")
        assert plan[6] == StepPlan(end=47, kind="expand", text="fs[]")
        assert plan[7] == StepPlan(end=47, kind="close", text="close_paren")

    def test_nested_in_parens(self):
        """Inner >- inside parens is not decomposed — stays as expand text."""
        plan = parse_step_plan_output(_REAL_JSON["nested_in_parens"])
        assert len(plan) == 4
        assert plan[0] == StepPlan(end=9, kind="expand", text="strip_tac")
        assert plan[1] == StepPlan(end=9, kind="open", text="open_then1")
        assert plan[2] == StepPlan(end=29, kind="expand", text="(simp[] >- fs[])")
        assert plan[3] == StepPlan(end=29, kind="close", text="close_paren")


class TestFormatStepContextReal:
    """Test format_step_context with real parsed step plans."""

    def test_thenlt_cheat_failure(self):
        plan = parse_step_plan_output(_REAL_JSON["then_chain_with_thenlt"])
        # cheat at idx 6; all on line 1 for simplicity
        lines = [1] * len(plan)
        result = format_step_context(
            plan, fail_idx=6, step_lines=lines,
            context_before=1, context_after=1,
        )
        text = "\n".join(result)
        assert "=== Failing tactic ===" in text
        assert "cheat  <-- FAILED" in text
        # Should show open/expand/close structure around the failing arm
        assert "open_then1" in text
        assert "close_paren" in text

    def test_bare_infix_failure(self):
        plan = parse_step_plan_output(_REAL_JSON["bare_infix"])
        lines = [1]
        result = format_step_context(plan, fail_idx=0, step_lines=lines)
        assert result == ["", "=== Failing tactic ===", ">- strip_tac"]

    def test_nested_parens_shows_atomic_text(self):
        plan = parse_step_plan_output(_REAL_JSON["nested_in_parens"])
        lines = [1] * len(plan)
        result = format_step_context(
            plan, fail_idx=2, step_lines=lines,
            context_before=1, context_after=1,
        )
        text = "\n".join(result)
        # The inner >- is not decomposed, shows as (simp[] >- fs[])
        assert "(simp[] >- fs[])" in text

