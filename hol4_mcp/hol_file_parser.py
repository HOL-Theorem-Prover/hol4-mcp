"""Parse HOL4 script files for theorem structure."""

import bisect
import re
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class TacticSpan:
    """A tactic with its source position."""
    text: str
    start: tuple[int, int]  # (line, col), 1-indexed
    end: tuple[int, int]    # (line, col), 1-indexed
    use_eall: bool = False  # True if tactic should apply to ALL goals (for >> chains)


def build_line_starts(content: str) -> list[int]:
    """Build table mapping line numbers to char offsets.

    line_starts[i] = char offset where line (i+1) begins.
    Line numbers are 1-indexed, but array is 0-indexed.
    """
    starts = [0]  # Line 1 starts at offset 0
    for i, c in enumerate(content):
        if c == '\n':
            starts.append(i + 1)  # Next line starts after newline
    return starts


def offset_to_line_col(offset: int, line_starts: list[int]) -> tuple[int, int]:
    """Convert char offset to (line, col), both 1-indexed."""
    # Find the line: largest line_starts[i] <= offset
    line = bisect.bisect_right(line_starts, offset)
    col = offset - line_starts[line - 1] + 1
    return (line, col)


def line_col_to_offset(line: int, col: int, line_starts: list[int]) -> int:
    """Convert (line, col) to char offset. Line and col are 1-indexed."""
    if line < 1 or line > len(line_starts):
        raise ValueError(f"Line {line} out of range (1-{len(line_starts)})")
    return line_starts[line - 1] + col - 1


class HOLParseError(Exception):
    """Error parsing HOL4 output."""
    pass


def _find_json_line(output: str, context: str) -> dict:
    """Find and parse the first JSON object line in output.

    HOL may print warnings/messages before the JSON line. This scans for the
    first line starting with '{' and attempts to parse it as JSON.

    Args:
        output: Raw output from HOL
        context: Description for error messages (e.g., "linearize_with_spans_json")

    Returns:
        Parsed JSON object

    Raises:
        HOLParseError if no valid JSON object found
    """
    import json

    for line in output.strip().split('\n'):
        line = line.strip()
        if line.startswith('{'):
            try:
                return json.loads(line)
            except json.JSONDecodeError:
                continue

    raise HOLParseError(f"No valid JSON object found in {context} output")


def parse_linearize_with_spans_output(output: str) -> list[tuple[str, int, int, bool]]:
    """Parse JSON output from linearize_with_spans_json.

    Expects: {"ok":[{"t":"text","s":0,"e":8,"a":false},...]} or {"err":"message"}
    Returns: list of (text, start_offset, end_offset, use_eall) tuples.
    Raises: HOLParseError if HOL4 returned an error or output is malformed.
    """
    result = _find_json_line(output, "linearize_with_spans_json")

    if 'ok' in result:
        try:
            return [(item['t'], item['s'], item['e'], item.get('a', False)) for item in result['ok']]
        except (KeyError, TypeError) as e:
            raise HOLParseError(f"Malformed tactic span in output: {e}") from e
    elif 'err' in result:
        raise HOLParseError(f"linearize_with_spans_json: {result['err']}")
    else:
        raise HOLParseError(f"Unexpected JSON structure: {result}")


def parse_step_positions_output(output: str) -> list[int]:
    """Parse JSON output from step_positions_json.

    Expects: {"ok":[offset1, offset2, ...]} or {"err":"message"}
    Returns: list of end offsets for each tactic step.
    Raises: HOLParseError if HOL4 returned an error or output is malformed.
    """
    result = _find_json_line(output, "step_positions_json")

    if 'ok' in result:
        try:
            return [int(pos) for pos in result['ok']]
        except (TypeError, ValueError) as e:
            raise HOLParseError(f"Malformed step positions in output: {e}") from e
    elif 'err' in result:
        raise HOLParseError(f"step_positions_json: {result['err']}")
    else:
        raise HOLParseError(f"Unexpected JSON structure: {result}")


def parse_prefix_commands_output(output: str) -> str:
    """Parse JSON output from prefix_commands_json.

    Expects: {"ok":"e(...);\n"} or {"err":"message"}
    Returns: The e() command string to execute.
    Raises: HOLParseError if HOL4 returned an error or output is malformed.
    """
    result = _find_json_line(output, "prefix_commands_json")

    if 'ok' in result:
        return result['ok']
    elif 'err' in result:
        raise HOLParseError(f"prefix_commands_json: {result['err']}")
    else:
        raise HOLParseError(f"Unexpected JSON structure: {result}")


@dataclass
class StepPlan:
    """A step with its end offset and command."""
    end: int       # End offset in proof body
    cmd: str       # e() command to execute this step


def parse_step_plan_output(output: str) -> list[StepPlan]:
    """Parse JSON output from step_plan_json.

    Expects: {"ok":[{"end":N,"cmd":"e(...);\\n"}, ...]} or {"err":"message"}
    Returns: list of StepPlan objects, one per executable step.
    Raises: HOLParseError if HOL4 returned an error or output is malformed.
    """
    result = _find_json_line(output, "step_plan_json")

    if 'ok' in result:
        try:
            steps = []
            for item in result['ok']:
                end = int(item['end'])
                cmd = str(item['cmd'])
                steps.append(StepPlan(end=end, cmd=cmd))
            return steps
        except (TypeError, ValueError, KeyError) as e:
            raise HOLParseError(f"Malformed step plan in output: {e}") from e
    elif 'err' in result:
        raise HOLParseError(f"step_plan_json: {result['err']}")
    else:
        raise HOLParseError(f"Unexpected JSON structure: {result}")


def make_tactic_spans(
    raw_spans: list[tuple[str, int, int, bool]],
    proof_body_offset: int,
    line_starts: list[int],
) -> list[TacticSpan]:
    """Convert raw (text, start, end, use_eall) tuples to TacticSpan with line/col.

    Args:
        raw_spans: Output from parse_linearize_with_spans_output (offsets relative to proof body)
        proof_body_offset: Char offset where proof body starts in the file
        line_starts: Line start table for the entire file

    Returns:
        List of TacticSpan with absolute line/col positions in the file.
    """
    result = []
    for text, start, end, use_eall in raw_spans:
        # Convert relative offsets to absolute
        abs_start = proof_body_offset + start
        abs_end = proof_body_offset + end
        start_lc = offset_to_line_col(abs_start, line_starts)
        end_lc = offset_to_line_col(abs_end, line_starts)
        result.append(TacticSpan(text=text, start=start_lc, end=end_lc, use_eall=use_eall))
    return result


@dataclass
class TheoremInfo:
    """Information about a theorem in a HOL script file."""
    name: str
    kind: str  # "Theorem", "Triviality", or "Definition"
    goal: str  # The statement to prove
    start_line: int  # Line of "Theorem name:"
    proof_start_line: int  # Line after "Proof" (first line of proof body)
    proof_end_line: int  # Line after "QED" (first line after theorem)
    has_cheat: bool
    proof_body: str = ""  # Content between Proof and QED (stripped)
    proof_body_offset: int = 0  # File offset where proof_body starts
    attributes: list[str] = field(default_factory=list)
    suspension_name: str | None = None  # For Resume: base theorem name
    label_name: str | None = None       # For Resume: first attribute = label

    @property
    def line_before_qed(self) -> int:
        """Line number of QED - 1 (last line of proof body)."""
        return self.proof_end_line - 2


def _strip_comments(content: str) -> str:
    """Replace SML comments (* ... *) with spaces, preserving newlines.

    Handles nested comments. Preserves character offsets so that line/col
    calculations on the result match the original content.
    """
    result = list(content)
    i = 0
    n = len(content)
    while i < n - 1:
        if content[i] == '(' and content[i + 1] == '*':
            # Found comment start - track nesting
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if j < n - 1 and content[j] == '(' and content[j + 1] == '*':
                    depth += 1
                    j += 2
                elif j < n - 1 and content[j] == '*' and content[j + 1] == ')':
                    depth -= 1
                    j += 2
                else:
                    j += 1
            # Blank out i..j, keeping newlines
            for k in range(i, j):
                if result[k] != '\n':
                    result[k] = ' '
            i = j
        else:
            i += 1
    return ''.join(result)


def parse_theorems(content: str) -> list[TheoremInfo]:
    """Parse .sml file content, return all theorems in order."""
    theorems = []
    lines = content.split('\n')

    # Strip comments so we don't match theorems inside (* ... *)
    stripped = _strip_comments(content)

    # Pattern for Theorem/Triviality with optional attributes
    # Matches: Theorem name:, Theorem name[simp]:, Triviality foo[local,simp]:
    header_pattern = re.compile(
        # Name allows SML-style primes, e.g. compile_correct'
        r"^(Theorem|Triviality)\s+([A-Za-z][A-Za-z0-9_']*)(?:\s*\[([^\]]*)\])?\s*:",
        re.MULTILINE
    )

    for match in header_pattern.finditer(stripped):
        kind = match.group(1)
        name = match.group(2)
        attrs_str = match.group(3)
        attributes = [a.strip() for a in attrs_str.split(',')] if attrs_str else []

        # Find line number of header
        start_pos = match.start()
        start_line = content[:start_pos].count('\n') + 1

        # Find Proof and QED after this point (in stripped to skip commented-out ones)
        rest_stripped = stripped[match.end():]
        rest = content[match.end():]

        proof_match = re.search(r'^\s*Proof\s*$', rest_stripped, re.MULTILINE)
        if not proof_match:
            continue

        qed_match = re.search(r'^\s*QED\s*$', rest_stripped, re.MULTILINE)
        if not qed_match:
            continue

        # Extract goal (between : and Proof) from original content
        goal = rest[:proof_match.start()].strip()

        # Calculate line numbers
        proof_start_line = start_line + rest[:proof_match.start()].count('\n') + 1
        proof_end_line = start_line + rest[:qed_match.start()].count('\n') + 1

        # Extract proof body and calculate its exact file offset
        proof_body_raw = rest[proof_match.end():qed_match.start()]
        proof_body_stripped = proof_body_raw.strip()
        # Calculate where the stripped body starts in the file:
        # match.end() is where 'rest' starts in content
        # proof_match.end() is where proof_body_raw starts in rest
        # leading whitespace chars = len(raw) - len(lstripped)
        leading_ws = len(proof_body_raw) - len(proof_body_raw.lstrip())
        proof_body_offset = match.end() + proof_match.end() + leading_ws

        # Check for cheat (strip comments first to avoid false positives)
        proof_no_comments = re.sub(r'\(\*.*?\*\)', '', proof_body_raw, flags=re.DOTALL)
        has_cheat = bool(re.search(r'\bcheat\b', proof_no_comments, re.IGNORECASE))

        theorems.append(TheoremInfo(
            name=name,
            kind=kind,
            goal=goal,
            start_line=start_line,
            proof_start_line=proof_start_line,
            proof_end_line=proof_end_line,
            has_cheat=has_cheat,
            proof_body=proof_body_stripped,
            proof_body_offset=proof_body_offset,
            attributes=attributes,
        ))

    # Second pass: Definition ... Termination ... End (recursive function proofs)
    def_pattern = re.compile(
        r"^(Definition)\s+([A-Za-z][A-Za-z0-9_']*)(?:\s*\[([^\]]*)\])?\s*:",
        re.MULTILINE
    )

    for match in def_pattern.finditer(stripped):
        kind = match.group(1)
        name = match.group(2)
        attrs_str = match.group(3)
        attributes = [a.strip() for a in attrs_str.split(',')] if attrs_str else []

        start_pos = match.start()
        start_line = content[:start_pos].count('\n') + 1

        rest_stripped = stripped[match.end():]
        rest = content[match.end():]

        term_match = re.search(r'^\s*Termination\s*$', rest_stripped, re.MULTILINE)
        if not term_match:
            continue  # No Termination block — plain definition, skip

        # Check that no End appears before Termination (otherwise it's a
        # plain Definition...End block, and the Termination belongs to a
        # later Definition)
        first_end = re.search(r'^\s*End\s*$', rest_stripped, re.MULTILINE)
        if first_end and first_end.start() < term_match.start():
            continue  # Plain definition — End comes before any Termination

        end_match = re.search(r'^\s*End\s*$', rest_stripped[term_match.end():], re.MULTILINE)
        if not end_match:
            continue

        # Goal is the function body between Definition header and Termination
        goal = rest[:term_match.start()].strip()

        # proof_start_line = line after "Termination"
        proof_start_line = start_line + rest[:term_match.start()].count('\n') + 1
        # proof_end_line = line of "End" (relative to after Termination)
        proof_end_line = start_line + rest[:term_match.end() + end_match.start()].count('\n') + 1

        proof_body_raw = rest[term_match.end():term_match.end() + end_match.start()]
        proof_body_stripped = proof_body_raw.strip()
        leading_ws = len(proof_body_raw) - len(proof_body_raw.lstrip())
        proof_body_offset = match.end() + term_match.end() + leading_ws

        proof_no_comments = re.sub(r'\(\*.*?\*\)', '', proof_body_raw, flags=re.DOTALL)
        has_cheat = bool(re.search(r'\bcheat\b', proof_no_comments, re.IGNORECASE))

        theorems.append(TheoremInfo(
            name=name,
            kind=kind,
            goal=goal,
            start_line=start_line,
            proof_start_line=proof_start_line,
            proof_end_line=proof_end_line,
            has_cheat=has_cheat,
            proof_body=proof_body_stripped,
            proof_body_offset=proof_body_offset,
            attributes=attributes,
        ))

    # Third pass: Resume blocks (suspended subgoal proofs)
    resume_pattern = re.compile(
        r"^(Resume)\s+([A-Za-z][A-Za-z0-9_']*)\s*\[([^\]]*)\]\s*:",
        re.MULTILINE
    )

    for match in resume_pattern.finditer(stripped):
        attrs_str = match.group(3)
        suspension_name = match.group(2)

        # First attribute is the label name; rest are proof modifiers
        attrs = [a.strip() for a in attrs_str.split(',')]
        label_name = attrs[0] if attrs else ""
        remaining_attrs = attrs[1:] if len(attrs) > 1 else []

        # Composite name for uniqueness ([ not valid in theorem names)
        name = f"{suspension_name}[{label_name}]"

        start_pos = match.start()
        start_line = content[:start_pos].count('\n') + 1

        rest_stripped = stripped[match.end():]
        rest = content[match.end():]

        qed_match = re.search(r'^\s*QED\s*$', rest_stripped, re.MULTILINE)
        if not qed_match:
            continue

        # No "Proof" keyword — body starts right after the header line's ":"
        # proof_start_line = line after the Resume header
        header_end_line = start_line + content[start_pos:match.end()].count('\n')
        proof_start_line = header_end_line + 1
        proof_end_line = start_line + rest[:qed_match.start()].count('\n') + 1

        # Extract proof body
        proof_body_raw = rest[:qed_match.start()]
        proof_body_stripped = proof_body_raw.strip()
        leading_ws = len(proof_body_raw) - len(proof_body_raw.lstrip())
        proof_body_offset = match.end() + leading_ws

        # Check for cheat
        proof_no_comments = re.sub(r'\(\*.*?\*\)', '', proof_body_raw, flags=re.DOTALL)
        has_cheat = bool(re.search(r'\bcheat\b', proof_no_comments, re.IGNORECASE))

        theorems.append(TheoremInfo(
            name=name,
            kind="Resume",
            goal="",  # Extracted at runtime from HOL session
            start_line=start_line,
            proof_start_line=proof_start_line,
            proof_end_line=proof_end_line,
            has_cheat=has_cheat,
            proof_body=proof_body_stripped,
            proof_body_offset=proof_body_offset,
            attributes=remaining_attrs,
            suspension_name=suspension_name,
            label_name=label_name,
        ))

    # Sort by file position (theorems and definitions interleaved)
    theorems.sort(key=lambda t: t.start_line)

    return theorems


def parse_file(path: Path) -> list[TheoremInfo]:
    """Parse .sml file, return all theorems."""
    content = path.read_text()
    return parse_theorems(content)



def parse_p_output(output: str) -> str | None:
    """Extract tactic script from p() output.

    p() output formats:
    1. Multi-line (proof in progress):
       > p();
       tac1 \\ tac2 >- (...) ...
       val it = () : unit

    2. Single-line (proof complete):
       val it = REWRITE_TAC[]: proof

    Returns None if output contains errors or no valid tactic script.
    """
    # Reject error output before parsing
    stripped = output.lstrip()
    if stripped.startswith('ERROR:') or stripped.startswith('Error:'):
        return None
    if 'Exception' in output or 'HOL_ERR' in output or 'No goalstack' in output or output.startswith('TIMEOUT'):
        return None

    lines = output.split('\n')
    tactic_lines = []

    for line in lines:
        stripped = line.strip()
        # Skip command echo and prompts
        if stripped.startswith('>') or stripped == 'p();':
            continue
        # Handle "val it = TACTIC: proof" format (completed proof)
        if stripped.startswith('val it = ') and ': proof' in stripped:
            tactic = stripped[len('val it = '):]
            tactic = tactic.rsplit(': proof', 1)[0].strip()
            if tactic:
                return tactic
            continue
        # Handle multi-line "val it =" format (completed proof spanning lines)
        if stripped == 'val it =':
            continue
        # Stop at other val bindings
        if stripped.startswith('val '):
            break
        # Handle ": proof" terminator for multi-line val it format
        if stripped == ': proof':
            break
        if stripped.endswith(': proof'):
            tactic_lines.append(stripped.rsplit(': proof', 1)[0].rstrip())
            break
        # Skip "OK" markers from goaltree
        if stripped == 'OK':
            continue
        # Collect tactic content
        if stripped:
            tactic_lines.append(line.rstrip())

    return '\n'.join(tactic_lines).strip() or None
