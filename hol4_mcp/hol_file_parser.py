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
    """Find and parse a JSON object in HOL output.

    HOL may print warnings, val bindings, or other output before the JSON.
    This handles two cases:
    1. A line starting with a JSON object (common case)
    2. A JSON object embedded after other output (e.g., "metis: {\"ok\":...}")

    Args:
        output: Raw output from HOL
        context: Description for error messages (e.g., "linearize_with_spans_json")

    Returns:
        Parsed JSON object

    Raises:
        HOLParseError if no valid JSON object found
    """
    import json

    markers = ['{"ok":', '{"err":']

    for line in output.strip().split('\n'):
        stripped = line.strip()
        # Try exact line match first (most common case)
        if stripped.startswith('{'):
            try:
                return json.loads(stripped)
            except json.JSONDecodeError:
                pass
        # Then look for embedded JSON after other output
        for marker in markers:
            idx = stripped.find(marker)
            if idx >= 0:
                try:
                    return json.loads(stripped[idx:])
                except json.JSONDecodeError:
                    pass

    # Include snippet of raw output in error for debugging
    preview = output.strip()[:200]
    raise HOLParseError(
        f"No JSON object found in {context} output. Raw output: {preview}"
    )


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


def _needs_infix_parens(text: str) -> bool:
    """Whether tactic text needs parens to avoid SML infix parsing issues.

    SML infix operators like >-, >>-, >>>- at expression start cause parse errors
    when used inside ef(goalFrag.expand(...)). Wrapping in parens prevents
    the SML parser from treating them as infix.
    """
    return bool(re.match(r'\s*>{1,3}-', text))


def _frag_to_cmd(kind: str, text: str) -> str:
    """Wrap a fragment (type, text) into an SML ef() command string.

    - expand: ef(goalFrag.expand(<text>));  (parens added if text starts with >-)
    - expand_list: ef(goalFrag.expand_list(<text>));  (for >~ pattern selectors)
    - open/mid/close: ef(goalFrag.<text>);
    """
    if kind == "expand":
        inner = f"({text})" if _needs_infix_parens(text) else text
        return f"ef(goalFrag.expand({inner}));"
    elif kind == "expand_list":
        return f"ef(goalFrag.expand_list({text}));"
    else:
        return f"ef(goalFrag.{text});"


@dataclass
class StepPlan:
    """A step with its end offset and fragment data."""
    end: int       # End offset in proof body
    kind: str      # Fragment type: "expand", "expand_list", "open", "mid", "close"
    text: str      # Raw tactic text or goalFrag function name

    @property
    def cmd(self) -> str:
        """SML ef() command to execute this step."""
        return _frag_to_cmd(self.kind, self.text)


def step_line_numbers(
    step_plan: list[StepPlan], proof_body_offset: int, content: str
) -> list[int]:
    """Compute 1-indexed source line number for each step in step_plan.

    A step starts at the end of the previous step (or proof_body_offset for step 0).
    """
    lines = []
    for i, step in enumerate(step_plan):
        if i == 0:
            start_offset = proof_body_offset
        else:
            start_offset = proof_body_offset + step_plan[i - 1].end
        line = _offset_to_line(start_offset, content)
        lines.append(line)
    return lines


def _offset_to_line(offset: int, content: str) -> int:
    """Convert byte offset in content to 1-indexed line number."""
    return content[:offset].count('\n') + 1


# Display names for structural step kinds (hide SML plumbing)
_STEP_DISPLAY = {
    "open": ">-",
    "mid": ">>-",
    "expand_list": ">~",  # >~[pat] >- tac shown as single step
}


def format_steps(
    step_plan: list[StepPlan],
    fail_idx: int | None = None,
    trace_data: list | None = None,
    step_lines: list[int] | None = None,
    context_before: int = 0,
    context_after: int = 0,
) -> list[str]:
    """Format step plan with indentation for >- arm nesting.

    - expand steps show raw tactic text at current depth
    - open steps show ">-" and increase nesting depth (arm start)
    - mid steps show ">>-" and increase nesting depth (ThenL arm start)
    - close steps are hidden (indent decrease is the visual)
    - >> chain tactics stay at same depth (sequential, not nested)

    With trace_data: appends "Nms  X→Y" timing/goals per step.
    With step_lines + context_before/after: shows only steps near fail_idx.

    Args:
        step_plan: List of StepPlan entries.
        fail_idx: Index of the failing step, or None if proof succeeded.
        trace_data: List of TraceEntry objects (index-aligned with step_plan).
                    If provided, adds timing and goal annotations.
        step_lines: 1-indexed line numbers for each step (from step_line_numbers).
                    Required for context_before/after filtering.
        context_before: Number of source lines before the failure to include.
        context_after: Number of source lines after the failure to include.

    Returns:
        Lines of formatted output.
    """
    # When context filtering is requested, determine step range
    if (context_before > 0 or context_after > 0) and fail_idx is not None and step_lines:
        if fail_idx < 0 or fail_idx >= len(step_plan):
            return []
        fail_line = step_lines[fail_idx]
        lo = fail_line - context_before
        hi = fail_line + context_after
        start = fail_idx
        for i in range(fail_idx - 1, -1, -1):
            if step_lines[i] < lo:
                break
            start = i
        end = fail_idx + 1
        for i in range(fail_idx + 1, len(step_plan)):
            if step_lines[i] > hi:
                break
            end = i + 1
    else:
        start = 0
        end = len(step_plan)

    # Precompute depth at `start`
    depth = 0
    for i in range(start):
        k = step_plan[i].kind
        if k == "close":
            depth = max(0, depth - 1)
        elif k in ("open", "mid"):
            depth += 1

    out = []
    for i in range(start, end):
        step = step_plan[i]
        k = step.kind

        if k == "close":
            # Hidden — indent decrease is the visual
            depth = max(0, depth - 1)
            continue

        indent = "  " * depth
        marker = "  <-- FAILED" if i == fail_idx else ""
        if k == "expand_list":
            # >~[pat] >- tac shown as single indented step
            display = step.text
        elif k in _STEP_DISPLAY:
            display = _STEP_DISPLAY[k]  # >-/>>- for structural
        else:
            display = step.text  # raw tactic text for expand

        # Timing/goals annotation
        annotation = ""
        if trace_data is not None and i < len(trace_data):
            entry = trace_data[i]
            ms = entry.real_ms
            gb = entry.goals_before if entry.goals_before is not None else "?"
            ga = entry.goals_after if entry.goals_after is not None else "?"
            annotation = f"  {ms}ms  {gb}→{ga}"

        out.append(f"{indent}{i}: {display}{annotation}{marker}")

        # Increase depth AFTER open/mid (their children go deeper)
        if k in ("open", "mid"):
            depth += 1

    return out


def format_step_context(
    step_plan: list[StepPlan],
    fail_idx: int,
    step_lines: list[int],
    context_before: int = 0,
    context_after: int = 0,
) -> list[str]:
    """Format step plan context around a failing step.

    Thin wrapper around format_steps for backward compatibility.
    """
    if fail_idx < 0 or fail_idx >= len(step_plan):
        return []

    failing_text = step_plan[fail_idx].text
    # Use structural display name if it's an open/mid step
    failing_display = _STEP_DISPLAY.get(step_plan[fail_idx].kind, failing_text)
    out = ["", "=== Failing tactic ===", failing_display]

    if context_before <= 0 and context_after <= 0:
        return out

    steps = format_steps(
        step_plan, fail_idx=fail_idx,
        step_lines=step_lines,
        context_before=context_before, context_after=context_after,
    )
    if steps:
        out.append("")
        out.append("=== Steps around failure ===")
        out.extend(steps)
    return out


def parse_step_plan_output(output: str) -> list[StepPlan]:
    """Parse JSON output from step_plan_json.

    Expects: {"ok":[{"end":N,"type":"expand","text":"..."}, ...]} or {"err":"message"}
    Returns: list of StepPlan objects, one per executable step.
    Raises: HOLParseError if HOL4 returned an error or output is malformed.
    """
    result = _find_json_line(output, "goalfrag_step_plan_json")

    if 'ok' in result:
        try:
            steps = []
            for item in result['ok']:
                end = int(item['end'])
                kind = str(item['type'])
                text = str(item['text'])
                steps.append(StepPlan(end=end, kind=kind, text=text))
            return steps
        except (TypeError, ValueError, KeyError) as e:
            raise HOLParseError(f"Malformed step plan in output: {e}") from e
    elif 'err' in result:
        raise HOLParseError(f"goalfrag_step_plan_json: {result['err']}")
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


@dataclass
class LocalBlock:
    """An SML local ... in ... end block spanning lines."""
    local_line: int   # Line of 'local' keyword (1-indexed)
    in_line: int      # Line of 'in' keyword (1-indexed)
    end_line: int     # Line of 'end' keyword (1-indexed)


def parse_local_blocks(content: str) -> list[LocalBlock]:
    """Parse SML local ... in ... end blocks from file content.

    Uses comment-stripped and string-stripped content to avoid false matches.
    Returns blocks sorted by local_line.
    """
    stripped = _strip_comments(content)
    stripped = _strip_strings(stripped)

    blocks = []
    # Stack entries: ('local', local_line, in_line) or ('let',) etc.
    # All SML block openers that require 'end' must be tracked so 'end'
    # pops the innermost opener, not just the nearest 'local'.
    stack: list[tuple] = []
    lines = stripped.split('\n')

    # Word-boundary patterns — match anywhere in line, not just at start.
    # SML 'let' commonly appears mid-line (e.g. "fun f x = let ...").
    local_re = re.compile(r'\blocal\b')
    in_re = re.compile(r'\bin\b')
    let_re = re.compile(r'\blet\b')
    end_re = re.compile(r'\bend\b')

    for line_num, line in enumerate(lines, start=1):
        # Find all keywords in order of appearance on this line.
        # Sort by position to handle cases like "let ... in ... end" on one line
        # or "local ... in" on one line.
        keywords = []
        for m in local_re.finditer(line):
            keywords.append((m.start(), 'local'))
        for m in in_re.finditer(line):
            keywords.append((m.start(), 'in'))
        for m in let_re.finditer(line):
            keywords.append((m.start(), 'let'))
        for m in end_re.finditer(line):
            keywords.append((m.start(), 'end'))
        keywords.sort()

        if not keywords:
            continue

        for _, kw in keywords:
            if kw == 'local':
                stack.append(('local', line_num, 0))
            elif kw == 'let':
                stack.append(('let',))
            elif kw == 'in':
                # 'in' closes the most recent opener (local or let)
                # For 'local', we record the in_line; for 'let', we just
                # note it so a subsequent 'end' pops the right layer.
                if stack and stack[-1][0] in ('local', 'let') and not _has_in(stack[-1]):
                    entry = stack.pop()
                    if entry[0] == 'local':
                        stack.append(('local', entry[1], line_num))
                    else:
                        stack.append(('let', line_num))
            elif kw == 'end':
                if stack:
                    entry = stack.pop()
                    if entry[0] == 'local' and entry[2] > 0:
                        blocks.append(LocalBlock(
                            local_line=entry[1],
                            in_line=entry[2],
                            end_line=line_num,
                        ))
                    # 'let' entries are just discarded — inner block closed

    return blocks


def _has_in(entry: tuple) -> bool:
    """Check if a stack entry already has its 'in' recorded."""
    if entry[0] == 'local':
        return entry[2] > 0
    if entry[0] == 'let':
        return len(entry) > 1 and entry[1] > 0
    return False


def _strip_strings(content: str) -> str:
    """Replace SML string literals with spaces, preserving newlines.

    Preserves character offsets so that line calculations on the result
    match the original content. Handles escaped quotes (\"\").
    """
    result = list(content)
    i = 0
    n = len(content)
    while i < n:
        if content[i] == '"':
            # Found string start
            j = i + 1
            while j < n:
                if content[j] == '\\' and j + 1 < n:
                    j += 2  # Skip escaped character
                elif content[j] == '"':
                    j += 1  # Include closing quote
                    break
                elif content[j] == '\n':
                    # SML strings can't span lines without \  at end
                    break
                else:
                    j += 1
            # Blank out i..j, keeping newlines
            for k in range(i, min(j, n)):
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

        proof_match = re.search(r'^[^\S\n]*Proof(?:\[.*?\])?[^\S\n]*$', rest_stripped, re.MULTILINE)
        if not proof_match:
            continue

        qed_match = re.search(r'^[^\S\n]*QED[^\S\n]*$', rest_stripped, re.MULTILINE)
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

        term_match = re.search(r'^[^\S\n]*Termination[^\S\n]*$', rest_stripped, re.MULTILINE)
        if not term_match:
            continue  # No Termination block — plain definition, skip

        # Check that no End appears before Termination (otherwise it's a
        # plain Definition...End block, and the Termination belongs to a
        # later Definition)
        first_end = re.search(r'^[^\S\n]*End[^\S\n]*$', rest_stripped, re.MULTILINE)
        if first_end and first_end.start() < term_match.start():
            continue  # Plain definition — End comes before any Termination

        end_match = re.search(r'^[^\S\n]*End[^\S\n]*$', rest_stripped[term_match.end():], re.MULTILINE)
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

        qed_match = re.search(r'^[^\S\n]*QED[^\S\n]*$', rest_stripped, re.MULTILINE)
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
