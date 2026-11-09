"""Detect and fix mismatched Unicode smart quotes in HOL4 sources.

U+2018 (LEFT SINGLE QUOTATION MARK) opens and U+2019 (RIGHT SINGLE
QUOTATION MARK) closes a HOL4 term quotation — matched pairs are valid and
must be left alone. An UNMATCHED smart quote (usually a U+2019 pasted where
an ASCII apostrophe belongs, e.g. in a variable name like x') breaks the
lexer with errors like "unknown character"; the fix is replacing it with
ASCII '.
"""

from pathlib import Path

from .hol_file_parser import _strip_comments, _strip_strings

OPEN_Q = '‘'
CLOSE_Q = '’'


def find_unmatched_quotes(text: str) -> list[tuple[int, int, str]]:
    """Return (line, col, 'open'|'close') for unmatched code smart quotes.

    SML comments and strings are ordinary text, not quotation delimiters.

    Lines are 1-indexed, columns 0-indexed (matching the historical
    check_quotes.py output, which printed col as 0-indexed).
    """
    quotes = []  # (line_1indexed, col_0indexed, kind)
    code = _strip_strings(_strip_comments(text))
    for li, line in enumerate(code.split('\n')):
        for col, ch in enumerate(line):
            if ch == OPEN_Q:
                quotes.append((li + 1, col, 'open'))
            elif ch == CLOSE_Q:
                quotes.append((li + 1, col, 'close'))

    matched = set()
    stack = []
    for i, (_, _, kind) in enumerate(quotes):
        if kind == 'open':
            stack.append(i)
        elif stack:
            matched.add(stack.pop())
            matched.add(i)
    return [q for i, q in enumerate(quotes) if i not in matched]


def fix_unmatched_quotes(path: Path) -> int:
    """Replace unmatched smart quotes in the file with ASCII '.

    Returns the number of quotes fixed.
    """
    path = Path(path)
    text = path.read_text(encoding='utf-8')
    unmatched = find_unmatched_quotes(text)
    if not unmatched:
        return 0
    lines = text.split('\n')
    for li, col, _ in reversed(unmatched):  # reverse to preserve positions
        line = lines[li - 1]
        lines[li - 1] = line[:col] + "'" + line[col + 1:]
    path.write_text('\n'.join(lines), encoding='utf-8')
    return len(unmatched)


def quote_diagnosis_lines(file_path, max_reports: int = 5) -> list[str]:
    """Diagnosis lines for tool error paths (empty when nothing to report)."""
    try:
        text = Path(file_path).read_text(encoding='utf-8')
    except OSError:
        return []
    unmatched = find_unmatched_quotes(text)
    if not unmatched:
        return []
    out = []
    for li, col, kind in unmatched[:max_reports]:
        out.append(
            f"unmatched smart quote ({kind} {OPEN_Q if kind == 'open' else CLOSE_Q}) "
            f"at line {li} col {col + 1}"
        )
    if len(unmatched) > max_reports:
        out.append(f"... and {len(unmatched) - max_reports} more")
    out.append(
        f"Likely cause of the parse error — fix with: "
        f"python3 -m hol4_mcp.quote_check {file_path} --fix"
    )
    return out


def main(argv: list[str]) -> int:
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__)
        print("Usage: python3 -m hol4_mcp.quote_check <file> [--fix]")
        return 0
    fname = argv[0]
    fix = '--fix' in argv[1:]
    text = Path(fname).read_text(encoding='utf-8')
    unmatched = find_unmatched_quotes(text)
    for li, col, kind in unmatched:
        label = f'open {OPEN_Q}' if kind == 'open' else f'close {CLOSE_Q}'
        line = text.split('\n')[li - 1]
        print(f"Line {li}, col {col}: unmatched {label}: {line.rstrip()}")
    if fix and unmatched:
        n = fix_unmatched_quotes(Path(fname))
        print(f"Fixed {n} unmatched quote(s)")
    elif not unmatched:
        print("No unmatched quotes found")
    return 0


if __name__ == '__main__':
    import sys
    sys.exit(main(sys.argv[1:]))
