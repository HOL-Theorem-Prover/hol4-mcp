"""Quote diagnostics and automatic fixes must preserve ordinary SML text."""
import pytest

from hol4_mcp.quote_check import find_unmatched_quotes, fix_unmatched_quotes
from hol4_mcp import hol_mcp_server as srv


@pytest.mark.parametrize("source", [
    "(* author's note: ’ (* nested ‘ *) ’ *)\nval x = 1;\n",
    'val note = "apostrophe ’ and escaped \\" quote ‘";\n',
    'val note = "first ’\\\n  \\second ‘";\n',
    'val note = "(* not a comment *) ’";\n',
])
def test_comment_and_string_quotes_are_not_delimiters(tmp_path, source):
    path = tmp_path / "source.sml"
    path.write_text(source)
    assert find_unmatched_quotes(source) == []
    assert srv._quote_diagnosis_if_parse_error(path, "unrelated parse error") == []
    assert fix_unmatched_quotes(path) == 0
    assert path.read_text() == source


def test_protected_quotes_cannot_match_a_stray_code_quote(tmp_path):
    source = '(* ‘ *)\nval note = "‘";\nval x’ = ‘tm’;\n'
    path = tmp_path / "source.sml"
    path.write_text(source)
    assert find_unmatched_quotes(source) == [(3, 5, "close")]
    diagnostic = srv._quote_diagnosis_if_parse_error(path, "unknown character")
    assert any("line 3 col 6" in line for line in diagnostic)
    assert fix_unmatched_quotes(path) == 1
    assert path.read_text() == source.replace("x’", "x'")
