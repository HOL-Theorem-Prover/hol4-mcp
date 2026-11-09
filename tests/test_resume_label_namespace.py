"""Resume headers take ONE label level; labels are flat per theorem.

A Resume block's own name is the composite `thm[label]`, so a diagnostic that
interpolates the ACTIVE theorem name into a suggested header emits
`Resume thm[a][X]:` once you are already inside a Resume body. That does not
match the Resume pattern, and the block it heads is invisible to the parser —
navigating to it reports "not within any theorem" rather than a syntax error,
which is why it reads as a lost suspension.

`suspension_base` is the fix every such message must go through.
"""

from hol4_mcp.hol_file_parser import parse_theorems, suspension_base

SCRIPT = """\
Theorem calls_correct:
  T
Proof
  conj_tac
  >~ [`Install`] >- suspend "Install"
QED

%s
  cheat
QED

Finalise calls_correct;
"""


def names(src):
    return [t.name for t in parse_theorems(src)]


class TestSuspensionBase:
    def test_strips_the_label(self):
        assert suspension_base("calls_correct[Install]") == "calls_correct"

    def test_plain_name_unchanged(self):
        assert suspension_base("calls_correct") == "calls_correct"

    def test_only_the_first_level_is_stripped(self):
        assert suspension_base("thm[a][b]") == "thm"

    def test_idempotent(self):
        once = suspension_base("calls_correct[Install]")
        assert suspension_base(once) == once


class TestResumeHeaderParsing:
    def test_flat_header_is_parsed(self):
        assert "calls_correct[Install]" in names(SCRIPT % "Resume calls_correct[Install]:")

    def test_nested_header_is_invisible_to_the_parser(self):
        """The shape a name-interpolating message used to suggest."""
        parsed = names(SCRIPT % "Resume calls_correct[Install][impl]:")
        assert not any(n.startswith("calls_correct[") for n in parsed), parsed

    def test_header_built_via_suspension_base_is_parsed(self):
        active = "calls_correct[Install]"          # already inside a Resume body
        header = f"Resume {suspension_base(active)}[impl]:"
        assert "calls_correct[impl]" in names(SCRIPT % header)


class TestDiagnosticsUseTheBase:
    """Every runtime message that builds a Resume header must route the
    theorem name through suspension_base, or it breaks inside a Resume body."""

    def test_no_message_interpolates_a_raw_active_theorem(self):
        import re
        from pathlib import Path
        src_dir = Path(__file__).parent.parent / "hol4_mcp"
        offenders = []
        # `Resume {name}[` where name is neither wrapped in suspension_base(...)
        # nor a `.suspension_name` field (already the base, by construction).
        bad = re.compile(
            r"Resume \{(?!suspension_base)[A-Za-z_][\w.]*\}\[")
        ok_suffix = re.compile(r"Resume \{[\w.]*\bsuspension_name\}\[")
        for py in src_dir.glob("*.py"):
            for i, line in enumerate(py.read_text().splitlines(), 1):
                if bad.search(line) and not ok_suffix.search(line):
                    offenders.append(f"{py.name}:{i}: {line.strip()}")
        assert not offenders, "\n".join(offenders)
