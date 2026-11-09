"""A step-plan request that runs out of time is reported as a timeout, not as
a parse failure of the proof text (P5, C3)."""
from hol4_mcp.hol_cursor import FileProofCursor

SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "spt";

Theorem st:
  !x:num. x + 0 = x
Proof
  gen_tac >>
  simp[]
QED

val _ = export_theory();
"""


class _StepPlanTimesOut:
    """Answers the step-plan request with the session's TIMEOUT text."""

    async def send(self, command, timeout=None):
        if "goalfrag_step_plan_json" in command:
            return "TIMEOUT after 1s - sent interrupt."
        return ""


async def test_step_plan_timeout_is_reported_as_a_timeout(tmp_path):
    script = tmp_path / "sptScript.sml"
    script.write_text(SCRIPT)
    cursor = FileProofCursor(script, _StepPlanTimesOut())
    cursor._reparse_if_changed()
    result = await cursor._reparse_steps_on_edit(cursor._get_theorem("st"))
    assert result.error.startswith("TIMEOUT computing the step plan"), result.error
    assert "parse step plan" not in result.error, result.error
