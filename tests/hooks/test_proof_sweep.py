"""proof_sweep B3 (`check_impl`): `impl_tac >- NORM >> NORM` and a single
normaliser in a parenthesised arm are hits; a parenthesised arm holding a
chain is not, since all its steps run on the antecedent's goal."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "hooks"))
from proof_sweep import check_impl  # noqa: E402

NO_HIT = [
    pytest.param(["  >> impl_tac >- (rw [] >> first_x_assum irule >> metis_tac [])",
                  "  >> rw []"], id="one-line-chain-arm"),
    pytest.param(["  >> impl_tac >- (",
                  "    rw [] >> first_x_assum irule",
                  "    >> rw [] >> gvs [exp_free_names_def] >> metis_tac [])",
                  "  >> rw []"], id="multi-line-chain-arm"),
]

HIT = [
    pytest.param(["  >> impl_tac >- rw [] >> gvs []"], id="bare"),
    pytest.param(["  >> impl_tac >- (rw []) >> gvs []"], id="parenthesised-single"),
    pytest.param(["  >> impl_tac", "  >- simp [] >> fs []"], id="bare-across-lines"),
    pytest.param(["  >> impl_tac >- rw [Once (f x)] >> gvs []"], id="parenthesised-argument"),
]


@pytest.mark.parametrize("lines", NO_HIT)
def test_chain_inside_parenthesised_arm_is_not_a_hit(lines):
    assert check_impl(lines + [""], 1) == []


@pytest.mark.parametrize("lines", HIT)
def test_normaliser_then_normaliser_is_a_hit(lines):
    hits = check_impl(lines + [""], 1)
    assert [ln for ln, _ in hits] == [1], hits
