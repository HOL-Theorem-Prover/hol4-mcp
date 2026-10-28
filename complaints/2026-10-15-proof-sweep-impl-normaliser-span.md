# proof_sweep B3 (`check_impl`) flags normalisers that are both inside one parenthesised `impl_tac` arm

**Status:** confirmed (reproduced at function level, 2026-10-28; no HOL needed).
**Component:** `hooks/proof_sweep.py` `check_impl` (check B3). Imported by
`hooks/h25_proof_text_sweep.py`, `hooks/h27_commit_audit_gate.py`,
`hooks/h7_holmake_advisory.py`.
**First seen:** 2026-10-15, H27 commit audit on
`compiler/backend/proofs/source_lift_constsProofScript.sml` (cake-imul, branch `lift_constants`).

## Summary

B3 is meant to catch `impl_tac >- NORM >> NORM`: one normaliser closes the
antecedent, a second runs on the remaining goal, and one assumption-using
normaliser could do both. It also fires when both normalisers are inside the same
parenthesised arm `impl_tac >- ( NORM >> … >> NORM )`, where they run in sequence
on one goal and the hint makes no sense. This is a false positive.

## Reproducer

```bash
cd ~/hol4-mcp/hooks && python3 -I -c "
import sys; sys.path.insert(0, '.')
import proof_sweep as p
print(p.check_impl(['  >> impl_tac >- (rw [] >> first_x_assum irule >> metis_tac [])',
                    '  >> rw []'], 1))"
```

Observed: one B3 hit on line 1. Expected: no hit, because the arm is the whole
parenthesised chain.

The original field shape (multi-line arm) also triggers:

```
  >> impl_tac >- (
    rw [] >> first_x_assum irule
    >> rw [] >> gvs [exp_free_names_def] >> metis_tac [])
  >> rw []
```

The intended positive, `impl_tac >- rw []` / `>> gvs []`, still fires correctly
and must keep firing.

## Source reading

`check_impl` joins a 3-line window and matches
`(impl_tac|impl_keep_tac)\s*(?:>-|THEN1)\s*\(?\s*(NORM)\b[^)]*\)?\s*(?:>>|\\\\)\s*(NORM)\b`.
The optional `\(?`, then `[^)]*`, lets the match run from the arm's first
normaliser across the arm's own `>>` steps to a later normaliser inside the same
parentheses. Nothing checks whether the second normaliser lies after the arm's
closing `)`.

## Impact

An advisory-only hook hint (H25/H27/H7) that suggests merging normalisers which
are not on different goals. Following it could lead an agent to restructure a
correct proof. There is no wrong verdict.

## Acceptance

- Add a test to `tests/hooks/` (there is no proof_sweep test file yet) covering:
  the single-line and multi-line parenthesised arms above (no hit), and the bare
  `impl_tac >- rw [] >> gvs []` form (hit).
- Decide, and state in the `check_impl` docstring, whether a parenthesised arm
  that holds a single normaliser, as in `impl_tac >- (rw []) >> gvs []`, is in scope.
