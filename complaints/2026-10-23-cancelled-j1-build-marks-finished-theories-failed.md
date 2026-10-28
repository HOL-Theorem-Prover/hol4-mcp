# Cancelling a long `jobs=1` build left every theory it had finished flagged as a partial artifact

**Status:** suspected; seen once. The mechanism first proposed is **refuted** for
this occurrence (see Source reading), so the cause is unknown. The log and the
`*.failed.json` records have since been deleted.
**Component:** build coordination: `hol4_mcp/build_coordination.py`
(`completed_outputs`, `job_verdicts`, `finalize`, `finalize_job`,
`BuildClaims.finish`) and `hol_build_status(cancel=True)`.
**First seen:** 2026-10-23.

## Observed sequence

1. `holmake(workdir=~/research/cakes/cake-pb/examples/pseudo_bool/array/compilation/proofs,
   target="npbc_fullProofTheory.uo", heap_size=40000, jobs=1, detach=True)` started job
   `ce03524a940f`, which planned 100 theories, mostly compiler backend proofs.
2. After 1605 s, while it was building `data_spaceProof`:
   `hol_build_status(job="ce03524a940f", cancel=True)`.
3. The next `holmake` on the same target refused:
   `ERROR: job=ce03524a940f … left a possibly partial or unverified artifact:
   …/compiler/backend/.hol/objs/word_elimTheory.ui. No build was started.`
4. The coordination state held 70 `*.failed.json` records for the job, covering 35 theories:
   `compiler/backend/semantics` ×20, `gc` ×5, `proofs` ×5, `semantics/proofs` ×3,
   `word_elim`, `asmSigned`. The job log showed that every one of them had finished
   before the cancel, with `Exporting theory "<thy>" ... done.` and a progress line
   such as `Holmake: [↓99] word_elim`, 26 min before the cancel in the case of `word_elim`.

## Expected

Progress and verdict lines in a cancelled build's log certify the theories they
name, which is what the `completed_outputs` docstring says. Only the theory being
built at the moment of the cancel (`data_spaceProof`) should be suspect.

## Evidence still available

- `/var/tmp/hol4-mcp-1000/jobs/ce03524a940f.json` records
  `"finalized": {"returncode": -15, …}`, with tags including `word_elimTheory`,
  `data_spaceProofTheory` and `word_elimProofTheory` (100 tags, 1002 outputs).
- The log `/var/tmp/hol4-mcp-1000/builds/ce03524a940f.log` is gone, and the `*.failed.json`
  records were removed by the workaround.

## Source reading (2026-10-28)

- The first report assumed that a cancel arrives with `returncode=None`, which
  would skip `completed_outputs`. That is wrong here: `returncode` was **-15**
  (SIGTERM), so the cancel went through the in-process reaper
  (`hol_mcp_server.py` `_reap`, then `build_claims.finish(claim, output)`, where `output`
  is the full log via `_read_log_tail(log, 0)`). `-15` is truthy, so
  `completed_outputs` **was** called.
- Fed a synthetic log, `completed_outputs` certifies the finished theory:
  `completed_outputs({'word_elimTheory': {…}}, set(), "Holmake: [↓99] word_elim\n", -15)`
  returns `word_elimTheory.ui`, because `_J1_THEORY_DONE_RE` matches and `"OK"` is in `_SUCCESS_VERDICTS`.
- So the real log must have differed from that assumption, or something else happened. Candidate causes:
  (a) the progress lines had extra text (ANSI codes, `\r` redraws, a trailing suffix) that
  `^(?:Holmake: )?\[(?:\d+/\d+|↓\d+)\] (\S+)\s*$` rejects;
  (b) the server process was started before commit `d870268` (2026-10-07, "Recognise a
  sequential build's theory progress lines") and was running older code;
  (c) the refusal came from a different check, such as the `before` snapshot or an
  `in_process` output, not from missing verdicts.
- A separate defect, found by reading only: the **adopted** cancel path
  (`_adopted_build_status`, for a job started by an earlier server) calls
  `finalize_job(record, returncode, full)` with `returncode` `None` when no exit status
  was written. `finalize_job` then sets `completed = set()` (`if returncode else set()`), so
  verdict lines are ignored, which contradicts the `completed_outputs` docstring. This
  path did not run in this occurrence.

## Impact

After cancelling a long sequential build, every theory it finished has to be
removed and rebuilt before the target will build again. Here that was about
26 min of backend proofs. No result was wrong.

## Workaround

Delete the flagged `.ui`/`.uo` outputs, as the error message suggests, and rebuild.

## Acceptance

- Reproduce: a detached `jobs=1` build of a few small theories (test fixtures), cancel it
  partway, then check that finished theories are not flagged. Copy the job log
  out of `/var/tmp/hol4-mcp-1000/builds/` before it is pruned.
- Add a unit test of the adopted path: `finalize_job(record, None, log_with_progress_lines)`
  certifies the theories that the progress lines name.
