# `hol_send` timeout "sent interrupt" does not stop a long-running tactic; later calls, including `hol_restart`, hang behind it

**Status:** suspected; seen once, no minimal reproducer. There are two sub-issues:
(A) SIGINT did not bring HOL back to the prompt; (B) `hol_restart` queued behind the
hung call instead of replacing the session.
**Component:** `hol4_mcp/hol_session.py` `HOLSession.send` (timeout branch), `HOLSession.interrupt`,
`HOLSession.stop`; `hol4_mcp/hol_mcp_server.py` `_serialized_session`, `hol_restart`,
`hol_goals`, `hol_stop`, `hol_interrupt`.
**First seen:** 2026-10-24.

## Environment

- Session workdir `~/research/cakes/cake-pb/examples/pseudo_bool/array`, script
  `npbc_listScript.sml`, parked in theorem `vomap_rel_fast_obj_constraint` (2 goals). An assumption
  of the form `∀x. (∃y. …) ⇔ …` was in context.
- The working tree had carried an uncommitted change since 2026-10-07 that multiplies the
  default timeouts by 10, so `HOLSession.send` defaults to `timeout=50`, as does its
  post-interrupt read. This matches the `50s` in the message below.

## Observed sequence

1. `hol_send e (rpt strip_tac >> Cases_on `y` >> gvs [] >> res_tac >> gvs [] >> metis_tac [SND]);`
   returned `TIMEOUT after 50s - sent interrupt.` after about 100 s of wall time.
2. `hol_send e (rpt strip_tac >> Cases_on `y` >> gvs [] >> res_tac >> gvs []);` gave the same TIMEOUT.
3. `hol_goals` (no arguments, live session) was still running after 120 s, and the client moved it to the background.
4. `ps`: the `hol` child was at about 89 % CPU for 12 min, with 6.8 GB RSS.
5. `hol_restart` was still running after 120 s, then for more than 5 min. Meanwhile the old
   `hol` child (pid 364009, parent the hol4-mcp server) stayed at about 90 % CPU.
6. A manual `kill -TERM 364009` ended the child within 3 s, after which the session was usable again.

## Expected

After "sent interrupt", HOL abandons the tactic and returns to the prompt, so the
next call answers at once. Whatever HOL does, `hol_restart` replaces the session.

## Source reading (2026-10-28; not executed)

- (A) In `HOLSession.send`'s timeout branch, `interrupt()` (SIGINT to the process group) is
  followed by `_read_response(timeout=50)`. A wall time of 100 s means 50 s of waiting plus
  50 s for the prompt that never came, so the interrupt was not honoured within 50 s. Why
  Poly/ML did not act on SIGINT here is unknown. It could be a long stretch without an
  interrupt check, or the second probe could have started a new loop after the first was
  interrupted successfully.
- (B) `hol_restart` and `hol_goals` both carry `@_serialized_session()`, so `hol_restart` waits for
  the in-flight `hol_goals`, which was itself stuck on the busy HOL pipe. `_serialized_session`'s
  docstring says "Interrupt and stop are deliberately outside this guard so they can abort a
  running operation", and `HOLSession.stop` (SIGTERM, then SIGKILL after 5 s) would have worked,
  as the manual `kill -TERM` showed. `hol_stop` and `hol_interrupt` were **not** tried in this
  incident. So (B) may come down to which tool to use (`hol_restart` cannot preempt) rather
  than a defect. Whether `hol_restart` should preempt, or say that it is queued, is a design
  decision for the maintainer.

## Untested

- Whether `hol_interrupt` or `hol_stop` would have recovered the session at step 3.
- Whether a single looping `gvs`/`res_tac` probe on a small goal reproduces (A).

## Impact

The session was unusable for more than 12 min until the process was killed by hand.

## Workaround

`hol_stop` (not serialized). Failing that, kill the `hol` child by hand.

## Acceptance

- (A) A test with a deliberately non-terminating tactic sent via `hol_send` with a short
  timeout. After the TIMEOUT, the next `hol_send "1;"` answers promptly, or the tool states
  that HOL is still busy and names the recovery tool.
- (B) A test or decision record for `hol_restart` while another call on the same session is
  blocked.
