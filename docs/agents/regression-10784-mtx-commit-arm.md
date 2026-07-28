# GH #10784 regression gate: MTx commit arm vs failed-tx SELFDESTRUCT

**Status: LATENT (measured).** The defect fires on every failing
post-preparation transaction and is unobservable in the post-state. This gate
pins the mechanism so an unrelated change cannot silently make it live.

- Gate runner: `scripts/gate-10784-mtx-commit-arm.py` (run from repo root;
  docstring has the full construction and the instrumented-probe recipe).
- Fixtures (fill file): `scripts/fill/test_10784_mtx_commit_arm.py`.

## The defect

`BlockVerdictMtxRuntime.lean:615`: the per-tx account-state epilogue takes
the COMMIT arm when the tx status is nonzero **or**
`runtime_tx_post_preparation_reached` is set. Only the fall-through arm
clears `account_state_pending/created/delete_count`, and the depth-0 rollback
does not restore those counters. A SELFDESTRUCT queued by a transaction that
later fails at top level is therefore consumed by the commit arm.

## The measurement

Corpus search found no ready-made fixture (eip6780_selfdestruct families are
child-frame reverts or pre-existing targets; eip8246 initcode selfdestructs
are top-level successes), so three fixtures were constructed with `fill`
(in-repo EELS t8n) — all valid blocks:

| fixture | shape | commit arm | post-prep flag | pending / created / delete at commit-arm entry | roots match spec |
|---|---|---|---|---|---|
| fx1 | same-tx-created A selfdestructs, tx REVERTs at top level | yes (17) | 1 | 7 / 1 / **1** | byte-for-byte |
| fxA | pre-existing A selfdestructs, tx REVERTs at top level | yes (17) | 1 | 4 / 0 / 0 | byte-for-byte |
| fxB | A deployed in tx1, selfdestructs in tx2, tx2 REVERTs | yes (17) | 1 | 2 / 0 / 0 | byte-for-byte |

Pristine-channel results on all three: guest succ byte = 1, guest output ==
fixture `statelessOutputBytes`, probe verdict = 1, bv_fail = 0,
`sv_recomputed` == declared `blockHeader.stateRoot` (byte-for-byte).

## Why latent — the two load-bearing conditions

1. **Delete-queue insertion is gated on created-in-same-tx**
   (`NoopHalt.lean:520-600`, EIP-6780 semantics). fxA/fxB prove it: delete=0
   at commit-arm entry for pre-existing and prior-tx-created targets.
2. **The depth-0 rollback removes everything a failed tx created.** fx1
   proves it: created=1, delete=1 at commit-arm entry — the destroy IS queued
   for the failed tx and IS consumed by the wrong arm — yet the post-state
   root matches the spec byte-for-byte, because committing the delete removes
   an already-absent account (a trie no-op).

If either condition changes, the probe numbers move and the gate fires. That
is why the gate asserts the instrumented-probe numbers **together with**
byte-exact root agreement, not the root alone: the root is no-op-identical
*by* the mechanism under test, so a root-only check would pass forever and
measure nothing.

## Direction verdict (for the issue)

All three a-priori hypotheses were refuted by measurement: not a false
reject, not a second false accept, and the route is not unreachable — it
fires on every failing post-preparation tx. The true state is a fourth:
**fires and unobservable**. No guest change is behaviorally forced today, but
the arm-selection disjunct should still be corrected for the same reason as
its storage twin, and this gate should run before any change touching
delete-queue gating or depth-0 rollback.
