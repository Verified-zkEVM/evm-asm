# Rollback witness KATs

These fixtures are the two read/write rollback witnesses for GH #11256.  Both
cases use `DELEGATECALL`, so the child runs in the parent storage context.
The child reads slot `1`, writes slot `0` to `1`, and then either reverts or
stops.  The parent ignores the child status, reads slot `0`, and returns it.

- `under_restore_child_reverts`: slot `0` must be absent after the transaction,
  while the parent BAL retains reads of slots `1` and `0`.
- `over_restore_child_succeeds`: slot `0` must persist with value `1`, while
  the independent read of slot `1` remains visible.

Slot `1` is deliberately distinct from slot `0`; the BAL omits a read that is
also represented in the storage-change list.

The JSON was generated with `test_rollback_witness_kat.py` using
`execution-specs` revision `e5a8caf1b8055e4d805c7fb169edfa710914b7da`.  The
reference fill passed both cases, and the byte-level converter reproduced both
reference outputs with `--verify-input-parity --verify-execution-spec-input
--verify-run-stateless-guest`.

## Current guest baseline

The exact-main `codegen` build completed successfully before emission.  The
emitted guest was tested with stock `ziskemu 0.16.0`
(`f4e612e`, 2026-06-11) using one job:

```text
guest SHA-256: 00225b05fd14a83a245bc0c8b79581f4e7911fa8462a6f23e233117844421f9a
selected: 2    errored: 0    fail: 0
full match: 2  root match: 2  successful_validation match: 2  tail match: 2
```

No rollback mechanism changes are included in this fixture-only change.
