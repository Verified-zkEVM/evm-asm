# BAL producer differential probe

This probe is a tooling-only check of the final BAL-builder rows in the
emitted guest. It does not change the guest or feed guest rows into SpecRef.
The guest runs on SPIKE; the reference rows are decoded from the pinned
execution-specs Amsterdam `BlockAccessList` in the fixture payload and are
pre-registered in
[`scripts/spike/bal-balance-changes.expectation.json`](../scripts/spike/bal-balance-changes.expectation.json).

The first registered fixture is
`bal_balance_changes.json` (manifest label
`00318_test_bal_balance_changes_fork_Amsterdam-blockchain_test__b0`). It
exercises nine account rows, two storage rows, three balance rows, and one
nonce row. The expectation records the execution-specs pin and the input
SHA-256; regenerate it only when deliberately changing the fixture:

```bash
uv run --directory execution-specs --quiet python3 ../scripts/spike/bal_producer_diff.py \
  --register-expectation \
  --spike ../scripts/spike/spike_run \
  --guest-elf ../gen-out/regionmap/stateless_guest.elf \
  --manifest /var/tmp/fc668/manifest.tsv \
  --label 00318_test_bal_balance_changes_fork_Amsterdam-blockchain_test__b0 \
  --expectation ../scripts/spike/bal-balance-changes.expectation.json \
  --out-dir /tmp/bal-producer-diff
```

The run supplies `SPIKE_DUMP_RANGES` from the ELF's `nm` symbols and the row
sizes/capacities from `BlockAccessListBuilder.lean`. It reports attempted,
decoded, skipped, undecodable, overflow, and final row counts. Any skipped or
undecodable row is a hard failure. It also requires the final rebuilt BAL hash
to equal the supplied BAL hash. `SPIKE_COMMITLOG` remains a separate
attempted-write audit and is not used as the producer extraction.

The tracked `fixtures/kat` JSONs are intentionally mutated reject-side KATs;
they are not a clean producer oracle for this check. The approved 26,104-row
manifest under `/var/tmp/fc668` is therefore the input corpus for the
pre-registered real fixture.
