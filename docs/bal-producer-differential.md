# BAL producer differential probe

This probe is a tooling-only check of the final BAL-builder rows in the
emitted guest. It does not change the guest or feed guest rows into SpecRef.
The primary assertion is exact element-by-element equality of each decoded
guest row stream (address, BAI, and payload fields) against the pre-registered
rows. A count match alone is insufficient: a mismatch names the affected
stream and fails the run. The guest runs on SPIKE; the reference rows are
decoded from the pinned execution-specs Amsterdam `BlockAccessList` in each
fixture payload and are pre-registered in
[`scripts/spike/bal-balance-changes.expectation.json`](../scripts/spike/bal-balance-changes.expectation.json).

The registered fixture set is deliberately small but spans the producer
classes:

| expectation | fixture | final rows (accounts/storage/balance/nonce/code) |
| --- | --- | --- |
| `bal-balance-changes` | balance-change fixture | 9 / 2 / 3 / 1 / 0 |
| `bal-storage-writes` | storage-write fixture | 9 / 4 / 2 / 1 / 0 |
| `bal-code-changes` | code-change fixture | 10 / 2 / 2 / 3 / 1 |
| `bal-all-transaction-types` | five-transaction, multi-BAI fixture | 18 / 7 / 10 / 6 / 1 |

Each expectation records the execution-specs pin and input SHA-256. Regenerate
one only when deliberately changing its fixture:

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

Run the complete registered set with:

```bash
scripts/spike/bal_producer_set.sh \
  gen-out/regionmap/stateless_guest.elf \
  /var/tmp/fc668/manifest.tsv \
  /tmp/bal-producer-diff-set
```

The run supplies `SPIKE_DUMP_RANGES` from the ELF's `nm` symbols and the row
sizes/capacities from `BlockAccessListBuilder.lean`, plus the code-effect and
EIP-7702 code arenas. It reports attempted, decoded, skipped, undecodable,
overflow, and final row counts. Any skipped or undecodable row is a hard
failure. The rebuilt/supplied serializer hash equality is retained as a
secondary cross-check; it is already shadow-verified inside the guest and is
not the differential's headline claim. `SPIKE_COMMITLOG` remains a separate
attempted-write audit and is not used as the producer extraction.

The tracked `fixtures/kat` JSONs are intentionally mutated reject-side KATs;
they are not a clean producer oracle for this check. The approved 26,104-row
manifest under `/var/tmp/fc668` is therefore the input corpus for the
pre-registered real fixture.
