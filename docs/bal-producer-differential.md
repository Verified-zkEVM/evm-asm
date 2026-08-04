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
classes. It keeps the first four controls and adds ten class-covering fixtures:

| expectation | fixture | final rows (accounts/storage/balance/nonce/code) |
| --- | --- | --- |
| `bal-balance-changes` | balance-change fixture | 9 / 2 / 3 / 1 / 0 |
| `bal-storage-writes` | storage-write fixture | 9 / 4 / 2 / 1 / 0 |
| `bal-code-changes` | code-change fixture | 10 / 2 / 2 / 3 / 1 |
| `bal-all-transaction-types` | five-transaction, multi-BAI fixture | 18 / 7 / 10 / 6 / 1 |
| `bal-cross-tx-balance-dependency` | multi-transaction BAI attribution | 11 / 3 / 6 / 2 / 0 |
| `bal-selfdestruct-to-coinbase` | SELFDESTRUCT / EIP-6780 | 9 / 2 / 3 / 1 / 0 |
| `bal-create-storage-selfdestruct` | CREATE storage then SELFDESTRUCT | 11 / 3 / 4 / 2 / 0 |
| `bal-7702-delegated-storage` | EIP-7702 delegated storage access | 10 / 3 / 3 / 1 / 0 |
| `bal-7702-delegation-create` | EIP-7702 delegation creation | 9 / 2 / 2 / 1 / 1 |
| `bal-system-noop` | system-phase rows including BAI 0 | 9 / 2 / 3 / 1 / 0 |
| `bal-system-dequeue-consolidations` | system-phase consolidation rows | 9 / 15 / 6 / 2 / 0 |
| `bal-net-zero-storage-empty-pre` | net-zero storage, empty prestate | 9 / 2 / 2 / 1 / 0 |
| `bal-net-zero-storage-nonzero-pre` | net-zero storage, nonzero prestate | 9 / 2 / 2 / 1 / 0 |
| `bal-net-zero-nested-delegatecall` | net-zero nested delegatecall storage | 10 / 2 / 2 / 1 / 0 |

Two additional class probes are recorded as findings rather than silently
removed from the investigation. They have no skipped, undecodable, or overflow
rows, but the guest producer disagrees with the pinned reference:

| fixture prefix | class | expected rows (accounts/storage/balance/nonce/code) | guest rows |
| --- | --- | --- | --- |
| `01087_test_bal_create2_selfdestruct_then_recreate_same_block...` | EIP-6780 deletion/recreation | 11 / 4 / 6 / 5 / 1 | 11 / 5 / 6 / 3 / 0 |
| `00612_test_bal_7702_cross_tx_delegation_then_call...` | EIP-7702 cross-transaction attribution | 12 / 4 / 5 / 4 / 1 | 12 / 4 / 5 / 4 / 1 |

The second finding has mismatching balance payloads despite equal row counts;
both findings also have unequal rebuilt/supplied serializer hashes. They are
kept out of the green set so the set runner remains a pass/fail oracle, but are
reported explicitly for follow-up rather than being hidden as unsupported
fixtures. The findings had zero undecodable rows and zero overflow flags.

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
