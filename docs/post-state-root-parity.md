# Post-State Root Parity

This note records the current `block_state_root` implementation surface against
the Python execution-specs state-root path. It is meant as agent-reachable
handoff material for EEST full-match work, not as a claim that all state-root
fixtures pass.

## Execution-Specs Reference

The target behavior is `State.compute_state_root_and_trie_changes` in
`execution-specs/src/ethereum/state.py`. That code:

- copies the main state trie and every storage trie except addresses listed in
  `storage_clears`;
- applies `account_changes` directly to the main trie, with `None` deleting an
  account;
- applies `storage_changes` to per-account secured storage tries, creating a
  storage trie if needed;
- drops a storage trie when its post-update data is empty;
- computes each account's final storage root through `get_storage_root`; and
- computes the post-state root with the final account RLP encoding.

Account encoding is `encode_account` in
`execution-specs/src/ethereum/merkle_patricia_trie.py`: RLP of
`(nonce, balance, storage_root, code_hash)`.

## Current Guest Path

The guest path is centered on
`EvmAsm/Codegen/Programs/BlockVerdict.lean`:

- `block_state_root` records EIP-2935 and EIP-4788 modeled-system account
  changes first.
- Non-system BAL account rows are compacted into final account descriptors with
  `bal_account_record_array` and `bal_account_change_descriptor`.
- Modeled-system BAL rows are applied back into the already-created system
  descriptors instead of being appended as duplicate account descriptors.
- Withdrawal descriptors are appended after system and BAL descriptors; repeated
  withdrawals to the same recipient are accumulated into one descriptor.
- All accumulated descriptors are passed to `mpt_state_root_ins`.
- `mpt_state_root_ins` supports modify, insert, delete, and no-op descriptor
  modes, and reports `sri_*` debug counters on state-trie failures.

The descriptor helper stack is covered by these focused probes:

```bash
scripts/codegen-zisk-bal-account-final-descriptor-array-check.sh
scripts/codegen-zisk-bal-account-apply-post-fields-check.sh
scripts/codegen-zisk-mpt-state-root-ins-check.sh
scripts/codegen-zisk-stateless-verdict-check.sh \
  --filter bal_create_storage_op_then_selfdestruct_same_tx \
  --limit 10 --steps 1000000000
```

Focused EEST frontiers that exercise the current block-verdict post-state path:

```bash
scripts/codegen-eest-simple-value-transfer-frontier-check.sh --jobs 1
scripts/codegen-eest-transaction-collision-empty-code-check.sh --jobs 1
scripts/codegen-eest-bal-replay-frontier-check.sh --jobs 1
```

The main EEST harness also reruns `zisk_stateless_verdict_v2` for
`successful_validation` mismatches unless `--no-verdict-debug` is set. Use the
printed `bsr_fail`, `change_count`, `baacd`, `bacv`, `baap`, `sri_index`,
`sri_mode`, and `sri_status` fields to distinguish descriptor construction
failures from state-trie application failures.

## Remaining Gaps

The current implementation is complete for the BAL-derived descriptor subset
that has landed so far, but it is not yet a full execution-specs state-diff
engine.

- Storage clears are not a general `storage_clears` set. Today only the modeled
  BAL/storage descriptor paths that have been implemented can produce storage
  root updates.
- Code preimages are validated and code hashes can appear in final account RLP,
  but there is no general code-deployment diff pipeline for arbitrary executed
  CREATE/CREATE2 outputs yet.
- Account creation and deletion are supported at the descriptor/MPT layer, but
  they are only as complete as the upstream execution path that emits those
  descriptors.
- Repeated account touches are compacted for BAL rows and withdrawals; future
  call/create/selfdestruct emitters need to preserve the same final-descriptor
  invariant before appending to `bsr_changes`.
- The static layout still has bounded arenas. The default witness cap is 256 KiB
  in `BlockVerdict.lean`, and BAL/account descriptor capacity is derived from
  the accepted block gas limit. Layout-incompatible fixtures should fail before
  launching the guest.
- Gas-sensitive post-state behavior, warm/cold access accounting, refunds, and
  cumulative gas remain tied to the gas-metering scaffold.

When adding a new state-changing opcode path, prefer emitting the same
`mpt_state_root_ins` descriptor shape rather than inventing a second state-root
application route.
