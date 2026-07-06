# EEST Receipt And Log Frontier

This note maps receipt/log-related EEST misses to focused implementation beads.
It is agent-facing triage: the stateless harness only compares the final
`SszStatelessValidationResult`, so fixture paths and known implementation gaps
are used to identify likely blockers.

Run the report after an EEST batch:

```bash
scripts/eest-receipt-log-frontier-report.py --run-dir gen-out/eest-run --limit 100
```

The report reads `manifest.tsv` plus `<case>.result.tsv` files and emits:

- `verdict`: `FULL`, `DIFF`, `ERROR`, or `MISSING`.
- `regions`: which stateless-output regions match (`root`, `succ`, `tail`).
- `classes`: likely receipt/log blocker classes.
- `blocker_beads`: focused beads that own each class.

## Frontier Classes

| Class | Evidence / current gap | Owner bead |
|---|---|---|
| `execution_status` | Receipts need success/revert/failure status from transaction execution before `receipt_encode` can be authoritative. | `evm-asm-fhsxz.2.4.2.63.1.3` |
| `cumulative_gas` | Receipts encode cumulative gas, but full refund and cumulative accounting is still separate gas work. | `evm-asm-fhsxz.2.4.2.57.7` |
| `logs_list` | `EvmAsm/Codegen/Programs/Evm.lean` documents LOG0-LOG4 as stack-pop no-ops that drop events. | `evm-asm-fhsxz.2.4.2.63.1.2` |
| `logs_bloom` | `Bloom.lean` has bloom helpers and block validation, but captured LOG entries are not yet connected to per-receipt bloom generation. | `evm-asm-fhsxz.2.4.2.63.1.4` |
| `receipts_root` | `BlockRoots.lean` has one- and two-receipt validators; a descriptor-loop path for all receipts is still needed. | `evm-asm-fhsxz.2.4.2.63.1.5` |
| `create_address` | CREATE/CREATE2 frame execution and created-account output must feed receipts and post-state. | `evm-asm-fhsxz.2.4.2.61.1` |
| `typed_receipt` | `Receipt.lean` notes typed receipts require a leading type byte; transaction execution must select legacy vs typed envelope. | `evm-asm-fhsxz.2.4.2.63.1.3` |

## Existing Substrate

- `EvmAsm/Codegen/Programs/Receipt.lean`: `rlp_encode_u64` and
  `receipt_encode`.
- `EvmAsm/Codegen/Programs/Bloom.lean`: bloom value insertion, receipt bloom
  extraction, receipt-list bloom accumulation, and header `logs_bloom`
  validation.
- `EvmAsm/Codegen/Programs/BlockRoots.lean`: fixed one-/two-receipt root
  validators that should be generalized into a future-proof loop.
- `scripts/codegen-zisk-receipt-encode-check.sh`,
  `scripts/codegen-zisk-block-logs-bloom-from-receipts-list-check.sh`, and
  `scripts/codegen-zisk-block-validate-logs-bloom-check.sh`: focused probes
  for current helper behavior.

## Interpretation

A row can have multiple classes. For example, a LOG-bearing typed transaction
can require LOG capture, logs bloom generation, typed receipt framing,
cumulative gas accounting, and receipts-root recomputation before it reaches
full match. Treat the class list as a work-routing hint, then confirm desired
behavior against `execution-specs` before implementation.
