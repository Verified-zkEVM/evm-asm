# EEST Feature Surfaces

This map is for scheduling missing EVM feature work. It does not mark fixtures
as passing; it points each fixture class at the implementation bead that should
make that class runnable enough for semantic debugging.

Generate the current map from the local fixture cache:

```bash
scripts/eest-feature-surface-report.py
```

Use TSV output when feeding another script:

```bash
scripts/eest-feature-surface-report.py --format tsv
```

Generate the opcode-family matrix when choosing the next dispatcher slice:

```bash
scripts/eest-feature-surface-report.py --opcode-families
```

The opcode-family report maps matching fixture groups to concrete implementation
beads such as arithmetic/bitwise (`.60.2`), memory/calldata/returndata
(`.60.3`), control/halting (`.60.4`), environment reads (`.60.5`),
storage/logs/SELFDESTRUCT (`.60.6`), CALL/CREATE frames (`.61.1`), and
precompile dispatch (`.62`). It uses token-aware path filters, so newly added
EEST fixture files are counted without extending a hardcoded filename list.

The classifier is path-based and deliberately cheap. A fixture may count in
more than one surface when its path mentions multiple features, such as
precompile gas or call/create gas.

| Surface | Owning bead | Example filter | Why it matters |
| --- | --- | --- | --- |
| Frontier scenario matrices | `evm-asm-fhsxz.2.4.2.54.2` | `frontier/scenarios/scenarios/scenarios` | Tracks Amsterdam `blockchain_tests/for_amsterdam` scenario failures across CALL/CREATE/revert/static-context combinations. See [`docs/eest-scenarios-frontier.md`](eest-scenarios-frontier.md). |
| Simple tx/value transfer | `evm-asm-fhsxz.2.4.2.56` | `validation/transaction` | Establishes the basic transaction state transition before contract code. Gate: `scripts/codegen-eest-simple-value-transfer-frontier-check.sh` requires every selected `validation/transaction` block to full-match. |
| Gas accounting | `evm-asm-fhsxz.2.4.2.57` | `precompile_warming` | Turns warm/cold, intrinsic, memory, call, refund, and OOG fixtures into semantic failures. |
| Witness-backed state reads | `evm-asm-fhsxz.2.4.2.58` | `sload_non_const` | Replaces local/stub reads for `BALANCE`, `SLOAD`, `EXTCODE*`, and account existence. |
| General post-state root | `evm-asm-fhsxz.2.4.2.59` | `sstore_non_const` | Recomputes nonce, balance, storage root, code hash, creation, and deletion effects. |
| Opcode dispatcher | `evm-asm-fhsxz.2.4.2.60` | `frontier/opcodes` | Runs bytecode fixtures through the EVM dispatcher instead of postponing opcode classes. |
| EIP-6780 SELFDESTRUCT | `evm-asm-fhsxz.2.4.2.60.6.2` | `eip6780_selfdestruct` | Tracks Cancun SELFDESTRUCT creation/deletion, balance-transfer, revert, CREATE2 collision, and post-state effects. Frontier: [`docs/eest-eip6780-selfdestruct-frontier.md`](eest-eip6780-selfdestruct-frontier.md). |
| Call/create frames | `evm-asm-fhsxz.2.4.2.61` | `stCallCodes` | Adds child contexts, returndata, revert propagation, value transfer, and frame gas. |
| Precompile dispatch | `evm-asm-fhsxz.2.4.2.62` | `frontier/precompiles` | Adds gas and return-data framing for identity, ecrecover, modexp, BN128, BLAKE2, BLS, and later precompiles. Matrix: [`docs/eest-precompile-frontier.md`](eest-precompile-frontier.md). |
| Receipts/logs/bloom | `evm-asm-fhsxz.2.4.2.63` | `log0_non_const` | Produces receipts, cumulative gas, logs, and blooms after transaction execution. |
| Advanced fork features | `evm-asm-fhsxz.8` | `eip4844_blobs` | Tracks blobs/KZG, optional proofs, beacon roots, and other long-tail fork features. |

To probe a surface with the stateless harness, pass its example filter:

```bash
scripts/codegen-eest-stateless-check.sh \
  --filter frontier/opcodes \
  --limit 1 \
  --jobs 1 \
  --quiet-passes \
  --max-failures 1 \
  --steps 1000000000
```

The generated reports are the source of truth for current fixture counts. Update
the broad-surface or opcode-family classifier patterns when a new EEST directory
introduces a feature class that falls into `unclassified / mixed`.
