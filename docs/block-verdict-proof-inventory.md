# BlockVerdict Proof Inventory

This is the working inventory for moving stateless verdict glue from raw
assembly strings toward `Program` values emitted by `emitProgram` and proved by
`cpsTriple`.  The immediate parent is bead `evm-asm-x43os`; the deployment
principle is bead `evm-asm-tj9ts`.

The template is the already-landed CREATE pair:

| Template | Current def | Strategy | First proof/probe | Blocker |
|---|---|---|---|---|
| initcode size gate | `cisvProgram`, `createInitcodeSizeValidFunction` in `EvmAsm/Codegen/Programs/CreateInitcodeSizeValid.lean` | Structured `Program`; function body is `"label:\n" ++ emitProgram cisvProgram`. | `cisv_deployed_spec` in `EvmAsm/Codegen/Proofs/CreateInitcodeSizeValidSpec.lean`; `zisk_create_initcode_size_valid`. | None. |
| deployed-code gate | `cdcvProgram`, `createDeployedCodeValidFunction` in `EvmAsm/Codegen/Programs/CreateDeployedCodeValid.lean` | Structured `Program`; function body is emitted from `cdcvProgram`. | `cdcv_spec` / deployed proof in `EvmAsm/Codegen/Proofs/CreateDeployedCodeValidSpec.lean`; `zisk_create_deployed_code_valid`. | None. |

## Classification

| Class | Meaning | Work pattern |
|---|---|---|
| Already structured and deployed | The emitted function body already comes from a `Program`, and a deployed `CodeReq.ofProg` proof exists or is intended in the same style. | Use as proof/deployment template. |
| Direct `Program` candidate | The body is a normal callable helper, uses only RV64 instructions expressible by `Instr`, and has internal labels that can become PC-relative branch offsets. | Introduce `<name>Program : Program`, emit via `emitProgram`, keep the probe, then prove a deployed spec. |
| Symbol-address helper | The helper is callable but directly loads/stores global symbols via `la`. | Split into a structured core with explicit pointer arguments; leave a thin raw wrapper for symbol setup if needed. |
| Caller-local fragment | The snippet jumps to labels owned by its caller or has no independent ABI. | Extract a callable helper with return statuses, then let the caller map statuses to existing labels. |
| Monolithic orchestration | Large top-level raw guest glue with many calls, globals, and local labels. | Prove only after smaller helpers have structured deployment links and a call/return composition plan. |

## BlockVerdict Targets

| Target | Current def | Class | Target strategy | First theorem/probe | Blocker |
|---|---|---|---|---|---|
| receipt classifier clear/set | `bvReceiptsShapeClear`, `bvReceiptsShapeSet` in `BlockVerdictReceiptGate.lean` | Symbol-address helper | Extract small store cores with explicit pointers for `bv_receipts_completeness_shape` and `bv_receipts_enforce_enabled`; keep existing call sites as wrappers. | `bvReceiptsShapeClear_deployed_spec`, `bvReceiptsShapeSet_deployed_spec`; add a focused classifier probe. | Needs `evm-asm-x43os.5` extraction before `evm-asm-x43os.6` proof. |
| runtime-completeness classifier | `bvRuntimeCompletenessClear`, `bvRuntimeCompletenessSet`, `bvRuntimeCompletenessSetFromArenaStatus` in `BlockVerdictReceiptGate.lean` | Symbol-address helper | Split direct status stores from arena-status branch classification; expose pointer/status arguments. | `bvRuntimeCompletenessClear_deployed_spec`, `bvRuntimeCompletenessSet_deployed_spec`, and branch helper spec if retained. | Same extraction/proof chain as receipt classifier. |
| empty transaction item scan | `blockVerdictEmptyTransactionCheckAsm` in `BlockVerdictTransactions.lean` | Caller-local fragment | Extract a callable tx-list scanner that returns `ok` or `empty_tx` instead of jumping to `.Lbv_empty_tx_fail` / `.Lbv_after_empty_tx_check`. | `blockVerdictEmptyTransactionCheck_deployed_spec`; probe no-tx, nonempty, empty item, malformed offsets. | `evm-asm-x43os.7` must define the ABI before proof bead `evm-asm-x43os.8`. |
| exact block gas check | `blockVerdictExactGasCheck` in `BlockVerdictExactGas.lean` | Caller-local fragment | Extract a helper returning status codes for net-state-gas failure, block-gas mismatch, and gas-limit overflow; caller maps to existing fail labels. | `blockVerdictExactGasCheck_deployed_spec`; reuse focused exact-gas probes and EEST rows. | `evm-asm-x43os.9` ABI extraction before proof bead `evm-asm-x43os.10`. |
| tx gas-limit materializer | `blockVerdictTxGasLimitsFunction` in `BlockVerdictGasResults.lean` | Symbol-address helper | The callable ABI is already clear, but debug globals use `la`; split a pointer-explicit core from debug wrapper or parameterize debug slots. | `blockVerdictTxGasLimits_deployed_spec`; existing `zisk_block_verdict_tx_gas_limits`. | Requires deciding whether debug globals are part of the proved core or wrapper. |
| gas-result arena prepare | `blockVerdictGasResultArenaPrepareFunction` in `BlockVerdictGasResults.lean` | Symbol-address helper | Keep the callable ABI; factor global arena/debug addresses into explicit pointer arguments before structured conversion. | `blockVerdictGasResultArenaPrepare_deployed_spec`; existing `zisk_block_verdict_gas_result_arena`. | Depends on tx gas-limit materializer strategy. |
| public key structural guard | `publicKeysValidFunction` in `BlockVerdictChainConfig.lean` | Symbol-address helper | Function is callable, but reads host-input length constants and writes `bv_public_keys_*`; extract pointer/limit arguments for a structured core. | `publicKeysValid_deployed_spec`; existing public-key sender probes plus a structural-only probe. | Needs a clean memory contract for host payload end and public-key output slots. |
| chain config guard | `chainConfigValidFunction` in `BlockVerdictChainConfig.lean` | Symbol-address helper | Callable guard with global `bv_chain_id` write; expose chain-config/public-key section bounds and chain-id output pointer. | `chainConfigValid_deployed_spec`; chain-config valid/invalid probe. | Larger branch tree; prove after a smaller chain-config helper split if needed. |
| bytecode self-contained scan | `bytecodeIsSelfContainedFunction` in `BlockVerdictSelfContained.lean` | Direct `Program` candidate | Body has no global `la` in the function itself; convert the loop and return arms to `Program` with PC-relative offsets. | `bytecodeIsSelfContained_deployed_spec`; existing `zisk_bytecode_is_self_contained`. | Need loop invariant for pushdata cursor progress before full semantic proof. |
| system storage side capture | `captureSystemStorageExecRowsFunction` in `BlockVerdictSystemStorageCapture.lean` | Symbol-address helper | Callable ABI is explicit for source/destination arenas, but debug globals use `la`; split debug stores from copy core. | `captureSystemStorageExecRows_deployed_spec`; existing `zisk_capture_system_storage_exec_rows`. | Decide whether overflow diagnostics are wrapper state or proved postcondition. |
| simple tx context | `simpleTransferTxContextFunction` in `BlockVerdictSimpleTransfer.lean` | Symbol-address helper | Callable parser with global scratch/debug dependencies; extract pure context parser core first. | `simpleTransferTxContext_deployed_spec`; existing `zisk_simple_transfer_tx_context`. | Requires stable context layout spec. |
| multi-tx nth context | `multiTxNthContextFunction` in `BlockVerdictMultiTx.lean` | Symbol-address helper | ABI is nearly callable; factor global context/output slots into explicit pointers. | `multiTxNthContext_deployed_spec`; existing `zisk_multi_tx_nth_context`. | Shares transaction-list parser facts with empty-tx and gas-limit helpers. |
| runtime payload staging | `stageRuntimePayloadFunction`, `stageRuntimePayloadCodeFunction`, `stageCreationRuntimePayloadFunction` | Symbol-address helper | Convert staging copy loops after splitting global arena addresses and environment-word destinations into parameters. | `stageRuntimePayload_deployed_spec` family; existing staging probes. | Needs byte-copy loop invariants and layout contracts. |
| contract storage key staging | `balRecipientStorageKeysFunction`, `balRecipientStorageReadsKeysFunction` | Symbol-address helper | Expose BAL recipient/storage output arenas as arguments; prove scan/copy cores independently. | `balRecipientStorageKeys_deployed_spec`; existing storage-key probes. | Depends on BAL account/storage descriptor shape lemmas. |
| account lookup | `balFindAccountByAddressFunction` in `BlockVerdictBalFindAccount.lean` | Direct `Program` candidate with loop | Callable helper with explicit inputs/outputs; convert after confirming no global `la` inside the function body. | `balFindAccountByAddress_deployed_spec`; existing `zisk_bal_find_account_by_address`. | Need account-list RLP iteration invariant. |
| system change helpers | `bsrSysChangeFunction`, `bsrBeaconChangeFunction` in `BlockVerdictSysChange.lean` | Symbol-address helper | Extract pointer-explicit state-change record builders before proving. | `bsrSysChange_deployed_spec`, `bsrBeaconChange_deployed_spec`; focused system-change probes. | Tied to state-root/BAL change record layout. |
| receipt/log materializers | `blockReceiptRecordsMaterializeFunction`, `blockLogWindowSnapshotFunction`, `blockReceiptLogsMaterializeFunction` | Symbol-address helper | Large but callable; parameterize all arenas/counters and prove loops in smaller cores. | Receipt/log deployed specs; existing overflow/materialization probes. | Capacity work under `evm-asm-vv4hr.3` may change layouts. |
| BAL tuple and independence helpers | `btiScanTuplesFunction`, `btiScanStorageChangesFunction`, `balTxsIndependentFunction` | Symbol-address helper | Keep tuple scanner cores separate from debug/global wrappers. | `balTxsIndependent_deployed_spec`; existing independence probe. | Tuple layout and skip-list policy still moving in P1/P0 BAL beads. |
| dispatch/runtime code helpers | `seedCalleeStorageFunction`, `dispatchTxRuntimeCodeFunction` | Symbol-address helper | Extract call-frame and code-preimage lookup cores with explicit arena/index pointers. | Deployed specs after code-preimage indexing work. | Depends on `evm-asm-vv4hr.5.3.*` code-index path. |
| state-root recompute | `blockStateRootFunction` in `BlockVerdictStateRoot.lean` | Monolithic orchestration | Defer full proof; carve out call/return verified helper islands first. | Future `blockStateRoot_deployed_spec`. | Too large until MPT/account/change helpers have deployed specs. |
| stateless verdict v2 wrapper | `statelessVerdictV2Function` in `BlockVerdictStateRoot.lean` | Monolithic orchestration | Treat as orchestration after block-state-root and block-verdict are structured. | Future `statelessVerdictV2_deployed_spec`. | Depends on most verdict helper proofs. |
| main block verdict | `blockVerdictFunction` in `BlockVerdictFunction.lean` | Monolithic orchestration | Continue extracting branchy fragments into callable helpers with status returns; compose proved calls later. | Future `blockVerdict_deployed_spec`. | Depends on classifier, empty-tx, exact-gas, receipt/log, state-root, BAL, request-hash helper specs. |
| stateless guest closure | `statelessVerdictV2GuestClosure`, `statelessVerdictV2GuestData` in `BlockVerdictV2.lean` | Monolithic orchestration / data section | Prove only after the functions it links are emitted from proved `Program`s or explicitly isolated wrappers. | Future `run_stateless_guest` / closure-level deployed spec. | Final north-star; not a first proof target. |

## First Build Order

1. `evm-asm-x43os.5`: extract receipt/runtime classifier store helpers.
2. `evm-asm-x43os.6`: prove the deployed classifier helpers.
3. `evm-asm-x43os.7`: extract empty-transaction scan into a status-return helper.
4. `evm-asm-x43os.8`: prove the deployed empty-transaction helper.
5. `evm-asm-x43os.9`: extract exact-gas check into a status-return helper.
6. `evm-asm-x43os.10`: prove the deployed exact-gas helper.

This order keeps each PR small, avoids the monolithic `block_verdict` proof
until smaller call targets have deployed specs, and follows the CREATE template
where the emitted assembly is connected to the proved `Program`.
