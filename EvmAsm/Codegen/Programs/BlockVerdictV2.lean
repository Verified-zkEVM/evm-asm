/-
  EvmAsm.Codegen.Programs.BlockVerdictV2

  Probe unit and guest-closure definitions carved out of
  `Programs/BlockVerdict.lean` to satisfy the 1500-line file-size hard cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdict
import EvmAsm.Codegen.Programs.MptBoundedSort
-- .63.1.6.2.3 (slice B): full-receipt encoder + combined root+bloom validator
import EvmAsm.Codegen.Programs.Receipt
import EvmAsm.Codegen.Programs.ReceiptList
import EvmAsm.Codegen.Programs.BloomBlock
import EvmAsm.Codegen.Programs.ReceiptsConsensus
import EvmAsm.Codegen.Programs.EvmBasic
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.DispatcherExecStateGas
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.SszWithdrawal
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.WitnessCodeLookup

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch
import EvmAsm.Codegen.Programs.BlockVerdictContractStage
import EvmAsm.Codegen.Programs.BlockVerdictSingleTxLog
import EvmAsm.Codegen.Programs.BlockVerdictSelfContained
import EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount
import EvmAsm.Codegen.Programs.BlockVerdictDispatchTx
import EvmAsm.Codegen.Programs.SeedTxAccessList
import EvmAsm.Codegen.Programs.BalAddrExecLogKey
-- #11118: CodeCovers/Code/AccountCodeConsistent/StorageReadsExecLog unlinked (dead 43/46/38).
import EvmAsm.Codegen.Programs.StageBlockhashM29
import EvmAsm.Codegen.Programs.TxPubkey
import EvmAsm.Codegen.Programs.VerifyPublicKeysSenders
import EvmAsm.Codegen.Programs.BalAllAccountsNonstorage
import EvmAsm.Codegen.Programs.BalAllAccountsNonstorageCovers
import EvmAsm.Codegen.Programs.BalAccountNonstorageConsistent
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.ExecLogLatestValue
import EvmAsm.Codegen.Programs.CommittedStorageLookup
import EvmAsm.Codegen.Programs.BlockVerdictMultiTx
import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.Eip7702Authority
import EvmAsm.Codegen.Programs.MultiTxSenderDebit
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.StorageReadLog
import EvmAsm.Codegen.Programs.StorageWriteMap
import EvmAsm.Codegen.Programs.AccountWriteMap
import EvmAsm.Codegen.Programs.BalMapBuilderConsistent
import EvmAsm.Codegen.Programs.BalCanonicalSort
import EvmAsm.Codegen.Programs.KeccakIncremental
import EvmAsm.Codegen.Programs.BalRlpEncode
import EvmAsm.Codegen.Programs.AccountReadLog
import EvmAsm.Codegen.Programs.CodeReadLog
import EvmAsm.Codegen.Programs.ReadSetsPromote
import EvmAsm.Codegen.Programs.BlockAccessListBuilder
import EvmAsm.Codegen.Programs.BlockVerdictTxsIndependent

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def ziskStatelessVerdictV2ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm :=
    ziskStatelessVerdictV2Prologue ++ "\n" ++
    "  j .Lstateless_verdict_v2_debug_after_runtime_dispatcher\n" ++
    emitRuntimeDispatcherCallableCoreSharedHelpers callFrameGuestRegistry evmAddEpilogue ++ "\n" ++
    -- je0xd: block_verdict's contract-dispatch helpers were embedded in the guest
    -- closure (statelessVerdictV2GuestClosure) but NOT this debug verdict ELF, so
    -- its link failed with 6 undefined references. Mirror the guest: emit the
    -- same 8 bodies (the 6 + the slot leaf helpers) in this jumped-over region.
    -- The data labels are already shared via ziskStatelessVerdictV2DataSection.
    slotDecodeU256Function ++ "\n" ++
    slotAtIndexFunction ++ "\n" ++
    slotAtHeaderStateRootFunction ++ "\n" ++
    codeAtHeaderStateRootFunction ++ "\n" ++
    bytecodeIsSelfContainedFunction ++ "\n" ++
    balFindAccountByAddressFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    stageRuntimePayloadWitnessContextFunction ++ "\n" ++
    -- .6.2.2.1: block_verdict's contract dispatch now calls dispatch_tx_runtime_code;
    -- emit its body here too so this debug verdict ELF links (mirrors the guest closure).
    dispatchTxRuntimeCodeFunction ++ "\n" ++
    txAccessListSpanFunction ++ "\n" ++
    -- Cursor-walk RLP primitives required by the tx/header decoders below
    -- (same drift class as the contract-dispatch helpers above: these are
    -- embedded in the guest closure but not this debug ELF, so mirror them).
    rlpWalkHelpersClosure ++ "\n" ++
    txEip2930DecodeFunction ++ "\n" ++
    txEip1559DecodeFunction ++ "\n" ++
    txEip7702DecodeFunction ++ "\n" ++
    storageAccessSeedFunction ++ "\n" ++
    seedTxAccessListFunction ++ "\n" ++
    -- .62.2.5: ECRECOVER recovery backend (armed via ecrecover_backend_ptr in
    -- dispatch_tx_runtime_code). NoU256 variants: this closure already links
    -- u256_add_be/u256_sub_be/u256_lt_be.
    secp256k1CurveCommonFunctionsNoU256 ++ "\n" ++
    secp256k1RecoverRFunction ++ "\n" ++
    secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
    -- The base V2 verdict closure already emits address_from_pubkey and the
    -- EIP-7702 authorization-recovery helpers for tx-state-gas accounting.
    -- Re-emitting them in this debug-only helper block duplicates symbols.
    -- GH #10619: this debug unit mirrors the guest's handlers and helpers, so every
    -- routine the read containers hook is present here too -- h_SLOAD/h_SSTORE,
    -- account_state_commit_pending, code_at_header_state_root,
    -- dispatch_tx_runtime_code, block_verdict_withdrawal_nonstorage_effects. It
    -- therefore needs the recorders, both tracked accessors and the promotion
    -- boundary, or it fails to LINK with undefined references to
    -- storage_read_record, code_read_fetch, read_sets_incorporate_tx and
    -- account_at_header_state_root_tracked.
    --
    -- `lake build` stays GREEN while this is missing: the fault is in emitted asm
    -- for a build unit that only the EEST harness links, so neither the build nor
    -- the byte-tie sees it. It surfaced as a link error buried inside an A/B leg.
    -- Same class as the earlier code_reads constant (a6c31440a) -- an emit is only
    -- verified once the `.elf` EXISTS, and this unit has its own `.elf`.
    execLogAddrToBalCanonicalFunction ++ "\n" ++
    storageReadRecordFunction ++ "\n" ++
    storageReadRecordBlockFunction ++ "\n" ++
    -- r59nm S2: the WRITE-side counterpart.  Mirrored into this unit for the same
    -- reason as the read recorders above -- this unit has its own `.elf`, so an
    -- omission here surfaces only as a link error inside an A/B leg.
    storageWriteRecordFunction ++ "\n" ++
    destroyStorageFunction ++ "\n" ++
    storageWritesBlockUpsertFunction ++ "\n" ++
    writeSetsIncorporateTxFunction ++ "\n" ++
    writeSetsDiscardTxFunction ++ "\n" ++
    storageWritesUndoPushFunction ++ "\n" ++
    writeSetsRestoreFrameFunction ++ "\n" ++
    -- GH #10695 nonstorage half: the account_writes MAP, one container pair for
    -- balance+nonce+code (the spec keeps one non-storage write dict per level).
    -- Mirrored here for the same reason as the storage set: this unit has its own
    -- `.elf`, so an omission surfaces only as a link error inside an A/B leg.
    accountWriteMapFunctions ++ "\n" ++
    balMapBuilderConsistentFunctions ++ "\n" ++
    -- GH #10680: canonical ordering for both write containers. Inert -- nothing
    -- consumes the ordering yet -- but emitted so the assembler and linker see it.
    balCanonicalSortFunctions ++ "\n" ++
    -- Resumable keccak entry points (general infrastructure, first consumer #10680).
    -- The one-shot routines are untouched; these use a caller-supplied context.
    keccakIncrementalFunctions ++ "\n" ++
    -- GH #10680 RLP field encoders. Inert -- nothing walks the containers yet.
    balRlpEncodeFunctions ++ "\n" ++
    blockAccessListBuilderFunctions ++ "\n" ++
    accountReadRecordFunction ++ "\n" ++
    accountAtHeaderStateRootTrackedFunction ++ "\n" ++
    codeReadRecordFunction ++ "\n" ++
    codeReadFetchFunction ++ "\n" ++
    readSetsMergeOneFunction ++ "\n" ++
    readSetsIncorporateTxFunction ++ "\n" ++
    readSetsDiscardTxFunction ++ "\n" ++
    -- F3 retirement: no eager BAL-account seed producer is linked.
    balAddrToExecLogKeyFunction ++ "\n" ++
    -- bmvmx.1.6.2: bal_storage_change_values (tuple path). matches/covers unlinked #10681.
    balStorageChangeValuesFunction ++ "\n" ++
  -- #11178: exec_log_latest_value unlinked (probe-only; 0 guest refs)
  -- #11118: bal_storage_reads_in_exec_log / code_covers / code_consistent unlinked (dead labels 38/43/46).
  -- #10681: bal_storage_matches/covers + all_accounts_storage_consistent unlinked (0 live jal; hash survivor).
  -- #11245: tuple skip-list 42 + exclusive callees unlinked (hash survivor; #10646 closed).
  stageBlockhashM29Function ++ "\n" ++   -- 3vc2p.3b: M29 recent-blockhash table reconstruction (dispatch staging)
  blockhashFromWitnessHeadersFunction ++ "\n" ++   -- 3vc2p.3b dep: find header by number -> keccak(header)
  headerExtractNumberFunction ++ "\n" ++   -- 3vc2p.3b dep: header NUMBER field extractor
  balAllAccountsNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3: all-accounts NON-STORAGE forward (balance/nonce)
  balAccountNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3 dep: per-account non-storage compare
  balAccountNonstorageFinalsFunction ++ "\n" ++   -- i3djw.3 dep: BAL account balance/nonce finals
  balAllAccountsNonstorageCoversFunction ++ "\n" ++   -- i3djw.3 reverse: exec net-change -> BAL presence
    -- Keep the standalone verdict-debug ELF's withdrawal-effect closure in
    -- lockstep with the guest closure; verdict code is unchanged.
    blockVerdictWithdrawalNonstorageEffectsFunction ++ "\n" ++
    multiTxNthContextFunction ++ "\n" ++
    rlpFieldToU64Function ++ "\n" ++
    -- bmvmx.3.2: mirror the guest closure's per-tx sender-recovery stack so this
    -- debug verdict ELF links (block_verdict calls verify_public_keys_match_senders).
    verifyPublicKeysSendersGuestFunctions ++ "\n" ++
    -- 8uld3.2.3 / .63.1.6.2.3: mirror the request-derivation and receipts-consensus
    -- bodies that block_verdict now reaches inside the embedded guest closure. The
    -- standalone debug ELF does not include statelessGuestUnit.epilogueAsm, so these
    -- symbols must be emitted here as well.
    -- `derive_block_system_requests` probe-only (#11156); dbsr_* data stays below.
    deriveWithdrawalRequestsFunction ++ "\n" ++
    deriveConsolidationRequestsFunction ++ "\n" ++
    deriveBuilderDepositRequestsFunction ++ "\n" ++
    deriveBuilderExitRequestsFunction ++ "\n" ++
    stageSystemCallFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    -- #11431: MtxRuntime jals process_block_start_system_transactions; standalone
    -- v2 unit mirrors those handlers and must link the callee (check-build-units-link).
    processBlockStartSystemTransactionsFunction ++ "\n" ++
    parseDepositRequestsFunction ++ "\n" ++
    extractDepositDataFunction ++ "\n" ++
    materializeLogRecordsFunction ++ "\n" ++
    assembleExecutionRequestsFunction ++ "\n" ++
    requestsHashVerifyFunction ++ "\n" ++
    zkvmKeccak256SegmentsFunction ++ "\n" ++
    rlpEncodeU64Function ++ "\n" ++
    receiptEncodeFunction ++ "\n" ++
    receiptRecordsEncodeNoLogsFunction ++ "\n" ++
    blockValidateLogsBloomFunction ++ "\n" ++
    receiptExtractLogsBloomFunction ++ "\n" ++
    bloomOrIntoFunction ++ "\n" ++
    blockLogsBloomFromReceiptsListFunction ++ "\n" ++
    blockValidateReceiptsConsensusListFunction ++ "\n" ++
    ".Lstateless_verdict_v2_debug_after_runtime_dispatcher:\n"
  dataAsm     :=
    ziskStatelessVerdictV2DataSection ++ "\n" ++
    -- GH #10619: cursors/overflow flags for the recorders mirrored into this unit
    -- above. `ziskStatelessVerdictV2DataSection` carries only the shared verdict
    -- labels; the read-log cursors live in `statelessVerdictV2GuestData`, which
    -- this unit does not use -- so they must be repeated here, not inherited.
    storageReadLogDataSection ++ "\n" ++
    -- r59nm S2: cursors/overflow flags for the two storage_writes levels.
    storageWriteMapDataSection ++ "\n" ++
    accountWriteMapDataSection ++ "\n" ++
    accountAgreementDataSection ++ "\n" ++
    balMapBuilderConsistentDataSection ++ "\n" ++
    balCanonicalSortDataSection ++ "\n" ++
    keccakIncrementalDataSection ++ "\n" ++
    accountReadLogDataSection ++ "\n" ++
    codeReadLogDataSection ++ "\n" ++
    readSetsBlockDataSection ++ "\n" ++
    executionRequestsHashShaDataSection ++ "\n" ++
    -- Data labels for the request-derivation helpers above.
    -- ziskStatelessVerdictV2DataSection already owns the receipt-consensus scratch.
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    ".section .data\n" ++
    ".balign 8\n" ++
    "scc_system_addr:\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe\n" ++
    ".balign 8\n" ++
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
    "ssc_calldata_ptr:\n  .zero 8\n" ++
    "ssc_calldata_len:\n  .zero 8\n" ++
    "pbsst_saved_ra:\n  .zero 8\n" ++
    "pbsst_code_ptr:\n  .zero 8\n" ++
    "pbsst_code_len:\n  .zero 8\n" ++
    withdrawalRequestPredeployAddrData ++
    consolidationRequestPredeployAddrData ++
    builderContractAddrData ++
    ".section .bss, \"aw\", @nobits\n" ++
    deriveBlockSystemRequestsData ++ "\n" ++
    -- `BlockVerdictDataSectionTail` places the large committed-storage map in
    -- its own NOBITS section and resumes `.bss`; these fixed deposit constants
    -- are initialized bytes, so resume PROGBITS before emitting them.
    ".section .data\n" ++
    ".balign 8\n" ++
    "pdr_deposit_addr:\n" ++
    "  .byte 0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40\n" ++
    "  .byte 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30\n" ++
    "  .byte 0x3d, 0x77, 0x05, 0xfa\n" ++
    ".balign 8\n" ++
    "pdr_deposit_sig:\n" ++
    "  .byte 0x64, 0x9b, 0xbc, 0x62, 0xd0, 0xe3, 0x13, 0x42\n" ++
    "  .byte 0xaf, 0xea, 0x4e, 0x5c, 0xd8, 0x2d, 0x40, 0x49\n" ++
    "  .byte 0xe7, 0xe1, 0xee, 0x91, 0x2f, 0xc0, 0x88, 0x9a\n" ++
    "  .byte 0xa7, 0x90, 0x80, 0x3b, 0xe3, 0x90, 0x38, 0xc5\n" ++
    ".section .bss, \"aw\", @nobits\n" ++
    ".balign 8\n" ++
    "pdr_out:\n  .zero 2048\n" ++
    "pdr_status:\n  .zero 8\n" ++
    "rhv_hash:\n  .zero 32\n" ++
    emitRuntimeDispatcherDataSectionSharedGuest callFrameGuestRegistry
}

/-- The full stateless_verdict_v2 asm closure for embedding in the GUEST epilogue,
    OMITTING rlp_list_nth_item + rlp_field_to_u64 (the guest already defines those,
    so they would be duplicate labels). The guest jal's `stateless_verdict_v2` and
    writes its bit to OUTPUT[32]. -/
def statelessVerdictV2GuestClosure : String :=
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  -- Cursor-walk RLP primitives (single-pass decode; used by the tx/header
  -- decoders invoked from the verdict pipeline). Peer to the index-based
  -- primitives above; linked here so the guest resolves these symbols.
  rlpWalkHelpersClosure ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalToPathDeltaFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  extcodesizeAtHeaderStateRootFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptStateRootFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  mptOneLeafRootIndexedFunction ++ "\n" ++
  withdrawalsStateRootFunction ++ "\n" ++
  mptIndexedTrieRootOneLeafFunction ++ "\n" ++
  mptIndexedLargeLeafHashFunction ++ "\n" ++
  mptIndexedTrieRootLargeFunction ++ "\n" ++
  mptIndexedTrieRootSmallFunction ++ "\n" ++
  mptIndexedStreamLeafHashFunction ++ "\n" ++
  mptIndexedSortChangesFunction ++ "\n" ++
  mptIndexedLeafRefFunction ++ "\n" ++
  mptIndexedBuildSubtreeFunction ++ "\n" ++
  mptIndexedTrieRootBoundedFunction ++ "\n" ++
  mptIndexedTrieRootBoundedFromValuesFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  blockValidateWithdrawalsRootIndexedFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  amsterdamBlobGasPriceU256Function ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  headerValidateExcessBlobGasFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  validateHeaderRlpPairFunction ++ "\n" ++
  bhrRevLeBeFunction ++ "\n" ++
  blockHeaderSszToRlpFunction ++ "\n" ++
  rlpBytesEncodedSizeFunction ++ "\n" ++
  rlpListEncodedSizeFunction ++ "\n" ++
  blockRlpRebuiltSizeFunction ++ "\n" ++
  bahU32leFunction ++ "\n" ++
  blockAccessListHashCoreFunction ++ "\n" ++
  blockAccessListHashFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  executionRequestsHashFunction ++ "\n" ++
  step2VerdictFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  ephU32leFunction ++ "\n" ++
  extractParentHeaderAndStateRootFunction ++ "\n" ++
  spwU32leFunction ++ "\n" ++
  extractPayloadAndWithdrawalsFunction ++ "\n" ++
  swsU32leFunction ++ "\n" ++
  extractWitnessStateSectionFunction ++ "\n" ++
  swrRevLeBeFunction ++ "\n" ++
  sszWithdrawalToRlpFunction ++ "\n" ++
  statelessVerdictFromSszFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  accountApplyStorageSlotAccFunction ++ "\n" ++
  swdReadU64leFunction ++ "\n" ++
  swdWriteBe32U64Function ++ "\n" ++
  swdWriteBe8Function ++ "\n" ++
  swdMinimalCopyFunction ++ "\n" ++
  systemWriteDescriptorsFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  accountIsEip161EmptyFunction ++ "\n" ++
  balAccountHasStateChangeFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  mapAccountApplyPostFieldsFunction ++ "\n" ++
  mapAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountRecordArrayFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++
  bsrSysChangeFunction ++ "\n" ++
  bsrBeaconChangeFunction ++ "\n" ++
  bsrApplyModeledSystemPostFieldsFunction ++ "\n" ++
  appendModeledSystemStorageTupleRowsFunction ++ "\n" ++
  recordModeledEip4788StorageReadsFunction ++ "\n" ++
  mptBoundedBuilderFrontEndFunction ++ "\n" ++
  blockStateRootPreAccountsFunction ++ "\n" ++
  executionMapStateChangesFunction ++ "\n" ++
  blockStateRootFunction ++ "\n" ++
  chainConfigValidFunction ++ "\n" ++
  publicKeysValidFunction ++ "\n" ++
  receiptRecordsFunction ++ "\n" ++
  blockReceiptRecordsMaterializeFunction ++ "\n" ++
  -- .63.1.6.2.1: per-tx log windows -> per-record logs RLP + bloom.
  blockLogWindowSnapshotFunction ++ "\n" ++
  blockReceiptLogsMaterializeFunction ++ "\n" ++
  logRecordsEncodeRlpFunction ++ "\n" ++
  bloomAddValueFunction ++ "\n" ++
  logBloomAddFunction ++ "\n" ++
  logsListBloomAddFunction ++ "\n" ++
  -- .63.1.6.2.3: receipts-consensus validators (the indexed-trie family is
  -- already linked for the transactions/withdrawals root checks).
  headerExtractReceiptsRootFunction ++ "\n" ++
  blockValidateReceiptsRootIndexedFunction ++ "\n" ++
  -- .63.1.6.2.3 (slice B): tx-bearing enforcement needs the full-receipt encoder
  -- (receipt_records_encode_no_logs + receipt_encode + rlp_encode_u64) and the combined
  -- root+bloom validator (block_validate_receipts_consensus_list + block_validate_logs_bloom).
  -- rlp_list_nth_item / rlp_list_count_items / rlp_encode_bytes / rlp_encode_list_prefix /
  -- receipt_records are already linked.
  rlpEncodeU64Function ++ "\n" ++
  receiptEncodeFunction ++ "\n" ++
  receiptRecordsEncodeNoLogsFunction ++ "\n" ++
  blockValidateLogsBloomFunction ++ "\n" ++
  -- block_validate_logs_bloom -> block_logs_bloom_from_receipts_list -> receipt_extract_logs_bloom
  -- + bloom_or_into (the logs_list_bloom_add / bloom_add_value family is already linked).
  receiptExtractLogsBloomFunction ++ "\n" ++
  bloomOrIntoFunction ++ "\n" ++
  blockLogsBloomFromReceiptsListFunction ++ "\n" ++
  blockValidateReceiptsConsensusListFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  bloomEqFunction ++ "\n" ++
  blockVerdictFunction ++ "\n" ++
  blockVerdictWithdrawalNonstorageEffectsFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  txEip4844ValidateBlobHashesFunction ++ "\n" ++
  sszTxListVersionedHashesMatchFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  balSectionInfoFunction ++ "\n" ++
  -- #11172: bal_gas_valid (RLP walker) unlinked; KEEP from_builder + bgv_* helpers
  balGasValidFromBuilderFunction ++ "\n" ++
  accountAtHeaderStateRootFunction ++ "\n" ++
  codeHashAtHeaderStateRootFunction ++ "\n" ++
  -- #11183 rows 11-12 / #11410: bal_code_preimages_valid unlinked (0 guest jal).
  -- Keep only live account_state_delegation_code_resolve from that blob.
  accountStateDelegationCodeResolveFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  txGasSenderBalLookupFunction ++ "\n" ++
  stageRuntimePayloadFunction ++ "\n" ++
  stageCreationRuntimePayloadFunction ++ "\n" ++
  blockVerdictCreationRuntimeFunction ++ "\n" ++
  -- .6.4.3.2 contract-recipient dispatch: state/code lookups + BAL storage-key
  -- enumeration + self-containment gate + variable pack-bytecode staging. The
  -- shared callees (account_at_address, header_extract_state_root,
  -- witness_lookup_by_hash, rlp_list_nth_item/count_items, mset_memcpy) are
  -- already in this closure; only these top-level bodies + slot leaf helpers
  -- (slot_at_index/slot_decode_u256) are new.
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  slotAtHeaderStateRootFunction ++ "\n" ++
  codeAtHeaderStateRootFunction ++ "\n" ++
  bytecodeIsSelfContainedFunction ++ "\n" ++
  balFindAccountByAddressFunction ++ "\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  stageRuntimePayloadWitnessContextFunction ++ "\n" ++
  -- #10685 PR2: bv_emit_single_tx_tl7708 unlinked (never-written buffer +
  -- mode-2 gate bypass; early-exit no-op even if jal taken). KEEP Function
  -- string for probe isolation.
  dispatchTxRuntimeCodeFunction ++ "\n" ++
  txAccessListSpanFunction ++ "\n" ++
    txEip2930DecodeFunction ++ "\n" ++
    txEip1559DecodeFunction ++ "\n" ++
    txEip7702DecodeFunction ++ "\n" ++
  storageAccessSeedFunction ++ "\n" ++
  seedTxAccessListFunction ++ "\n" ++
  -- .62.2.5: ECRECOVER recovery backend (armed via ecrecover_backend_ptr in
  -- dispatch_tx_runtime_code). NoU256 variants: this closure already links
  -- u256_add_be/u256_sub_be/u256_lt_be.
  secp256k1CurveCommonFunctionsNoU256 ++ "\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
  -- F3 retirement: no eager BAL-account seed producer is linked.
  balAddrToExecLogKeyFunction ++ "\n" ++
  -- bmvmx.1.6.2: bal_storage_change_values (tuple path). matches/covers unlinked #10681.
  balStorageChangeValuesFunction ++ "\n" ++
  -- #11178: exec_log_latest_value unlinked (probe-only; 0 guest refs)
  storageWritesBlockLatestValueFunction ++ "\n" ++
  -- #11118: dead BAL labels 38/43/46 unlinked (reads/code_covers/code_consistent).
  -- #10681: bal_storage_matches/covers + all_accounts_storage_consistent unlinked (0 live jal).
  -- #11245: tuple skip-list 42 + exclusive callees unlinked (hash survivor; #10646 closed).
  -- GH #10619: producer for the storage_reads CONTAINER (spec set semantics,
  -- block lifetime, untouched by rollback).  Called from the SLOAD/SSTORE
  -- handler preBody so the verified evm_sload body stays byte-identical.
  execLogAddrToBalCanonicalFunction ++ "\n" ++
  storageReadRecordFunction ++ "\n" ++
  storageReadRecordBlockFunction ++ "\n" ++
  -- r59nm S2: producer and promotion boundary for the storage_writes MAP (spec
  -- dict semantics, two levels, upsert rather than append).  Not yet consulted --
  -- every comparator still reads the exec-log arenas, so this cannot move a
  -- verdict.  S3/S4 wire the comparators over.
  storageWriteRecordFunction ++ "\n" ++
    destroyStorageFunction ++ "\n" ++
  storageWritesBlockUpsertFunction ++ "\n" ++
  writeSetsIncorporateTxFunction ++ "\n" ++
    writeSetsDiscardTxFunction ++ "\n" ++
    storageWritesUndoPushFunction ++ "\n" ++
    writeSetsRestoreFrameFunction ++ "\n" ++
  -- GH #10695 nonstorage half: producer and promotion boundary for the
  -- account_writes MAP -- ONE container pair covering balance, nonce AND code,
  -- because the spec keeps one non-storage write dict per level and
  -- update_builder_from_tx derives all three BAL fields from a single loop over it
  -- (block_access_lists.py:637-664).  Not yet consulted and nothing calls these:
  -- emitted so the assembler and linker see them, since an unreferenced routine is
  -- unverified code.  The change-emission slice adds the callers.
  accountWriteMapFunctions ++ "\n" ++
  balMapBuilderConsistentFunctions ++ "\n" ++
    -- GH #10680: canonical ordering for both write containers. Inert -- nothing
    -- consumes the ordering yet -- but emitted so the assembler and linker see it.
    balCanonicalSortFunctions ++ "\n" ++
    -- Resumable keccak entry points (general infrastructure, first consumer #10680).
    -- The one-shot routines are untouched; these use a caller-supplied context.
    keccakIncrementalFunctions ++ "\n" ++
    -- GH #10680 RLP field encoders. Inert -- nothing walks the containers yet.
    balRlpEncodeFunctions ++ "\n" ++
    blockAccessListBuilderFunctions ++ "\n" ++
  -- GH #10619: producer for the account_reads CONTAINER.  Fires
  -- UNCONDITIONALLY (state_tracker.py:139 records before consulting
  -- account_writes) -- unlike the code-read producer.
  accountReadRecordFunction ++ "\n" ++
  -- GH #10619 gate 2: the TRACKED account accessor over the raw
  -- account_at_header_state_root, mirroring the spec's get_account/pre_state
  -- pair.  Execution call sites route here; the 7 block_verdict/BAL-verification
  -- sites and the 1 guest-only site keep the raw entry, so the
  -- execution-vs-verification boundary is in the call graph rather than in a
  -- classification table (four instruments mis-counted that table -- see the
  -- docstring).
  accountAtHeaderStateRootTrackedFunction ++ "\n" ++
  -- GH #10619: code_reads producer + the TRACKED accessor.  Fires only on a
  -- pre-state FALLTHROUGH and skips EMPTY_CODE_HASH (state_tracker.py:263-270)
  -- -- the opposite condition from the account/storage recorders.
  codeReadRecordFunction ++ "\n" ++
  codeReadFetchFunction ++ "\n" ++
  -- GH #10619 gate 3: the PROMOTION BOUNDARY.  Recorders write the tx level;
  -- these merge it up and clear it, mirroring incorporate_tx_into_block
  -- (state_tracker.py:832, merge :858-861, clear :879-881).  discard_tx is what
  -- makes fork.py:745-752's never-promoted throwaway state expressible.
  readSetsMergeOneFunction ++ "\n" ++
  readSetsIncorporateTxFunction ++ "\n" ++
  readSetsDiscardTxFunction ++ "\n" ++
  -- #11118: code_covers/code_consistent/account_code_consistent unlinked (dead 43/46).
  stageBlockhashM29Function ++ "\n" ++   -- 3vc2p.3b: M29 recent-blockhash table reconstruction (dispatch staging)
  blockhashFromWitnessHeadersFunction ++ "\n" ++   -- 3vc2p.3b dep: find header by number -> keccak(header)
  headerExtractNumberFunction ++ "\n" ++   -- 3vc2p.3b dep: header NUMBER field extractor
  balAllAccountsNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3: all-accounts NON-STORAGE forward (balance/nonce)
  balAccountNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3 dep: per-account non-storage compare
  balAccountNonstorageFinalsFunction ++ "\n" ++   -- i3djw.3 dep: BAL account balance/nonce finals
  balAllAccountsNonstorageCoversFunction ++ "\n" ++   -- i3djw.3 reverse: exec net-change -> BAL presence
  multiTxNthContextFunction ++ "\n" ++
  -- g8zeq.1.4.2: per-tx EIP-8037 intrinsic state-gas + array assembly, used by
  -- block_verdict's block_state-gas floor check. tx_extract_to_address /
  -- tx_type_dispatch / rlp_list_nth_item / rlp_list_count_items / bgv_u32le are
  -- already in this closure; only the EIP-8037 state-gas bodies are new.
  eip8037TxStateGasFunction ++ "\n" ++
  txIntrinsicStateGasFunction ++ "\n" ++
  blockVerdictEip8037TxStateGasNetArrayFunction ++ "\n" ++
  eip8037BlockGasUsedFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  txEffectiveGasPricingFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  txUpfrontPrechargeFunction ++ "\n" ++
  txGasBalPostVerifyFunction ++ "\n" ++
  bvSumWithdrawalsToAddressFunction ++ "\n" ++
  accessListCountFunction ++ "\n" ++
  intrinsicGasAmsterdamCountsFunction ++ "\n" ++
  eip8037GasGateBundleFunction ++ "\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  multiTxRunningSenderBalanceStepFunction ++ "\n" ++
  senderDebitFromGasFunction ++ "\n" ++
  txGasBalPostVerifyRuntimeFunction ++ "\n" ++
  senderPostNonceConsistentFunction ++ "\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  eip7778RemainingBlockGasFromResultsFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  eip7702AuthorizationExtractSignatureFunction ++ "\n" ++
  eip7702AuthorizationSigningHashFunction ++ "\n" ++
  eip7702AuthorizationRecoverAddressFunction ++ "\n" ++
  eip7702WarmRecoveredAuthoritiesFunction ++ "\n" ++
  eip7702AuthorityAsOfFunction ++ "\n" ++
  eip7702AuthStatePrepareFunction ++ "\n" ++
  blockVerdictTxStateGasInlinePrepareFunction ++ "\n" ++
  blockVerdictTxStateGasInlineFinalizeFunction ++ "\n" ++
  -- #11533 follow-up: eip7702_authority_state_materialize probe-only (frozen S1 retired).
  blockVerdictGasResultArenaPrepareFunction ++ "\n" ++
  b1SenderCountTableFunction ++ "\n" ++
  b1SenderTableFindFunction ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  enrgU32leFunction ++ "\n" ++
  -- fhsxz.2.4.2.57.11.6.5.2.1 P1: link dispatcher_capture_exec_state_gas so the verdict can
  -- persist each tx's executed state gas into bvgr_tx_exec_state_gas (behavior-neutral substrate
  -- for the EIP-7778 2D state-dim).
  dispatcherCaptureExecStateGasFunction ++ "\n" ++
  dispatcherCaptureExecStateGasDifferentialFunction ++ "\n" ++
  -- bmvmx.3.2: per-tx sender recovery vs witness public_keys. block_verdict
  -- calls verify_public_keys_match_senders after public_keys_valid; the TX-side
  -- recovery stack (signature extractors + signing-hash + material/stage/
  -- recover/compare) is new here. tx_type_dispatch / tx_extract_* /
  -- rlp_list_nth_item/count_items / zkvm_keccak256 / u256_is_zero / u256_lt_be /
  -- bgv_u32le and the secp256k1 recover kernel are already in this closure.
  verifyPublicKeysSendersGuestFunctions ++ "\n" ++
  statelessVerdictV2Function ++ "\n" ++
  -- Keep the diagnostic verdict ELF linked with the same shared precompile
  -- selector/pricing + execution core as the shipped guest (#11163 item 2).
  precompileSharedSelectPriceFunction ++ "\n" ++
  precompileSharedExecuteFunction

/-- Data section for the embedded verdict closure. -/
def statelessVerdictV2GuestData : String :=
  ziskStatelessVerdictV2DataSection ++ "\n" ++
  -- GH #10619: storage_reads cursor + overflow flag.  Block-lifetime: nothing
  -- resets them per transaction and nothing restores them on rollback,
  -- mirroring restore_tx_state leaving storage_reads alone.
  storageReadLogDataSection ++ "\n" ++
  -- r59nm S2: storage_writes cursors + overflow flags, both levels.  The block
  -- pair is block-lifetime; the tx pair is cleared by write_sets_incorporate_tx,
  -- mirroring state_tracker.py:879-881.
  storageWriteMapDataSection ++ "\n" ++
  accountWriteMapDataSection ++ "\n" ++
  accountAgreementDataSection ++ "\n" ++
  balMapBuilderConsistentDataSection ++ "\n" ++
  balCanonicalSortDataSection ++ "\n" ++
  keccakIncrementalDataSection ++ "\n" ++
  accountReadLogDataSection ++ "\n" ++
  codeReadLogDataSection ++ "\n" ++
  readSetsBlockDataSection

end EvmAsm.Codegen
