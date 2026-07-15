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
import EvmAsm.Codegen.Programs.BlockVerdictDepositFallback
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.SystemCallStoragePreload
import EvmAsm.Codegen.Programs.WitnessCodeLookup

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch
import EvmAsm.Codegen.Programs.BlockVerdictContractStage
import EvmAsm.Codegen.Programs.BlockVerdictSingleTxLog
import EvmAsm.Codegen.Programs.BlockVerdictSelfContained
import EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount
import EvmAsm.Codegen.Programs.BlockVerdictContractStorage
import EvmAsm.Codegen.Programs.BlockVerdictDispatchTx
import EvmAsm.Codegen.Programs.SeedTxAccessList
import EvmAsm.Codegen.Programs.BalAddrExecLogKey
import EvmAsm.Codegen.Programs.BalStorageMatchesExecLog
import EvmAsm.Codegen.Programs.BalStorageCoversExecLog
import EvmAsm.Codegen.Programs.BalAllAccountsStorage
import EvmAsm.Codegen.Programs.BalAllAccountsCodeCovers
import EvmAsm.Codegen.Programs.BalAllAccountsCode
import EvmAsm.Codegen.Programs.BalAccountCodeConsistent
import EvmAsm.Codegen.Programs.StageBlockhashM29
import EvmAsm.Codegen.Programs.TxPubkey
import EvmAsm.Codegen.Programs.VerifyPublicKeysSenders
import EvmAsm.Codegen.Programs.BalAllAccountsNonstorage
import EvmAsm.Codegen.Programs.BalAllAccountsNonstorageCovers
import EvmAsm.Codegen.Programs.BalAccountNonstorageConsistent
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BalStorageReadsExecLog
import EvmAsm.Codegen.Programs.ExecLogLatestValue
import EvmAsm.Codegen.Programs.CommittedStorageSnapshot
import EvmAsm.Codegen.Programs.CommittedStorageLookup
import EvmAsm.Codegen.Programs.BlockVerdictTxsIndependent
import EvmAsm.Codegen.Programs.BlockVerdictMultiTx
import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.Eip7702Authority
import EvmAsm.Codegen.Programs.MultiTxSenderDebit
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.SystemCallStoragePreload
import EvmAsm.Codegen.Programs.AmsterdamSystemTx

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
    balRecipientStorageKeysFunction ++ "\n" ++
    balRecipientStorageReadsKeysFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
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
    -- bmvmx.1.6.4.2.b: callee-storage enumeration + its LE exec-log key helper.
    balAddrToExecLogKeyFunction ++ "\n" ++
    seedCalleeStorageFunction ++ "\n" ++
    -- bmvmx.1.6.2: exec-vs-BAL recipient storage consistency callees, now referenced by
    -- block_verdict's contract-dispatch tail (rlp_list_nth_item/count_items already present).
    balStorageChangeValuesFunction ++ "\n" ++
    balStorageMatchesExecLogFunction ++ "\n" ++
    balStorageCoversExecLogFunction ++ "\n" ++   -- bmvmx.1.6.5: exec ⊆ BAL (omission detection)
  balAllAccountsStorageConsistentFunction ++ "\n" ++   -- bmvmx.1.6.4.3: all-accounts forward+reverse
  balSlotTupleSequenceFunction ++ "\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  systemUserExecLogSlotTuplesFunction ++ "\n" ++
  execLogLatestValueFunction ++ "\n" ++   -- fhsxz.2.4.2.57.11.6.3.2: cross-tx storage threading lookup
  slotTupleSequencesMatchFunction ++ "\n" ++
  accountTupleSequencesConsistentFunction ++ "\n" ++
  balAllAccountsTupleSequencesConsistentFunction ++ "\n" ++   -- bmvmx.1.6.6: per-slot tuple-sequence all-accounts
  balStorageReadsInExecLogFunction ++ "\n" ++   -- bmvmx.1.6.7: storage_reads exec consistency
  balAllAccountsCodeCoversFunction ++ "\n" ++   -- i3djw: all-accounts CODE reverse (hidden created/destroyed account)
  balAllAccountsCodeConsistentFunction ++ "\n" ++   -- i3djw.4: all-accounts CODE forward (+ EIP-7702 skip)
  stageBlockhashM29Function ++ "\n" ++   -- 3vc2p.3b: M29 recent-blockhash table reconstruction (dispatch staging)
  blockhashFromWitnessHeadersFunction ++ "\n" ++   -- 3vc2p.3b dep: find header by number -> keccak(header)
  headerExtractNumberFunction ++ "\n" ++   -- 3vc2p.3b dep: header NUMBER field extractor
  balAccountCodeConsistentFunction ++ "\n" ++   -- i3djw.4 dep: per-account CODE compare
  balAllAccountsNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3: all-accounts NON-STORAGE forward (balance/nonce)
  balAccountNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3 dep: per-account non-storage compare
  balAccountNonstorageFinalsFunction ++ "\n" ++   -- i3djw.3 dep: BAL account balance/nonce finals
  balAllAccountsNonstorageCoversFunction ++ "\n" ++   -- i3djw.3 reverse: exec net-change -> BAL presence
    -- .6.2.2.2.a: multi-tx dispatch helpers (independence guard + per-index tx
    -- context extractor) wired ahead of the gated multi-tx loop (.6.2.2.2.b).
    btiScanTuplesFunction ++ "\n" ++
    btiScanStorageChangesFunction ++ "\n" ++
    balTxsIndependentFunction ++ "\n" ++
    multiTxNthContextFunction ++ "\n" ++
    rlpFieldToU64Function ++ "\n" ++
    -- bmvmx.3.2: mirror the guest closure's per-tx sender-recovery stack so this
    -- debug verdict ELF links (block_verdict calls verify_public_keys_match_senders).
    verifyPublicKeysSendersGuestFunctions ++ "\n" ++
    -- 8uld3.2.3 / .63.1.6.2.3: mirror the request-derivation and receipts-consensus
    -- bodies that block_verdict now reaches inside the embedded guest closure. The
    -- standalone debug ELF does not include statelessGuestUnit.epilogueAsm, so these
    -- symbols must be emitted here as well.
    deriveBlockSystemRequestsFunction ++ "\n" ++
    deriveWithdrawalRequestsFunction ++ "\n" ++
    deriveConsolidationRequestsFunction ++ "\n" ++
    deriveBuilderDepositRequestsFunction ++ "\n" ++
    deriveBuilderExitRequestsFunction ++ "\n" ++
    stageSystemCallFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    blockVerdictAllDirectDepositTxsFunction ++ "\n" ++
    blockVerdictAppendDirectDepositFunction ++ "\n" ++
    parseDepositRequestsFunction ++ "\n" ++
    extractDepositDataFunction ++ "\n" ++
    materializeLogRecordsFunction ++ "\n" ++
    assembleExecutionRequestsFunction ++ "\n" ++
    requestsHashVerifyFunction ++ "\n" ++
    stagePredeployStoragePreloadFunction ++ "\n" ++
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
    executionRequestsHashShaDataSection ++ "\n" ++
    -- Data labels for the request-derivation/predeploy-storage helpers above.
    -- ziskStatelessVerdictV2DataSection already owns the receipt-consensus scratch.
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    "scc_preload_ptr:\n  .zero 8\nscc_preload_count:\n  .zero 8\n" ++
    ".balign 8\n" ++
    "scc_system_addr:\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe\n" ++
    ".balign 8\n" ++
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
    withdrawalRequestPredeployAddrData ++
    consolidationRequestPredeployAddrData ++
    builderContractAddrData ++
    deriveBlockSystemRequestsData ++ "\n" ++
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
    ".balign 8\n" ++
    "pdr_out:\n  .zero 2048\n" ++
    "pdr_status:\n  .zero 8\n" ++
    "rhv_hash:\n  .zero 32\n" ++
    stagePredeployStoragePreloadData ++ "\n" ++
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
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  blockValidateWithdrawalsRootIndexedFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  amsterdamBlobGasPriceFunction ++ "\n" ++
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
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountAccessOutcomeDescriptorsFunction ++ "\n" ++
  balStorageAccessOutcomeDescriptorsFunction ++ "\n" ++
  balAccountRecordArrayFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++
  bsrSysChangeFunction ++ "\n" ++
  bsrBeaconChangeFunction ++ "\n" ++
  bsrApplyModeledSystemPostFieldsFunction ++ "\n" ++
  captureSystemStorageExecRowsFunction ++ "\n" ++
  appendModeledSystemStorageTupleRowsFunction ++ "\n" ++
  mptBoundedBuilderFrontEndFunction ++ "\n" ++
  blockStateRootFunction ++ "\n" ++
  codesBlockhashRequiredHeadersFunction ++ "\n" ++
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
  balGasValidFunction ++ "\n" ++
  accountAtHeaderStateRootFunction ++ "\n" ++
  codeHashAtHeaderStateRootFunction ++ "\n" ++
  balCodePreimagesValidFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  txGasSenderBalLookupFunction ++ "\n" ++
  simpleTransferTxContextFunction ++ "\n" ++
  stageRuntimePayloadFunction ++ "\n" ++
  stageCreationRuntimePayloadFunction ++ "\n" ++
  blockVerdictSingleTxCreationRuntimeFunction ++ "\n" ++
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
  balRecipientStorageKeysFunction ++ "\n" ++
  balRecipientStorageReadsKeysFunction ++ "\n" ++
  stageRuntimePayloadCodeFunction ++ "\n" ++
  blockVerdictSingleTxTopLevelLogFunction ++ "\n" ++
  -- .6.2.2.1: contract-recipient runtime gas-measurement tail extracted from
  -- block_verdict so the multi-tx dispatch loop can reuse it.
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
  -- bmvmx.1.6.4.2.b: callee-storage enumeration + its LE exec-log key helper.
  balAddrToExecLogKeyFunction ++ "\n" ++
  seedCalleeStorageFunction ++ "\n" ++
  -- bmvmx.1.6.2: exec-vs-BAL recipient storage consistency callees, referenced by
  -- block_verdict's contract-dispatch tail. rlp_list_nth_item/count_items already in closure.
  balStorageChangeValuesFunction ++ "\n" ++
  balStorageMatchesExecLogFunction ++ "\n" ++
  balStorageCoversExecLogFunction ++ "\n" ++   -- bmvmx.1.6.5: exec ⊆ BAL (omission detection)
  balAllAccountsStorageConsistentFunction ++ "\n" ++   -- bmvmx.1.6.4.3: all-accounts forward+reverse
  balSlotTupleSequenceFunction ++ "\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  systemUserExecLogSlotTuplesFunction ++ "\n" ++
  execLogLatestValueFunction ++ "\n" ++   -- fhsxz.2.4.2.57.11.6.3.2: cross-tx storage threading lookup
  committedStorageSnapshotUpsertFunction ++ "\n" ++
  committedStorageLatestValueFunction ++ "\n" ++
  committedStorageChunkedSnapshotUpsertFunction ++ "\n" ++
  committedStorageChunkedLatestValueFunction ++ "\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  accountTupleSequencesConsistentFunction ++ "\n" ++
  balAllAccountsTupleSequencesConsistentFunction ++ "\n" ++   -- bmvmx.1.6.6: per-slot tuple-sequence all-accounts
  balStorageReadsInExecLogFunction ++ "\n" ++   -- bmvmx.1.6.7: storage_reads exec consistency
  balAllAccountsCodeCoversFunction ++ "\n" ++   -- i3djw: all-accounts CODE reverse (hidden created/destroyed account)
  balAllAccountsCodeConsistentFunction ++ "\n" ++   -- i3djw.4: all-accounts CODE forward (+ EIP-7702 skip)
  stageBlockhashM29Function ++ "\n" ++   -- 3vc2p.3b: M29 recent-blockhash table reconstruction (dispatch staging)
  blockhashFromWitnessHeadersFunction ++ "\n" ++   -- 3vc2p.3b dep: find header by number -> keccak(header)
  headerExtractNumberFunction ++ "\n" ++   -- 3vc2p.3b dep: header NUMBER field extractor
  balAccountCodeConsistentFunction ++ "\n" ++   -- i3djw.4 dep: per-account CODE compare
  balAllAccountsNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3: all-accounts NON-STORAGE forward (balance/nonce)
  balAccountNonstorageConsistentFunction ++ "\n" ++   -- i3djw.3 dep: per-account non-storage compare
  balAccountNonstorageFinalsFunction ++ "\n" ++   -- i3djw.3 dep: BAL account balance/nonce finals
  balAllAccountsNonstorageCoversFunction ++ "\n" ++   -- i3djw.3 reverse: exec net-change -> BAL presence
  -- .6.2.2.2.a: multi-tx dispatch helpers — bal_txs_independent (independence
  -- guard) + its bti_scan_* walkers, and multi_tx_nth_context (per-index tx
  -- context extractor) — wired ahead of the gated multi-tx loop (.6.2.2.2.b).
  btiScanTuplesFunction ++ "\n" ++
  btiScanStorageChangesFunction ++ "\n" ++
  balTxsIndependentFunction ++ "\n" ++
  multiTxNthContextFunction ++ "\n" ++
  -- g8zeq.1.4.2: per-tx EIP-8037 intrinsic state-gas + array assembly, used by
  -- block_verdict's block_state-gas floor check. tx_extract_to_address /
  -- tx_type_dispatch / rlp_list_nth_item / rlp_list_count_items / bgv_u32le are
  -- already in this closure; only the EIP-8037 state-gas bodies are new.
  eip8037TxStateGasFunction ++ "\n" ++
  txIntrinsicStateGasFunction ++ "\n" ++
  blockVerdictTxStateGasArrayFunction ++ "\n" ++
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
  simpleTransferRecipientBalVerifyFunction ++ "\n" ++
  simpleTransferFeeRecipientBalVerifyFunction ++ "\n" ++
  bvSumWithdrawalsToAddressFunction ++ "\n" ++
  accessListCountFunction ++ "\n" ++
  intrinsicGasAmsterdamCountsFunction ++ "\n" ++
  eip8037TxGasGateFunction ++ "\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  multiTxRunningSenderBalanceStepFunction ++ "\n" ++
  multiTxSequentialGasSettleStepFunction ++ "\n" ++
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
  balAccountNonceBeforeIndexFunction ++ "\n" ++
  txEip7702ExistingAuthorityRefundFunction ++ "\n" ++
  eip7702AuthNonstorageEffectsFunction ++ "\n" ++
  blockVerdictEip7702AuthNonstorageEffectsArrayFunction ++ "\n" ++
  blockVerdictGasResultArenaPrepareFunction ++ "\n" ++
  b1SenderCountTableFunction ++ "\n" ++
  b1SenderTableFindFunction ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  enrgU32leFunction ++ "\n" ++
  eip7702NonceReuseGuardFunction ++ "\n" ++
  -- fhsxz.2.4.2.57.11.6.5.2.1 P1: link dispatcher_capture_exec_state_gas so the verdict can
  -- persist each tx's executed state gas into bvgr_tx_exec_state_gas (behavior-neutral substrate
  -- for the EIP-7778 2D state-dim; the array is filled but not yet read by eip8037_state_used_before_tx).
  dispatcherCaptureExecStateGasFunction ++ "\n" ++
  -- bmvmx.3.2: per-tx sender recovery vs witness public_keys. block_verdict
  -- calls verify_public_keys_match_senders after public_keys_valid; the TX-side
  -- recovery stack (signature extractors + signing-hash + material/stage/
  -- recover/compare) is new here. tx_type_dispatch / tx_extract_* /
  -- rlp_list_nth_item/count_items / zkvm_keccak256 / u256_is_zero / u256_lt_be /
  -- bgv_u32le and the secp256k1 recover kernel are already in this closure.
  verifyPublicKeysSendersGuestFunctions ++ "\n" ++
  statelessVerdictV2Function

/-- Data section for the embedded verdict closure. -/
def statelessVerdictV2GuestData : String :=
  ziskStatelessVerdictV2DataSection

end EvmAsm.Codegen
