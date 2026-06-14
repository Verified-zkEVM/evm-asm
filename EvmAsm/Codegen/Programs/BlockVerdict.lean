/-
  EvmAsm.Codegen.Programs.BlockVerdict

  Full state-transition verdict: rebuild header RLP, validate header pair,
  recompute post-state root with system writes + BAL + withdrawals, and compare
  against the payload state root. Static block_state_root arenas are sized from
  execution-specs limits; see docs/agents/eest-static-layout.md.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.SystemWrites
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.BalAccountStateRoot
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptDeleteAcc
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.AccountFieldGetters
import EvmAsm.Codegen.Programs.BalCodePreimages
import EvmAsm.Codegen.Programs.BalAccountAccessDescriptors
import EvmAsm.Codegen.Programs.BalStorageAccessDescriptors
import EvmAsm.Codegen.Programs.BlockVerdictModeledSystem
import EvmAsm.Codegen.Programs.BlockhashRequiredHeaders
import EvmAsm.Codegen.Programs.BlockRlpSize
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.BlockVerdictGasResults
import EvmAsm.Codegen.Programs.ReceiptsRootIndexed
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.BlockVerdictTransactions
import EvmAsm.Codegen.Programs.MptEncodeLeafBranch
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.SszWithdrawal
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.WithdrawalsRootIndexed
import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Programs.BlockVerdictSenderCounts

import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
import EvmAsm.Codegen.Programs.SenderBalanceDebit
import EvmAsm.Codegen.Programs.TxGasBalPostVerifyRuntime
import EvmAsm.Codegen.Programs.SenderPostNonceConsistent
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.SlotTupleSequencesMatch
import EvmAsm.Codegen.Programs.AccountTupleSequencesConsistent
import EvmAsm.Codegen.Programs.BalAllAccountsTupleSequences
import EvmAsm.Codegen.Programs.SimpleTransferRecipient
import EvmAsm.Codegen.Programs.SimpleTransferFeeRecipient
import EvmAsm.Codegen.Programs.BlockVerdictSysChange
import EvmAsm.Codegen.Programs.BlockVerdictChainConfig
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictDataSection
import EvmAsm.Codegen.Programs.BlockVerdictRuntimePayload
import EvmAsm.Codegen.Programs.BlockVerdictStateRoot
import EvmAsm.Codegen.Programs.BlockVerdictFunction
namespace EvmAsm.Codegen

open EvmAsm.Rv64

/- `zisk_stateless_verdict_v2`: probe. Fed the SAME `-i` input as the guest.
   Output OUTPUT+0 = verdict bit (system writes + withdrawals modeled). -/
def ziskStatelessVerdictV2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  jal ra, stateless_verdict_v2\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)            # OUTPUT+0 = verdict bit\n" ++
  "  la t1, bv_fail_code; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, bv_header_status; ld t2, 0(t1); sd t2, 16(t0)\n" ++
  "  la t1, bv_state_status; ld t2, 0(t1); sd t2, 24(t0)\n" ++
  "  la t1, bsr_bal_count; ld t2, 0(t1); sd t2, 32(t0)\n" ++
  "  la t1, bsr_fail_code; ld t2, 0(t1); sd t2, 40(t0)\n" ++
  "  la t1, bsr_change_count; ld t2, 0(t1); sd t2, 48(t0)\n" ++
  "  la t1, bsr_wl_v; ld t2, 0(t1); sd t2, 56(t0)\n" ++
  "  la t1, baacd_fail_code; ld t2, 0(t1); sd t2, 64(t0)\n" ++
  "  la t1, bacv_fail_code; ld t2, 0(t1); sd t2, 72(t0)\n" ++
  "  la t1, baap_fail_code; ld t2, 0(t1); sd t2, 80(t0)\n" ++
  "  la t1, sri_fail_index; ld t2, 0(t1); sd t2, 88(t0)\n" ++
  "  la t1, sri_fail_mode; ld t2, 0(t1); sd t2, 96(t0)\n" ++
  "  la t1, sri_fail_status; ld t2, 0(t1); sd t2, 104(t0)\n" ++
  "  la t1, bv_block_rlp_len; ld t2, 0(t1); sd t2, 112(t0)\n" ++
  "  la t1, brr_status; ld t2, 0(t1); sd t2, 120(t0)\n" ++
  "  la t1, brr_control; ld t2, 0(t1); sd t2, 128(t0)\n" ++
  "  la t1, brr_append_status; ld t2, 0(t1); sd t2, 136(t0)\n" ++
  "  la t1, brr_records; ld t2, 0(t1); sd t2, 144(t0)\n" ++
  "  la t1, brr_records; ld t2, 8(t1); sd t2, 152(t0)\n" ++
  "  la t1, brr_records; ld t2, 16(t1); sd t2, 160(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 0(t1); sd t2, 168(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 8(t1); sd t2, 176(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 16(t1); sd t2, 184(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 24(t1); sd t2, 192(t0)\n" ++
  "  la t1, sv_params; ld t1, 0(t1); addi t1, t1, 52\n" ++
  "  ld t2, 0(t1); sd t2, 200(t0)\n" ++
  "  ld t2, 8(t1); sd t2, 208(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 216(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 224(t0)\n" ++
  "  la t1, bvgr_arena_status; ld t2, 0(t1); sd t2, 232(t0)\n" ++
  "  la t1, bvgr_arena_tx_count; ld t2, 0(t1); sd t2, 240(t0)\n" ++
  "  la t1, bvgr_arena_runtime_count; ld t2, 0(t1); sd t2, 248(t0)\n" ++
  "  la t1, bvgr_arena_status; ld t2, 0(t1); sd t2, 256(t0)\n" ++
  "  la t1, bvgr_arena_tx_count; ld t2, 0(t1); sd t2, 264(t0)\n" ++
  "  la t1, bvgr_arena_runtime_count; ld t2, 0(t1); sd t2, 272(t0)\n" ++
  "  la t1, bvgr_arena_fail_index; ld t2, 0(t1); sd t2, 280(t0)\n" ++
  "  la t1, bvgr_arena_substatus; ld t2, 0(t1); sd t2, 288(t0)\n" ++
  "  la t1, bv_eip7778_status; ld t2, 0(t1); sd t2, 296(t0)\n" ++
  "  la t1, bv_eip7778_index; ld t2, 0(t1); sd t2, 304(t0)\n" ++
  "  la t1, bv_eip7778_used; ld t2, 0(t1); sd t2, 312(t0)\n" ++
  "  la t1, bvgr_tx_gas_limits; ld t2, 0(t1); sd t2, 320(t0)\n" ++
  "  la t1, bvgr_block_gas_increments; ld t2, 0(t1); sd t2, 328(t0)\n" ++
  "  la t1, bvgr_receipt_gas_increments; ld t2, 0(t1); sd t2, 336(t0)\n" ++
  "  la t1, bv_simple_transfer_tx; ld t2, 0(t1); sd t2, 344(t0)\n" ++
  "  la t1, bv_tx_gas_precharge; ld t2, 0(t1); sd t2, 352(t0)\n" ++
  "  la t1, bv_simple_transfer_recipient; ld t2, 0(t1); sd t2, 360(t0)\n" ++
  "  la t1, bv_simple_transfer_fee_recipient; ld t2, 0(t1); sd t2, 368(t0)\n" ++
  "  la t1, bv_withdrawals_root_status; ld t2, 0(t1); sd t2, 376(t0)\n" ++
  "  la t1, bv_withdrawals_root_valid; ld t2, 0(t1); sd t2, 384(t0)\n" ++
  "  la t1, bv_tx_root_status; ld t2, 0(t1); sd t2, 392(t0)\n" ++
  "  la t1, svf_tx_count; ld t2, 0(t1); sd t2, 400(t0)\n" ++
  "  j .Lv2_pdone\n" ++
  zkvmSha256Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  txEip4844ValidateBlobHashesFunction ++ "\n" ++
  sszTxListVersionedHashesMatchFunction ++ "\n" ++
  txExtractToAddressFunction ++ "\n" ++
  txExtractValueFunction ++ "\n" ++
  txExtractDataSectionFunction ++ "\n" ++
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
  accountAtHeaderStateRootFunction ++ "\n" ++
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
  -- already linked above for the transactions/withdrawals root checks).
  headerExtractReceiptsRootFunction ++ "\n" ++
  blockValidateReceiptsRootIndexedFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  bloomEqFunction ++ "\n" ++
  blockVerdictFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  balSectionInfoFunction ++ "\n" ++
  balGasValidFunction ++ "\n" ++
  codeHashAtHeaderStateRootFunction ++ "\n" ++
  balCodePreimagesValidFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  txGasSenderBalLookupFunction ++ "\n" ++
  simpleTransferTxContextFunction ++ "\n" ++
  stageRuntimePayloadFunction ++ "\n" ++
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
  senderDebitFromGasFunction ++ "\n" ++
  txGasBalPostVerifyRuntimeFunction ++ "\n" ++
  senderPostNonceConsistentFunction ++ "\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  eip7778RemainingBlockGasFromResultsFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  blockVerdictGasResultArenaPrepareFunction ++ "\n" ++
  b1SenderCountTableFunction ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  enrgU32leFunction ++ "\n" ++
  eip7702NonceReuseGuardFunction ++ "\n" ++
  statelessVerdictV2Function ++ "\n" ++
  ".Lv2_pdone:"

end EvmAsm.Codegen
