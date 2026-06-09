/-
  EvmAsm.Codegen.Programs.BlockVerdictV2

  Probe unit and guest-closure definitions carved out of
  `Programs/BlockVerdict.lean` to satisfy the 1500-line file-size hard cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdict
import EvmAsm.Codegen.Programs.EvmBasic
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.SszWithdrawal

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch
import EvmAsm.Codegen.Programs.BlockVerdictContractStage
import EvmAsm.Codegen.Programs.BlockVerdictSelfContained
import EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount
import EvmAsm.Codegen.Programs.BlockVerdictContractStorage

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
    stageRuntimePayloadCodeFunction ++ "\n" ++
    ".Lstateless_verdict_v2_debug_after_runtime_dispatcher:\n"
  dataAsm     :=
    ziskStatelessVerdictV2DataSection ++ "\n" ++
    executionRequestsHashShaDataSection ++ "\n" ++
    emitRuntimeDispatcherDataSectionSharedGuest callFrameGuestRegistry
}

/-- The full stateless_verdict_v2 asm closure for embedding in the GUEST epilogue,
    OMITTING rlp_list_nth_item + rlp_field_to_u64 (the guest already defines those,
    so they would be duplicate labels). The guest jal's `stateless_verdict_v2` and
    writes its bit to OUTPUT[32]. -/
def statelessVerdictV2GuestClosure : String :=
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
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
  stageRuntimePayloadCodeFunction ++ "\n" ++
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
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  eip7778RemainingBlockGasFromResultsFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  blockVerdictGasResultArenaPrepareFunction ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  enrgU32leFunction ++ "\n" ++
  eip7702NonceReuseGuardFunction ++ "\n" ++
  statelessVerdictV2Function

/-- Data section for the embedded verdict closure. -/
def statelessVerdictV2GuestData : String :=
  ziskStatelessVerdictV2DataSection

end EvmAsm.Codegen
