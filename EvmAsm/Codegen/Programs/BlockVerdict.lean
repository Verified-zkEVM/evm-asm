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
import EvmAsm.Codegen.Programs.StorageWriteMap
import EvmAsm.Codegen.Programs.SystemWrites
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptDeleteAcc
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.MptBoundedSort
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.AccountFieldGetters
import EvmAsm.Codegen.Programs.BalCodePreimages
import EvmAsm.Codegen.Programs.BalAccountAccessDescriptors
import EvmAsm.Codegen.Programs.BalStorageAccessDescriptors
import EvmAsm.Codegen.Programs.BalAccountChangeDescriptor
import EvmAsm.Codegen.Programs.BalAccountRecordArray
import EvmAsm.Codegen.Programs.BlockVerdictModeledSystem
import EvmAsm.Codegen.Programs.BlockRlpSize
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.BlockVerdictGasResults
import EvmAsm.Codegen.Programs.DispatcherExecStateGas
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
import EvmAsm.Codegen.Programs.CommittedStorageLookup

import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.PrecompileSharedExecute
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
import EvmAsm.Codegen.Programs.SenderBalanceDebit
import EvmAsm.Codegen.Programs.TxGasBalPostVerifyRuntime
import EvmAsm.Codegen.Programs.SenderPostNonceConsistent
import EvmAsm.Codegen.Programs.SimpleTransferRecipient
import EvmAsm.Codegen.Programs.SimpleTransferFeeRecipient
import EvmAsm.Codegen.Programs.BlockVerdictSysChange
import EvmAsm.Codegen.Programs.BlockVerdictChainConfig
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictDataSection
import EvmAsm.Codegen.Programs.BlockVerdictRuntimePayload
import EvmAsm.Codegen.Programs.WitnessCodeLookup
import EvmAsm.Codegen.Programs.BlockVerdictSingleTxLog
import EvmAsm.Codegen.Programs.BlockVerdictStateRoot
import EvmAsm.Codegen.Programs.BlockVerdictFunction
import EvmAsm.Codegen.Programs.MultiTxSenderDebit
import EvmAsm.Codegen.Programs.DispatcherTxGasSettle
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
namespace EvmAsm.Codegen

open EvmAsm.Rv64

/- `zisk_stateless_verdict_v2`: probe. Fed the SAME `-i` input as the guest.
   Output OUTPUT+0 = verdict bit (system writes + withdrawals modeled).

   ⚠️ THIS IS AN OFFSET-ADDRESSED DEBUG CONTRACT, NOT A PRIVATE SCRATCH BUFFER.
   `scripts/codegen-eest-stateless-check.sh`'s `format_verdict_debug` decodes it
   POSITIONALLY, via a bash label array that names each 8-byte word. The stores
   below are the ONLY ground truth for what each offset holds; the label array is
   an interpretation of them and can drift. **If you add, remove or reorder a
   store here, update that array in the same commit** — otherwise every reader
   silently mis-labels every field after the change.

   Verified 2026-08-02 (GH #11105 follow-up): the label array matches these
   stores, field for field. Recorded because four agents read this buffer by
   offset and the mapping had to be re-derived from the emitter to be trusted —
   a field NAME is not a contract, and a control row only validates the fields
   that happen to be NON-ZERO in it.

   The map, as emitted below:
     +0   verdict bit                        +96  bvgr_receipt_gas_increments[1]
     +8   bv_fail_code                       +104 bvgr_tx_total_state_gas[0]
         bv_fail_code VALUES (not offsets) for the former catch-all 40 split:
          40 sender_nonce (tx.nonce mismatch only)
          68 sender_count_table  69 sender_resolve  70 sender_not_eoa (reserved→#11533)
          71 sender_inclusion    72 auth_prepare
         (73-76 not assigned: frozen S1 deleted by #11536)
        Sinks: BlockVerdictReceiptsTail.lean .Lbv_*_fail. Emitter layout unchanged.
     +16  bv_header_status                   +112 bvgr_tx_total_state_gas[1]
     +24  bv_state_status                    +120 bv_exact_net_status
     +32  bsr_bal_count                      +128 bv_exact_net_index
     +40  bsr_fail_code                      +136 bv_exact_block_status
     +48  bsr_change_count                   +144 bv_exact_header_gas_used
     +56  bsr_wl_v                           +152 bv_exact_expected_gas_used
     +64  baacd_fail_code                    +160 brr_records[16]
     +72  bacv_fail_code                     +168 sv_recomputed  (32 bytes)
     +80  baap_fail_code                     +200 payload state root (32 bytes)
     +88  bvgr_receipt_gas_increments[0]     +232 onward: gas-arena status/counts -/
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
  "  la t1, bvgr_receipt_gas_increments; ld t2, 0(t1); sd t2, 88(t0)\n" ++
  "  la t1, bvgr_receipt_gas_increments; ld t2, 8(t1); sd t2, 96(t0)\n" ++
  "  la t1, bvgr_tx_total_state_gas; ld t2, 0(t1); sd t2, 104(t0)\n" ++
  "  la t1, bvgr_tx_total_state_gas; ld t2, 8(t1); sd t2, 112(t0)\n" ++
  "  la t1, bv_exact_net_status; ld t2, 0(t1); sd t2, 120(t0)\n" ++
  "  la t1, bv_exact_net_index; ld t2, 0(t1); sd t2, 128(t0)\n" ++
  "  la t1, bv_exact_block_status; ld t2, 0(t1); sd t2, 136(t0)\n" ++
  "  la t1, bv_exact_header_gas_used; ld t2, 0(t1); sd t2, 144(t0)\n" ++
  "  la t1, bv_exact_expected_gas_used; ld t2, 0(t1); sd t2, 152(t0)\n" ++
  "  la t1, brr_records; ld t2, 16(t1); sd t2, 160(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 0(t1); sd t2, 168(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 8(t1); sd t2, 176(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 16(t1); sd t2, 184(t0)\n" ++
  "  la t1, sv_recomputed; ld t2, 24(t1); sd t2, 192(t0)\n" ++
  "  la t1, sv_params; ld t1, 0(t1); beqz t1, .Lv2_dbg_no_payload_root; addi t1, t1, 52\n" ++
  "  ld t2, 0(t1); sd t2, 200(t0)\n" ++
  "  ld t2, 8(t1); sd t2, 208(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 216(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 224(t0)\n" ++
  ".Lv2_dbg_no_payload_root:\n" ++
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
  -- #10685 PR2: bv_simple_transfer_tx BSS deleted with bv_emit_single_tx_tl7708.
  -- Slot 344 left unwritten (same sibling-unit trap class as 360/368).
  "  la t1, bv_tx_gas_precharge; ld t2, 0(t1); sd t2, 352(t0)\n" ++
  -- #10685: bv_simple_transfer_recipient / fee_recipient BSS deleted with the
  -- dead bal_verify twins. zisk_stateless_verdict_v2 debug dump must not la them
  -- (sibling-unit trap: dead in guest, live only as dump mirrors). Slots 360/368
  -- left unwritten; later dumps keep their historical offsets.
  "  la t1, bv_withdrawals_root_status; ld t2, 0(t1); sd t2, 376(t0)\n" ++
  "  la t1, bv_withdrawals_root_valid; ld t2, 0(t1); sd t2, 384(t0)\n" ++
  "  la t1, bv_tx_root_status; ld t2, 0(t1); sd t2, 392(t0)\n" ++
  "  la t1, svf_tx_count; ld t2, 0(t1); sd t2, 400(t0)\n" ++
  "  la t1, bv_receipts_completeness_shape; ld t2, 0(t1); sd t2, 408(t0)\n" ++
  "  la t1, bv_receipts_enforce_enabled; ld t2, 0(t1); sd t2, 416(t0)\n" ++
  "  la t1, bv_receipts_validator_status; ld t2, 0(t1); sd t2, 424(t0)\n" ++
  "  la t1, bv_receipts_encoder_status; ld t2, 0(t1); sd t2, 432(t0)\n" ++
  "  la t1, bv_receipt_logs_status; ld t2, 0(t1); sd t2, 440(t0)\n" ++
  "  la t1, bv_block_log_overflow; ld t2, 0(t1); sd t2, 448(t0)\n" ++
  "  la t1, bv_dispatch_runtime_status; ld t2, 0(t1); sd t2, 456(t0)\n" ++
  "  la t1, bv_runtime_completeness_status; ld t2, 0(t1); sd t2, 464(t0)\n" ++
  "  la t1, widx_build_status; ld t2, 0(t1); sd t2, 536(t0)\n" ++
  "  la t1, widx_build_section_len; ld t2, 0(t1); sd t2, 544(t0)\n" ++
  "  la t1, widx_build_count; ld t2, 0(t1); sd t2, 552(t0)\n" ++
  "  la t1, widx_enabled; ld t2, 0(t1); sd t2, 560(t0)\n" ++
  "  la t1, wlh_lookup_calls; ld t2, 0(t1); sd t2, 568(t0)\n" ++
  "  la t1, wlh_indexed_calls; ld t2, 0(t1); sd t2, 576(t0)\n" ++
  "  la t1, wlh_indexed_hits; ld t2, 0(t1); sd t2, 584(t0)\n" ++
  "  la t1, wlh_indexed_misses; ld t2, 0(t1); sd t2, 592(t0)\n" ++
  "  la t1, wlh_linear_calls; ld t2, 0(t1); sd t2, 600(t0)\n" ++
  "  la t1, wlh_linear_hits; ld t2, 0(t1); sd t2, 608(t0)\n" ++
  "  la t1, wlh_linear_misses; ld t2, 0(t1); sd t2, 616(t0)\n" ++
  "  la t1, wlh_linear_iterations; ld t2, 0(t1); sd t2, 624(t0)\n" ++
  "  la t1, wlh_linear_last_section_len; ld t2, 0(t1); sd t2, 632(t0)\n" ++
  "  la t1, wlh_linear_max_section_len; ld t2, 0(t1); sd t2, 640(t0)\n" ++
  "  la t1, svf_codes_len; ld t2, 0(t1); sd t2, 648(t0)\n" ++
  "  la t1, svf_headers_len; ld t2, 0(t1); sd t2, 656(t0)\n" ++
  "  la t1, svf_headers_count; ld t2, 0(t1); sd t2, 664(t0)\n" ++
  "  la t1, c1_dstatus; ld t2, 0(t1); sd t2, 672(t0)\n" ++
  "  la t1, c1_dlen; ld t2, 0(t1); sd t2, 680(t0)\n" ++
  "  li t2, 32768; sd t2, 688(t0)\n" ++
  "  li t2, 81920; sd t2, 696(t0)\n" ++
  "  la t1, dbsr_wlen; ld t2, 0(t1); sd t2, 704(t0)\n" ++
  "  la t1, dbsr_clen; ld t2, 0(t1); sd t2, 712(t0)\n" ++
  "  li t2, 2048; sd t2, 720(t0)\n" ++
  "  la t1, c1_er_assembled_len; ld t2, 0(t1); sd t2, 728(t0)\n" ++
  "  li t2, 32768; sd t2, 736(t0)\n" ++
  "  la t1, c1_erh_status; ld t2, 0(t1); sd t2, 744(t0)\n" ++
  "  li t2, 1572865; sd t2, 752(t0)\n" ++
  "  la t1, c1_notx_deposit_body_len; ld t2, 0(t1); sd t2, 760(t0)\n" ++
  "  li t2, " ++ toString bvMtxArenaTxCap ++ "; sd t2, 768(t0)\n" ++
  "  li t2, " ++ toString bmvFullTxCapacity ++ "; sd t2, 776(t0)\n" ++
  "  li t2, " ++ toString bvMtxU64ArenaBytes ++ "; sd t2, 784(t0)\n" ++
  "  li t2, " ++ toString bvMtxLogWindowBytes ++ "; sd t2, 792(t0)\n" ++
  "  li t2, " ++ toString bvMtxSkipListEntries ++ "; sd t2, 800(t0)\n" ++
  "  la t1, bv_mtx_skip_count; ld t2, 0(t1); sd t2, 808(t0)\n" ++
  "  la t1, bv_mtx_i; ld t2, 0(t1); sd t2, 816(t0)\n" ++
  "  li t2, " ++ toString bvMtxSenderCountEntries ++ "; sd t2, 824(t0)\n" ++
  "  la t1, bv_b1_sender_count; ld t2, 0(t1); sd t2, 832(t0)\n" ++
  "  li t2, " ++ toString bvMtxSenderBalanceEntries ++ "; sd t2, 840(t0)\n" ++
  "  la t1, bv_b2_count; ld t2, 0(t1); sd t2, 848(t0)\n" ++
  "  li t2, " ++ toString storageWritesCapacity ++ "; sd t2, 856(t0)\n" ++
  "  la t1, storage_writes_count; ld t2, 0(t1); sd t2, 864(t0)\n" ++
  "  li t2, 0; sd t2, 872(t0)  # retired nonce-seen debug counter\n" ++
  "  li t2, 16; sd t2, 880(t0)\n" ++
  "  la t1, bv_tx_count; ld t2, 0(t1); sd t2, 888(t0)\n" ++
  "  la t1, brr_control; ld t2, 0(t1); sd t2, 896(t0)\n" ++
  "  li t2, " ++ toString bvReceiptRecordCapacity ++ "; sd t2, 904(t0)\n" ++
  "  la t1, brr_status; ld t2, 0(t1); sd t2, 912(t0)\n" ++
  "  la t1, brr_append_status; ld t2, 0(t1); sd t2, 920(t0)\n" ++
  "  la t1, bv_block_log_count; ld t2, 0(t1); sd t2, 928(t0)\n" ++
  "  li t2, " ++ toString bvBlockLogDescCapacity ++ "; sd t2, 936(t0)\n" ++
  "  la t1, bv_block_log_data_used; ld t2, 0(t1); sd t2, 944(t0)\n" ++
  "  li t2, " ++ toString bvBlockLogDataBytes ++ "; sd t2, 952(t0)\n" ++
  "  la t1, bv_logs_rlp_arena_used; ld t2, 0(t1); sd t2, 960(t0)\n" ++
  "  li t2, " ++ toString bvLogsRlpArenaBytes ++ "; sd t2, 968(t0)\n" ++
  "  la t1, bv_logs_rlp_len; ld t2, 0(t1); sd t2, 976(t0)\n" ++
  "  la t1, bv_receipts_rlp_len; ld t2, 0(t1); sd t2, 984(t0)\n" ++
  "  li t2, " ++ toString bvReceiptsRlpBytes ++ "; sd t2, 992(t0)\n" ++
  "  la t1, brr_control; ld t2, 0(t1); slli t2, t2, 8; sd t2, 1000(t0)\n" ++
  "  li t2, " ++ toString bvRecordBloomsBytes ++ "; sd t2, 1008(t0)\n" ++
  "  la t1, bv_receipt_logs_status; ld t2, 0(t1); sd t2, 1016(t0)\n" ++
  "  la t1, bv_block_log_overflow; ld t2, 0(t1); sd t2, 1024(t0)\n" ++
  "  la t1, wcidx_build_status; ld t2, 0(t1); sd t2, 1032(t0)\n" ++
  "  la t1, wcidx_build_section_len; ld t2, 0(t1); sd t2, 1040(t0)\n" ++
  "  la t1, wcidx_build_count; ld t2, 0(t1); sd t2, 1048(t0)\n" ++
  "  la t1, wcidx_enabled; ld t2, 0(t1); sd t2, 1056(t0)\n" ++
  "  la t1, wclh_lookup_calls; ld t2, 0(t1); sd t2, 1064(t0)\n" ++
  "  la t1, wclh_indexed_calls; ld t2, 0(t1); sd t2, 1072(t0)\n" ++
  "  la t1, wclh_indexed_hits; ld t2, 0(t1); sd t2, 1080(t0)\n" ++
  "  la t1, wclh_indexed_misses; ld t2, 0(t1); sd t2, 1088(t0)\n" ++
  "  la t1, wclh_linear_calls; ld t2, 0(t1); sd t2, 1096(t0)\n" ++
  "  la t1, wclh_linear_hits; ld t2, 0(t1); sd t2, 1104(t0)\n" ++
  "  la t1, wclh_linear_misses; ld t2, 0(t1); sd t2, 1112(t0)\n" ++
  "  la t1, wclh_linear_iterations; ld t2, 0(t1); sd t2, 1120(t0)\n" ++
  "  j .Lv2_pdone\n" ++
  zkvmSha256Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
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
  -- already linked above for the transactions/withdrawals root checks).
  headerExtractReceiptsRootFunction ++ "\n" ++
  blockValidateReceiptsRootIndexedFunction ++ "\n" ++
  headerExtractLogsBloomFunction ++ "\n" ++
  bloomEqFunction ++ "\n" ++
  storageWritesBlockLatestValueFunction ++ "\n" ++
  blockVerdictFunction ++ "\n" ++
  -- #10685 PR2: bv_emit_single_tx_tl7708 unlinked from guest; KEEP Function for probes.
  rlpListCountItemsFunction ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  balSectionInfoFunction ++ "\n" ++
  -- #11172: bal_gas_valid unlinked; KEEP from_builder (live at Lbv_ret)
  balGasValidFromBuilderFunction ++ "\n" ++
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
  eip8037TxStateGasFunction ++ "\n" ++
  txIntrinsicStateGasFunction ++ "\n" ++
  eip7702AuthorizationExtractSignatureFunction ++ "\n" ++
  eip7702AuthorizationSigningHashFunction ++ "\n" ++
  eip7702AuthorizationRecoverAddressFunction ++ "\n" ++
  eip7702WarmRecoveredAuthoritiesFunction ++ "\n" ++
  eip7702AuthorityAsOfFunction ++ "\n" ++
  eip7702AuthStatePrepareFunction ++ "\n" ++
  blockVerdictTxStateGasInlinePrepareFunction ++ "\n" ++
  blockVerdictTxStateGasInlineFinalizeFunction ++ "\n" ++
  -- #11533 follow-up: eip7702_authority_state_materialize probe-only.
  blockVerdictEip8037TxStateGasNetArrayFunction ++ "\n" ++
  eip8037BlockGasUsedFunction ++ "\n" ++
  txGasResultIncrementsFunction ++ "\n" ++
  multiTxRunningSenderBalanceStepFunction ++ "\n" ++
  senderDebitFromGasFunction ++ "\n" ++
  txGasBalPostVerifyRuntimeFunction ++ "\n" ++
  senderPostNonceConsistentFunction ++ "\n" ++
  eip7778RemainingBlockGasCheckFunction ++ "\n" ++
  eip7778RemainingBlockGasFromResultsFunction ++ "\n" ++
  dispatcherCaptureExecStateGasFunction ++ "\n" ++
  dispatcherCaptureExecStateGasDifferentialFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  blockVerdictGasResultArenaPrepareFunction ++ "\n" ++
  b1SenderCountTableFunction ++ "\n" ++
  b1SenderTableFindFunction ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  enrgU32leFunction ++ "\n" ++
  statelessVerdictV2Function ++ "\n" ++
  -- #11163: one emitted selector/pricing kernel is shared by the root
  -- transaction adapter and all CALL-family precompile tails.  The helper is
  -- appended after the returning stateless entry, so it is a callable label
  -- and cannot alter the entry's fall-through control flow.
  precompileSharedSelectPriceFunction ++ "\n" ++
  -- #11163 item 2: one execution core shared by depth-0 and CALL-family wrappers.
  precompileSharedExecuteFunction ++ "\n" ++
  ".Lv2_pdone:"

end EvmAsm.Codegen
