/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords

  Receipt-record materialization helpers carved out of BlockVerdict.lean to keep
  the main stateless verdict file below the file-size cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.ReceiptRecords
import EvmAsm.Codegen.Programs.LogRecordsRlp
import EvmAsm.Codegen.Programs.Bloom

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_receipt_records_materialize -- first receipt-record integration.
    a0 = execution payload ptr.
    a1 = pointer to `a2` u64 receipt gas increments from runtime results.
    a2 = receipt gas increment count.
    a3 = per-tx execution status array ptr (u64 per tx: 1 success / 0 failed),
         or 0 to record every tx as successful (.63.1.6.2.1 — the verdict
         passes the dispatcher_tx_gas_settle success bits via bv_tx_status_arr;
         probes that only exercise the gas chain pass 0).
    a4 = per-tx log window array ptr (16-byte stride {start u64, count u64}
         into the block log arena — bv_tx_log_window), or 0 for empty log
         windows (the pre-log behavior).

    This deliberately handles only a small materialization surface before full
    transaction execution exists: zero transactions leaves the arena empty, and
    transactions append records with the runtime-captured execution status and
    cumulative_gas_used equal to the running sum of the runtime-provided
    receipt gas increments. Other transaction shapes, or missing runtime gas
    increments, leave a debug status but do not affect the block verdict. -/
def blockReceiptRecordsMaterializeFunction : String :=
  "block_receipt_records_materialize:\n" ++
  "  addi sp, sp, -120\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # execution payload\n" ++
  "  la t0, brr_receipt_gas_ptr; sd a1, 0(t0)\n" ++
  "  la t0, brr_receipt_gas_count; sd a2, 0(t0)\n" ++
  "  la t0, brr_tx_status_ptr; sd a3, 0(t0)\n" ++
  "  la t0, brr_tx_window_ptr; sd a4, 0(t0)\n" ++
  "  la t0, brr_status; sd zero, 0(t0)\n" ++
  "  la t0, brr_append_status; sd zero, 0(t0)\n" ++
  "  la a0, brr_control; li a1, " ++ toString bvReceiptRecordCapacity ++ "; la a2, brr_records\n" ++
  "  jal ra, receipt_records_init\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le\n" ++
  "  mv s1, a0                   # transactions_offset\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le\n" ++
  "  mv s2, a0                   # withdrawals_offset\n" ++
  "  bleu s2, s1, .Lbrr_ok       # zero transactions\n" ++
  "  add s3, s0, s1              # tx list ptr\n" ++
  "  sub s4, s2, s1              # tx list len\n" ++
  "  li t0, 4; bltu s4, t0, .Lbrr_unsupported\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbrr_unsupported\n" ++
  "  srli s5, a0, 2              # tx_count\n" ++
  "  beqz s5, .Lbrr_ok\n" ++
  "  la t0, brr_receipt_gas_ptr; ld t1, 0(t0); beqz t1, .Lbrr_missing_gas_results\n" ++
  "  la t0, brr_receipt_gas_count; ld t1, 0(t0); bltu t1, s5, .Lbrr_missing_gas_results\n" ++
  "  bgtu a0, s4, .Lbrr_unsupported\n" ++
  "  mv s6, zero                 # tx index\n" ++
  "  mv s7, zero                 # cumulative gas\n" ++
  ".Lbrr_tx_loop:\n" ++
  "  beq s6, s5, .Lbrr_ok\n" ++
  "  slli t0, s6, 2\n" ++
  "  add a0, s3, t0\n" ++
  "  jal ra, bgv_u32le\n" ++
  "  mv s8, a0                   # current tx offset\n" ++
  "  bltu s8, s5, .Lbrr_unsupported\n" ++
  "  slli t0, s5, 2\n" ++
  "  bltu s8, t0, .Lbrr_unsupported\n" ++
  "  bgtu s8, s4, .Lbrr_unsupported\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s5, .Lbrr_last_tx\n" ++
  "  slli t1, t0, 2\n" ++
  "  add a0, s3, t1\n" ++
  "  jal ra, bgv_u32le\n" ++
  "  mv s9, a0                   # next tx offset\n" ++
  "  j .Lbrr_have_next\n" ++
  ".Lbrr_last_tx:\n" ++
  "  mv s9, s4                   # final tx ends at list end\n" ++
  ".Lbrr_have_next:\n" ++
  "  bltu s9, s8, .Lbrr_unsupported\n" ++
  "  bgtu s9, s4, .Lbrr_unsupported\n" ++
  "  add s10, s3, s8             # tx ptr\n" ++
  "  sub s11, s9, s8             # tx len\n" ++
  "  mv a0, s10; mv a1, s11; la a2, brr_tx_type; la a3, brr_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbrr_unsupported\n" ++
  -- bmvmx.1.3: typed txs (EIP-2718 type 1/2/3/4) are now supported, not just legacy
  -- (type 0). tx_type_dispatch already validated the type is in 0..4; the receipt
  -- record is a consistency pass (no receipts-root/header check) and cumulative gas
  -- is type-independent, so non-legacy txs no longer bail .Lbrr_unsupported.
  "  la t0, brr_receipt_gas_ptr; ld t1, 0(t0)\n" ++
  "  slli t2, s6, 3\n" ++
  "  add t1, t1, t2\n" ++
  "  ld t1, 0(t1)                # runtime receipt gas increment\n" ++
  "  add t2, s7, t1\n" ++
  "  bltu t2, s7, .Lbrr_unsupported\n" ++
  "  mv s7, t2\n" ++
  "  la a0, brr_control\n" ++
  "  la t0, brr_tx_type; ld a1, 0(t0)   # tx type (0 legacy / 1-4 typed)\n" ++
  -- .63.1.6.2.1: per-tx execution status from the runtime capture (1 when the
  -- dispatch halted via STOP/RETURN/SELFDESTRUCT, 0 on REVERT/exceptional —
  -- the spec's `error is None` receipt bit); a null array keeps the old
  -- all-success behavior for gas-only probes.
  "  la t0, brr_tx_status_ptr; ld t0, 0(t0)\n" ++
  "  li a2, 1\n" ++
  "  beqz t0, .Lbrr_status_ready\n" ++
  "  slli t1, s6, 3; add t0, t0, t1; ld a2, 0(t0)\n" ++
  ".Lbrr_status_ready:\n" ++
  "  mv a3, s7                   # cumulative gas\n" ++
  -- .63.1.6.2.1: thread this tx's block-arena log window (checkpoint = start,
  -- final = start + count); a null array keeps the empty-window behavior.
  "  la t0, brr_tx_window_ptr; ld t0, 0(t0)\n" ++
  "  li a4, 0\n" ++
  "  li a5, 0\n" ++
  "  beqz t0, .Lbrr_window_ready\n" ++
  "  slli t1, s6, 4; add t0, t0, t1\n" ++
  "  ld a4, 0(t0)                # window start (checkpoint)\n" ++
  "  ld t1, 8(t0)\n" ++
  "  add a5, a4, t1              # final = start + count\n" ++
  ".Lbrr_window_ready:\n" ++
  "  jal ra, receipt_records_append_runtime_result\n" ++
  "  la t0, brr_append_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbrr_append_fail\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lbrr_tx_loop\n" ++
  ".Lbrr_unsupported:\n" ++
  "  li t0, 1; la t1, brr_status; sd t0, 0(t1); j .Lbrr_ret\n" ++
  ".Lbrr_append_fail:\n" ++
  "  li t0, 2; la t1, brr_status; sd t0, 0(t1); j .Lbrr_ret\n" ++
  ".Lbrr_missing_gas_results:\n" ++
  "  li t0, 3; la t1, brr_status; sd t0, 0(t1); j .Lbrr_ret\n" ++
  ".Lbrr_ok:\n" ++
  "  li a0, 0; j .Lbrr_ret\n" ++
  ".Lbrr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 120\n" ++
  "  ret"

/-- `zisk_block_receipt_records_materialize`: focused probe for the first
    block-verdict receipt-record materialization slice. The input is a synthetic
    execution-payload byte array at INPUT_ADDR with only the fields this helper
    reads populated: gas_used, transactions_offset, withdrawals_offset, and the
    transactions SSZ list bytes. Output layout:
      +0  brr_status
      +8  receipt count
      +16 append status
      +24 first-record nth status
      +32 first 64-byte record copy, zero if absent
      +96 last-record nth status
      +104 last 64-byte record copy, zero if absent.

    Receipt gas increments for non-empty transaction lists are read from
    INPUT_ADDR + 8 + 0x1000:
      +0  count u64
      +8  count u64 receipt gas increments. -/
def ziskBlockReceiptRecordsMaterializePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 24\n" ++
  ".Lbrrp_zero_out:\n" ++
  "  beqz t1, .Lbrrp_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbrrp_zero_out\n" ++
  ".Lbrrp_zero_done:\n" ++
  "  li a0, 0x40000008\n" ++
  "  li a1, 0x40001010\n" ++
  "  li t0, 0x40001008\n" ++
  "  ld a2, 0(t0)\n" ++
  "  li a3, 0\n" ++
  "  li a4, 0\n" ++
  "  jal ra, block_receipt_records_materialize\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t1, brr_status; ld t2, 0(t1); sd t2, 0(s0)\n" ++
  "  la t1, brr_control; ld t2, 0(t1); sd t2, 8(s0)\n" ++
  "  la t1, brr_append_status; ld t2, 0(t1); sd t2, 16(s0)\n" ++
  "  la a0, brr_control; li a1, 0; addi a2, s0, 32\n" ++
  "  jal ra, receipt_record_nth\n" ++
  "  sd a0, 24(s0)\n" ++
  "  la t1, brr_control; ld t2, 0(t1); addi a1, t2, -1\n" ++
  "  la a0, brr_control; addi a2, s0, 104\n" ++
  "  jal ra, receipt_record_nth\n" ++
  "  sd a0, 96(s0)\n" ++
  "  j .Lbrrp_done\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  receiptRecordsFunction ++ "\n" ++
  blockReceiptRecordsMaterializeFunction ++ "\n" ++
  ".Lbrrp_done:"

def ziskBlockReceiptRecordsMaterializeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_tx_gas:\n  .zero 8\n" ++
  "brr_receipt_gas_ptr:\n  .zero 8\n" ++
  "brr_tx_status_ptr:\n  .zero 8\n" ++
  "brr_tx_window_ptr:\n  .zero 8\n" ++
  "brr_receipt_gas_count:\n  .zero 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero " ++ toString bvReceiptRecordsBytes

def ziskBlockReceiptRecordsMaterializeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockReceiptRecordsMaterializePrologue
  dataAsm     := ziskBlockReceiptRecordsMaterializeDataSection
}

/-! ## block_log_window_snapshot (.63.1.6.2.1 log windows)

    Snapshot the CURRENT dispatch's event-log window into the block-level log
    arena. Each `runtime_dispatcher_call` resets env+472 and overwrites
    `evm_event_logs` / `evm_log_data` from index 0, so the verdict must copy a
    tx's descriptors + data out before the next dispatch. Appends the
    descriptors to `bv_block_log_descs` (256 B stride), the data bytes to
    `bv_block_log_data` (offsets rebased into `bv_block_log_meta`), bumps
    `bv_block_log_count` / `bv_block_log_data_used`, and records this tx's
    window in `bv_last_log_start` / `bv_last_log_count` (the dispatch callers
    store those into the per-tx `bv_tx_log_window` slots).

    No arguments (env/global driven). a0 = 0 ok; 1 = arena overflow or the
    capture buffer overflowed (sets `bv_block_log_overflow` and zeroes the
    window so downstream consumers stay conservative). -/
def blockLogWindowSnapshotFunction : String :=
  "block_log_window_snapshot:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  la t0, evm_env\n" ++
  "  ld s0, 472(t0)              # n = this tx's event-log count\n" ++
  "  la t0, bv_block_log_count\n" ++
  "  ld s1, 0(t0)                # base = block log count\n" ++
  "  la t1, bv_last_log_start; sd s1, 0(t1)\n" ++
  "  la t1, bv_last_log_count; sd s0, 0(t1)\n" ++
  "  beqz s0, .Lblws_ok\n" ++
  "  add t2, s1, s0\n" ++
  "  li t3, " ++ toString bvBlockLogDescCapacity ++ "\n" ++
  "  bgtu t2, t3, .Lblws_overflow\n" ++
  "  la t1, evm_log_data_overflow; ld t1, 0(t1); bnez t1, .Lblws_overflow\n" ++
  "  add t2, s1, s0\n" ++
  "  sd t2, 0(t0)                # commit new block count\n" ++
  -- vv4hr.3.4.2 PACK: repack each source 256 B descriptor into a variable-length
  -- packed record (32 B header {topic_count@0, BE address 20 B @+8} + 32 B per
  -- ACTUAL topic). `bv_block_log_desc_used` is the running packed byte cursor that
  -- persists across per-tx dispatches; each log's packed offset is recorded in
  -- bv_block_log_meta[base+i].desc_off (+16) so the random-access reader can jump.
  "  la t0, bv_block_log_desc_used; ld s5, 0(t0)   # s5 = packed byte cursor\n" ++
  "  li s2, 0                    # i (local index)\n" ++
  ".Lblws_dpack:\n" ++
  "  beq s2, s0, .Lblws_dpack_done\n" ++
  "  la t0, evm_event_logs; slli t1, s2, 8; add t0, t0, t1   # t0 = src desc (i*256)\n" ++
  "  ld t1, 0(t0)                # t1 = topic_count\n" ++
  "  li t2, 4; bgtu t1, t2, .Lblws_overflow         # guard topic_count <= 4\n" ++
  "  slli t2, t1, 5; addi t2, t2, 32                # t2 = reclen = 32 + 32*tc\n" ++
  "  add t3, s5, t2\n" ++
  "  li t4, " ++ toString bvBlockLogDescBytes ++ "\n" ++
  "  bgtu t3, t4, .Lblws_overflow                   # packed byte cap\n" ++
  -- meta[(base+i)].desc_off = s5  (24 B stride: idx*24 = idx*16 + idx*8)
  "  add t4, s1, s2; slli t3, t4, 4; slli t5, t4, 3; add t3, t3, t5\n" ++
  "  la t4, bv_block_log_meta; add t3, t4, t3\n" ++
  "  sd s5, 16(t3)               # desc_off field\n" ++
  -- write the packed descriptor at bv_block_log_descs + s5
  "  la t3, bv_block_log_descs; add t3, t3, s5      # t3 = dest desc\n" ++
  "  sd t1, 0(t3)                # header: topic_count\n" ++
  "  addi t4, t0, 192; addi t5, t3, 8; li t6, 20    # copy 20 addr bytes src+192 -> dst+8\n" ++
  ".Lblws_acopy:\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; bnez t6, .Lblws_acopy\n" ++
  "  beqz t1, .Lblws_dpack_next                     # LOG0: no topics\n" ++
  "  slli a0, t1, 5                                 # topic bytes = 32*tc\n" ++
  "  addi t4, t0, 32; addi t5, t3, 32\n" ++
  ".Lblws_tcopy:\n" ++
  "  ld a1, 0(t4); sd a1, 0(t5); addi t4, t4, 8; addi t5, t5, 8; addi a0, a0, -8; bnez a0, .Lblws_tcopy\n" ++
  ".Lblws_dpack_next:\n" ++
  "  add s5, s5, t2              # desc_used += reclen\n" ++
  "  addi s2, s2, 1; j .Lblws_dpack\n" ++
  ".Lblws_dpack_done:\n" ++
  "  la t0, bv_block_log_desc_used; sd s5, 0(t0)    # persist packed cursor\n" ++
  "  li s2, 0                    # i\n" ++
  ".Lblws_meta_loop:\n" ++
  "  beq s2, s0, .Lblws_ok\n" ++
  "  la t0, evm_log_data_meta\n" ++
  "  slli t1, s2, 4\n" ++
  "  add t0, t0, t1\n" ++
  "  ld s3, 0(t0)                # src data offset\n" ++
  "  ld s4, 8(t0)                # data len\n" ++
  "  la t0, bv_block_log_data_used; ld s5, 0(t0)\n" ++
  "  add t1, s5, s4\n" ++
  "  li t2, " ++ toString bvBlockLogDataBytes ++ "\n" ++
  "  bgtu t1, t2, .Lblws_overflow\n" ++
  "  add t0, s1, s2\n" ++
  "  slli t1, t0, 3; slli t0, t0, 4; add t0, t0, t1   # (base+i)*24 (24 B meta)\n" ++
  "  la t1, bv_block_log_meta\n" ++
  "  add t1, t1, t0\n" ++
  "  sd s5, 0(t1)                # rebased offset\n" ++
  "  sd s4, 8(t1)\n" ++
  "  la t0, evm_log_data\n" ++
  "  add t0, t0, s3\n" ++
  "  la t1, bv_block_log_data\n" ++
  "  add t1, t1, s5\n" ++
  "  mv t2, s4\n" ++
  ".Lblws_bcopy:\n" ++
  "  beqz t2, .Lblws_bdone\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lblws_bcopy\n" ++
  ".Lblws_bdone:\n" ++
  "  add s5, s5, s4\n" ++
  "  la t0, bv_block_log_data_used; sd s5, 0(t0)\n" ++
  "  addi s2, s2, 1\n" ++
  "  j .Lblws_meta_loop\n" ++
  ".Lblws_overflow:\n" ++
  "  la t0, bv_block_log_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, bv_last_log_count; sd zero, 0(t0)\n" ++
  "  li a0, 1\n" ++
  "  j .Lblws_ret\n" ++
  ".Lblws_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lblws_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"


/-- `zisk_block_log_window_snapshot_overflow`: focused probe for the block-log
    stream-capacity checks inside `block_log_window_snapshot`. Input mode is a
    u64 at INPUT_ADDR + 8:
      1 = descriptor-capacity overflow (`bv_block_log_count` starts at cap)
      2 = data-capacity overflow (one captured log has data length cap+1)

    Output layout:
      +0  block_log_window_snapshot return status
      +8  bv_block_log_count
      +16 bv_block_log_data_used
      +24 bv_block_log_overflow
      +32 bv_last_log_start
      +40 bv_last_log_count. -/
def ziskBlockLogWindowSnapshotOverflowPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  li t0, 6\n" ++
  ".Lblwsp_zero_out:\n" ++
  "  beqz t0, .Lblwsp_zero_out_done\n" ++
  "  sd zero, 0(s0)\n" ++
  "  addi s0, s0, 8\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lblwsp_zero_out\n" ++
  ".Lblwsp_zero_out_done:\n" ++
  "  la t0, evm_env\n" ++
  "  li t1, 1; sd t1, 472(t0)\n" ++
  "  la t0, bv_block_log_count; sd zero, 0(t0)\n" ++
  "  la t0, bv_block_log_data_used; sd zero, 0(t0)\n" ++
  "  la t0, bv_block_log_overflow; sd zero, 0(t0)\n" ++
  "  la t0, bv_last_log_start; sd zero, 0(t0)\n" ++
  "  la t0, bv_last_log_count; sd zero, 0(t0)\n" ++
  "  la t0, evm_log_data_overflow; sd zero, 0(t0)\n" ++
  "  li t0, 0x40000008; ld t1, 0(t0)\n" ++
  "  li t2, 1; beq t1, t2, .Lblwsp_desc_overflow\n" ++
  "  li t2, 2; beq t1, t2, .Lblwsp_data_overflow\n" ++
  "  j .Lblwsp_call\n" ++
  ".Lblwsp_desc_overflow:\n" ++
  "  la t0, bv_block_log_count; li t2, " ++ toString bvBlockLogDescCapacity ++ "; sd t2, 0(t0)\n" ++
  "  j .Lblwsp_call\n" ++
  ".Lblwsp_data_overflow:\n" ++
  "  la t0, evm_log_data_meta; sd zero, 0(t0)\n" ++
  "  li t2, " ++ toString (bvBlockLogDataBytes + 1) ++ "; sd t2, 8(t0)\n" ++
  ".Lblwsp_call:\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  "  li s0, 0xa0010000\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, bv_block_log_count; ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  la t0, bv_block_log_data_used; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  la t0, bv_block_log_overflow; ld t1, 0(t0); sd t1, 24(s0)\n" ++
  "  la t0, bv_last_log_start; ld t1, 0(t0); sd t1, 32(s0)\n" ++
  "  la t0, bv_last_log_count; ld t1, 0(t0); sd t1, 40(s0)\n" ++
  "  j .Lblwsp_done\n" ++
  blockLogWindowSnapshotFunction ++ "\n" ++
  ".Lblwsp_done:"

def ziskBlockLogWindowSnapshotOverflowDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_env:\n  .zero 480\n" ++
  "evm_log_data_overflow:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n  .zero 256\n" ++
  "evm_log_data_meta:\n  .zero 16\n" ++
  "evm_log_data:\n  .zero 1\n" ++
  ".balign 8\n" ++
  "bv_block_log_count:\n  .zero 8\n" ++
  "bv_block_log_data_used:\n  .zero 8\n" ++
  "bv_block_log_desc_used:\n  .zero 8\n" ++
  "bv_block_log_overflow:\n  .zero 8\n" ++
  "bv_last_log_start:\n  .zero 8\n" ++
  "bv_last_log_count:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bv_block_log_descs:\n  .zero 256\n" ++
  "bv_block_log_meta:\n  .zero 24\n" ++
  "bv_block_log_data:\n  .zero 1"

def ziskBlockLogWindowSnapshotOverflowProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockLogWindowSnapshotOverflowPrologue
  dataAsm     := ziskBlockLogWindowSnapshotOverflowDataSection
}

/-! ## block_receipt_logs_materialize (.63.1.6.2.1 logs into records)

    Post-pass over the receipt-record arena: for each record with a non-empty
    log window, encode the window from the block log arena as the spec RLP
    logs list (`log_records_encode_rlp` into `bv_logs_rlp_arena`), derive the
    record's logs bloom (`logs_list_bloom_add` over the encoding), fill the
    per-record `{bloom_ptr, logs_rlp_ptr, logs_rlp_len}` descriptor
    (`bv_record_logs_desc`), and point record@56 at it — exactly the shape
    `receipt_records_encode_no_logs` consumes for with-log receipts.

    INERT until the receipts consensus enforcement consumes the encoded
    records (gated on the EIP-7708 transfer-log emission gap, see the
    receipts-blocker bead): nothing reads the filled descriptors yet.

    a0 = receipt-record control block.
    a0 (output): 0 ok; 1 log window malformed/encode failed; 2 bloom failed;
    3 block log arena overflowed (conservative). -/
def blockReceiptLogsMaterializeFunction : String :=
  "block_receipt_logs_materialize:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # control\n" ++
  "  la t0, bv_block_log_overflow; ld t0, 0(t0); bnez t0, .Lbrlm_overflow\n" ++
  "  ld s1, 0(s0)                # record count\n" ++
  "  ld s2, 16(s0)               # record base\n" ++
  "  li s3, 0                    # i\n" ++
  "  li s4, 0                    # rlp arena cursor\n" ++
  "  la t0, bv_logs_rlp_arena_used; sd zero, 0(t0)\n" ++
  ".Lbrlm_loop:\n" ++
  "  beq s3, s1, .Lbrlm_ok\n" ++
  "  slli t0, s3, 6\n" ++
  "  add s5, s2, t0              # record ptr\n" ++
  "  ld t1, 32(s5)               # log_count\n" ++
  "  beqz t1, .Lbrlm_next\n" ++
  "  ld t2, 24(s5)               # log_start (index)\n" ++
  -- vv4hr.3.4.2 PACK: descriptors are variable length, so jump to the window's
  -- first log via the packed byte-offset recorded in meta[log_start].desc_off.
  "  la a3, bv_block_log_meta\n" ++
  "  slli t3, t2, 4; slli t4, t2, 3; add t3, t3, t4   # log_start*24\n" ++
  "  add a3, a3, t3              # a3 = &meta[log_start] (24 B stride)\n" ++
  "  la a0, bv_block_log_descs\n" ++
  "  ld t3, 16(a3); add a0, a0, t3   # a0 = packed desc base (meta.desc_off)\n" ++
  "  mv a1, t1\n" ++
  "  la a2, bv_block_log_data\n" ++
  "  la a4, bv_logs_rlp_arena\n" ++
  "  add a4, a4, s4\n" ++
  "  li a5, " ++ toString bvLogsRlpArenaBytes ++ "\n" ++
  "  sub a5, a5, s4\n" ++
  "  la a6, bv_logs_rlp_len\n" ++
  "  jal ra, log_records_encode_rlp\n" ++
  "  bnez a0, .Lbrlm_encode_fail\n" ++
  "  la t0, bv_logs_rlp_len; ld s6, 0(t0)   # encoded length\n" ++
  "  # zero this record's bloom, then accumulate from the encoding\n" ++
  "  la t0, bv_record_blooms\n" ++
  "  slli t1, s3, 8\n" ++
  "  add t0, t0, t1\n" ++
  "  li t1, 32\n" ++
  ".Lbrlm_bloom_zero:\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lbrlm_bloom_zero\n" ++
  "  la a0, bv_record_blooms\n" ++
  "  slli t1, s3, 8\n" ++
  "  add a0, a0, t1\n" ++
  "  la a1, bv_logs_rlp_arena\n" ++
  "  add a1, a1, s4\n" ++
  "  mv a2, s6\n" ++
  "  jal ra, logs_list_bloom_add\n" ++
  "  bnez a0, .Lbrlm_bloom_fail\n" ++
  "  # fill the logs descriptor {bloom_ptr, rlp_ptr, len} and record@56\n" ++
  "  la t0, bv_record_logs_desc\n" ++
  "  slli t1, s3, 5              # 32-byte stride (24 used, 8 pad)\n" ++
  "  add t0, t0, t1\n" ++
  "  la t2, bv_record_blooms\n" ++
  "  slli t3, s3, 8\n" ++
  "  add t2, t2, t3\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t2, bv_logs_rlp_arena\n" ++
  "  add t2, t2, s4\n" ++
  "  sd t2, 8(t0)\n" ++
  "  sd s6, 16(t0)\n" ++
  "  sd t0, 56(s5)\n" ++
  "  add s4, s4, s6\n" ++
  ".Lbrlm_next:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lbrlm_loop\n" ++
  ".Lbrlm_encode_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbrlm_ret\n" ++
  ".Lbrlm_bloom_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbrlm_ret\n" ++
  ".Lbrlm_overflow:\n" ++
  "  li a0, 3\n" ++
  "  j .Lbrlm_ret\n" ++
  ".Lbrlm_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lbrlm_ret:\n" ++
  "  la t0, bv_logs_rlp_arena_used; sd s4, 0(t0)\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_receipt_logs_materialize_overflow`: focused probe for a
    nonzero block_receipt_logs_materialize status. It forces the existing
    block-log overflow flag before calling the helper, so the output must be
    status 3 with the overflow flag still set. Output layout:
      +0  block_receipt_logs_materialize return status
      +8  bv_receipt_logs_status mirror
      +16 bv_block_log_overflow. -/
def ziskBlockReceiptLogsMaterializeOverflowPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  sd zero, 0(s0); sd zero, 8(s0); sd zero, 16(s0)\n" ++
  "  la t0, brr_control; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0)\n" ++
  "  la t0, bv_receipt_logs_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_block_log_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  "  la a0, brr_control\n" ++
  "  jal ra, block_receipt_logs_materialize\n" ++
  "  sd a0, 0(s0)\n" ++
  "  la t0, bv_receipt_logs_status; sd a0, 0(t0); ld t1, 0(t0); sd t1, 8(s0)\n" ++
  "  la t0, bv_block_log_overflow; ld t1, 0(t0); sd t1, 16(s0)\n" ++
  "  j .Lbrlmp_done\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  logRecordsEncodeRlpFunction ++ "\n" ++
  bloomAddValueFunction ++ "\n" ++
  logBloomAddFunction ++ "\n" ++
  logsListBloomAddFunction ++ "\n" ++
  blockReceiptLogsMaterializeFunction ++ "\n" ++
  ".Lbrlmp_done:"

def ziskBlockReceiptLogsMaterializeOverflowDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  "bv_block_log_overflow:\n  .zero 8\n" ++
  "bv_receipt_logs_status:\n  .zero 8\n" ++
  "bv_block_log_descs:\n  .zero 256\n" ++
  "bv_block_log_meta:\n  .zero 24\n" ++
  "bv_block_log_data:\n  .zero 1\n" ++
  "bv_record_blooms:\n  .zero 256\n" ++
  "bv_record_logs_desc:\n  .zero 24\n" ++
  "bv_logs_rlp_arena:\n  .zero 1\n" ++
  "bv_logs_rlp_len:\n  .zero 8\n" ++
  logRecordsRlpDataSection ++
  ziskLogsListBloomAddDataSection

def ziskBlockReceiptLogsMaterializeOverflowProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockReceiptLogsMaterializeOverflowPrologue
  dataAsm     := ziskBlockReceiptLogsMaterializeOverflowDataSection
}

end EvmAsm.Codegen
