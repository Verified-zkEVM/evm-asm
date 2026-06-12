/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords

  Receipt-record materialization helpers carved out of BlockVerdict.lean to keep
  the main stateless verdict file below the file-size cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalGasValid
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
  "  la a0, brr_control; li a1, 16; la a2, brr_records\n" ++
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
  "brr_records:\n  .zero 1024"

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
  "  li t3, 128\n" ++
  "  bgtu t2, t3, .Lblws_overflow\n" ++
  "  la t1, evm_log_data_overflow; ld t1, 0(t1); bnez t1, .Lblws_overflow\n" ++
  "  add t2, s1, s0\n" ++
  "  sd t2, 0(t0)                # commit new block count\n" ++
  "  la t0, evm_event_logs\n" ++
  "  la t1, bv_block_log_descs\n" ++
  "  slli t2, s1, 8\n" ++
  "  add t1, t1, t2\n" ++
  "  slli t2, s0, 8              # n * 256 bytes (both regions 8-aligned)\n" ++
  ".Lblws_dcopy:\n" ++
  "  ld t3, 0(t0)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -8\n" ++
  "  bnez t2, .Lblws_dcopy\n" ++
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
  "  li t2, 65536\n" ++
  "  bgtu t1, t2, .Lblws_overflow\n" ++
  "  add t0, s1, s2\n" ++
  "  slli t0, t0, 4\n" ++
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
  ".Lbrlm_loop:\n" ++
  "  beq s3, s1, .Lbrlm_ok\n" ++
  "  slli t0, s3, 6\n" ++
  "  add s5, s2, t0              # record ptr\n" ++
  "  ld t1, 32(s5)               # log_count\n" ++
  "  beqz t1, .Lbrlm_next\n" ++
  "  ld t2, 24(s5)               # log_start\n" ++
  "  la a0, bv_block_log_descs\n" ++
  "  slli t3, t2, 8\n" ++
  "  add a0, a0, t3\n" ++
  "  mv a1, t1\n" ++
  "  la a2, bv_block_log_data\n" ++
  "  la a3, bv_block_log_meta\n" ++
  "  slli t3, t2, 4\n" ++
  "  add a3, a3, t3\n" ++
  "  la a4, bv_logs_rlp_arena\n" ++
  "  add a4, a4, s4\n" ++
  "  li a5, 65536\n" ++
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
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

end EvmAsm.Codegen
