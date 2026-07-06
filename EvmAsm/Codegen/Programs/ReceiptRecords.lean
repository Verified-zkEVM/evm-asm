/-
  EvmAsm.Codegen.Programs.ReceiptRecords

  Standalone receipt-record arena ABI used before wiring receipts into
  stateless_verdict_v2. This file intentionally only defines the record shape
  and a probe; transaction execution will populate the arena in later slices.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## receipt record arena

    Control block layout:
      +0  : count (u64)
      +8  : capacity (u64)
      +16 : record base pointer (u64)

    Record stride is 64 bytes:
      +0  : tx type (0 = legacy, 1..4 = typed envelope byte)
      +8  : execution status (1 = success, 0 = failure/revert)
      +16 : cumulative_gas_used
      +24 : captured LOG descriptor start index
      +32 : captured LOG descriptor count
      +40 : encoded receipt pointer, filled by the later receipt-list encoder
      +48 : encoded receipt length, filled by the later receipt-list encoder
      +56 : reserved for future flags

    The helper surface is deliberately small: init, append, append from a
    runtime execution result, and nth-copy. -/

def receiptRecordsFunction : String :=
  "receipt_records_init:\n" ++
  "  sd zero, 0(a0)              # count = 0\n" ++
  "  sd a1, 8(a0)                # capacity\n" ++
  "  sd a2, 16(a0)               # record base\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  "receipt_records_clear:\n" ++
  "  sd zero, 0(a0)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  "receipt_records_append:\n" ++
  "  ld t0, 0(a0)                # count\n" ++
  "  ld t1, 8(a0)                # capacity\n" ++
  "  bgeu t0, t1, .Lrrec_full\n" ++
  "  ld t2, 16(a0)               # record base\n" ++
  "  slli t3, t0, 6              # count * 64\n" ++
  "  add t2, t2, t3\n" ++
  "  sd a1, 0(t2)                # tx type\n" ++
  "  sd a2, 8(t2)                # execution status\n" ++
  "  sd a3, 16(t2)               # cumulative gas\n" ++
  "  sd a4, 24(t2)               # log start\n" ++
  "  sd a5, 32(t2)               # log count\n" ++
  "  sd a6, 40(t2)               # encoded receipt ptr\n" ++
  "  sd a7, 48(t2)               # encoded receipt len\n" ++
  "  sd zero, 56(t2)             # reserved\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 0(a0)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lrrec_full:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  "receipt_records_append_runtime_result:\n" ++
  "  beqz a2, .Lrrec_runtime_no_logs\n" ++
  "  bltu a5, a4, .Lrrec_runtime_no_logs\n" ++
  "  sub a5, a5, a4              # committed log count = final - checkpoint\n" ++
  "  j .Lrrec_runtime_call\n" ++
  ".Lrrec_runtime_no_logs:\n" ++
  "  li a5, 0                    # reverted/failing txs have no receipt logs\n" ++
  ".Lrrec_runtime_call:\n" ++
  "  li a6, 0                    # encoded receipt ptr (later encoder)\n" ++
  "  li a7, 0                    # encoded receipt len (later encoder)\n" ++
  "  j receipt_records_append\n" ++
  "receipt_record_nth:\n" ++
  "  ld t0, 0(a0)                # count\n" ++
  "  bgeu a1, t0, .Lrrnth_oob\n" ++
  "  ld t1, 16(a0)               # record base\n" ++
  "  slli t2, a1, 6\n" ++
  "  add t1, t1, t2\n" ++
  "  ld t3, 0(t1);  sd t3, 0(a2)\n" ++
  "  ld t3, 8(t1);  sd t3, 8(a2)\n" ++
  "  ld t3, 16(t1); sd t3, 16(a2)\n" ++
  "  ld t3, 24(t1); sd t3, 24(a2)\n" ++
  "  ld t3, 32(t1); sd t3, 32(a2)\n" ++
  "  ld t3, 40(t1); sd t3, 40(a2)\n" ++
  "  ld t3, 48(t1); sd t3, 48(a2)\n" ++
  "  ld t3, 56(t1); sd t3, 56(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lrrnth_oob:\n" ++
  "  li a0, 1\n" ++
  "  ret"

/-- `zisk_receipt_records_probe`: exercise the receipt-record arena.
    Input layout:
      bytes  0.. 8 : host length prefix, ignored by the guest
      bytes  8..16 : arena capacity
      bytes 16..24 : number of synthetic append attempts
      bytes 24..32 : runtime-result case:
        0 = none
        1 = successful tx with one committed LOG descriptor from 0..1
        2 = successful tx with one committed LOG descriptor from 2..3
        3 = reverted tx after two captured descriptors from 4..6

    Synthetic record `i` has:
      tx_type=0, status=1, cumulative_gas=21000+100*i,
      log_start=2*i, log_count=i, encoded_ptr=0x50000000+64*i,
      encoded_len=100+i.

    Output layout:
      bytes   0..  8 : status of the final append attempt, or 0 if none
      bytes   8.. 16 : final count
      bytes  16.. 24 : capacity
      bytes  24.. 32 : nth(0) status
      bytes  32.. 96 : first record copy, zero if absent
      bytes  96..104 : nth(count-1) status
      bytes 104..168 : last record copy, zero if absent -/
def ziskReceiptRecordsProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  li t0, 32\n" ++
  "  mv t1, s1\n" ++
  ".Lrrp_zero_out:\n" ++
  "  beqz t0, .Lrrp_zero_done\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lrrp_zero_out\n" ++
  ".Lrrp_zero_done:\n" ++
  "  ld s2, 8(s0)                # capacity\n" ++
  "  ld s3, 16(s0)               # append attempts\n" ++
  "  ld s7, 24(s0)               # runtime-result case\n" ++
  "  la a0, rr_control\n" ++
  "  mv a1, s2\n" ++
  "  la a2, rr_records\n" ++
  "  jal ra, receipt_records_init\n" ++
  "  li s4, 0                    # i\n" ++
  "  li s5, 0                    # last append status\n" ++
  ".Lrrp_append_loop:\n" ++
  "  beq s4, s3, .Lrrp_append_done\n" ++
  "  li a1, 0                    # legacy tx type\n" ++
  "  li a2, 1                    # success status\n" ++
  "  li t0, 100\n" ++
  "  mul a3, s4, t0\n" ++
  "  li t1, 21000\n" ++
  "  add a3, a3, t1\n" ++
  "  slli a4, s4, 1              # log start\n" ++
  "  mv a5, s4                   # log count\n" ++
  "  li t2, 0x50000000\n" ++
  "  slli t3, s4, 6\n" ++
  "  add a6, t2, t3\n" ++
  "  addi a7, s4, 100\n" ++
  "  la a0, rr_control\n" ++
  "  jal ra, receipt_records_append\n" ++
  "  mv s5, a0\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lrrp_append_loop\n" ++
  ".Lrrp_append_done:\n" ++
  "  beqz s7, .Lrrp_output\n" ++
  "  li t0, 1\n" ++
  "  beq s7, t0, .Lrrp_runtime_log0_success\n" ++
  "  li t0, 2\n" ++
  "  beq s7, t0, .Lrrp_runtime_log2_success\n" ++
  "  li t0, 3\n" ++
  "  beq s7, t0, .Lrrp_runtime_revert\n" ++
  "  j .Lrrp_output\n" ++
  ".Lrrp_runtime_log0_success:\n" ++
  "  li a1, 0; li a2, 1; li a3, 21111; li a4, 0; li a5, 1\n" ++
  "  j .Lrrp_runtime_append\n" ++
  ".Lrrp_runtime_log2_success:\n" ++
  "  li a1, 0; li a2, 1; li a3, 22222; li a4, 2; li a5, 3\n" ++
  "  j .Lrrp_runtime_append\n" ++
  ".Lrrp_runtime_revert:\n" ++
  "  li a1, 0; li a2, 0; li a3, 33333; li a4, 4; li a5, 6\n" ++
  ".Lrrp_runtime_append:\n" ++
  "  la a0, rr_control\n" ++
  "  jal ra, receipt_records_append_runtime_result\n" ++
  "  mv s5, a0\n" ++
  ".Lrrp_output:\n" ++
  "  sd s5, 0(s1)\n" ++
  "  la t0, rr_control\n" ++
  "  ld s6, 0(t0)                # count\n" ++
  "  ld t1, 8(t0)                # capacity\n" ++
  "  sd s6, 8(s1)\n" ++
  "  sd t1, 16(s1)\n" ++
  "  la a0, rr_control\n" ++
  "  li a1, 0\n" ++
  "  addi a2, s1, 32\n" ++
  "  jal ra, receipt_record_nth\n" ++
  "  sd a0, 24(s1)\n" ++
  "  beqz s6, .Lrrp_no_last\n" ++
  "  la a0, rr_control\n" ++
  "  addi a1, s6, -1\n" ++
  "  addi a2, s1, 104\n" ++
  "  jal ra, receipt_record_nth\n" ++
  "  sd a0, 96(s1)\n" ++
  "  j .Lrrp_done\n" ++
  ".Lrrp_no_last:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 96(s1)\n" ++
  ".Lrrp_done:\n" ++
  "  j .Lrrp_exit\n" ++
  receiptRecordsFunction ++ "\n" ++
  ".Lrrp_exit:"

def ziskReceiptRecordsProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rr_control:\n" ++
  "  .zero 24\n" ++
  ".balign 8\n" ++
  "rr_records:\n" ++
  "  .zero 1024"

def ziskReceiptRecordsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskReceiptRecordsProbePrologue
  dataAsm     := ziskReceiptRecordsProbeDataSection
}

end EvmAsm.Codegen
