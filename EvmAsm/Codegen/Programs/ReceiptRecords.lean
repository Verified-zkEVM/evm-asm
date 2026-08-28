/-
  EvmAsm.Codegen.Programs.ReceiptRecords

  Standalone receipt-record arena ABI used before wiring receipts into
  stateless_verdict_v2. This file intentionally only defines the record shape
  and a probe; transaction execution will populate the arena in later slices.
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Codegen.Layout
public import EvmAsm.Codegen.Emit
public meta import EvmAsm.Codegen.Emit
public import EvmAsm.Codegen.Programs.ReceiptRecordsProgs
public meta import EvmAsm.Codegen.Programs.ReceiptRecordsProgs

@[expose] public section

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

-- Drift guards (build-time evaluation): the exact renderings of the two
-- verified DCode programs.  The assemble+cmp byte-identity check against
-- the previous hand-written text was run against THESE strings; if the
-- emitter or a program changes, the pins fail and the check must be rerun.
#guard emitProgram receiptRecordsInitProg ==
  "  sd x0, 0(x10)\n  sd x11, 8(x10)\n  sd x12, 16(x10)\n"
    ++ "  li x10, 0\n  jalr x0, 0(x1)"
#guard emitProgram receiptRecordsClearProg ==
  "  sd x0, 0(x10)\n  li x10, 0\n  jalr x0, 0(x1)"
#guard emitProgram receiptRecordsAppendProg ==
  "  ld x5, 0(x10)\n  ld x6, 8(x10)\n  bgeu x5, x6, .+64\n"
    ++ "  ld x7, 16(x10)\n  slli x28, x5, 6\n  add x7, x7, x28\n"
    ++ "  sd x11, 0(x7)\n  sd x12, 8(x7)\n  sd x13, 16(x7)\n"
    ++ "  sd x14, 24(x7)\n  sd x15, 32(x7)\n  sd x16, 40(x7)\n"
    ++ "  sd x17, 48(x7)\n  sd x0, 56(x7)\n  addi x5, x5, 1\n"
    ++ "  sd x5, 0(x10)\n  li x10, 0\n  jalr x0, 0(x1)\n"
    ++ "  li x10, 1\n  jalr x0, 0(x1)"
#guard emitProgram receiptRecordsAppendRuntimeProg ==
  "  beq x12, x0, .+16\n  bltu x15, x14, .+12\n  sub x15, x15, x14\n"
    ++ "  jal x0, .+8\n  li x15, 0\n  li x16, 0\n  li x17, 0\n"
    ++ "  jal x0, .-108"
#guard emitProgram receiptRecordNthProg ==
  "  ld x5, 0(x10)\n  bgeu x11, x5, .+88\n  ld x6, 16(x10)\n"
    ++ "  slli x7, x11, 6\n  add x6, x6, x7\n"
    ++ "  ld x28, 0(x6)\n  sd x28, 0(x12)\n"
    ++ "  ld x28, 8(x6)\n  sd x28, 8(x12)\n"
    ++ "  ld x28, 16(x6)\n  sd x28, 16(x12)\n"
    ++ "  ld x28, 24(x6)\n  sd x28, 24(x12)\n"
    ++ "  ld x28, 32(x6)\n  sd x28, 32(x12)\n"
    ++ "  ld x28, 40(x6)\n  sd x28, 40(x12)\n"
    ++ "  ld x28, 48(x6)\n  sd x28, 48(x12)\n"
    ++ "  ld x28, 56(x6)\n  sd x28, 56(x12)\n"
    ++ "  li x10, 0\n  jalr x0, 0(x1)\n  li x10, 1\n  jalr x0, 0(x1)"

def receiptRecordsFunction : String :=
  -- `receipt_records_init` and `receipt_records_clear` are emitted from
  -- the verified DCode programs (`ReceiptRecordsSAsm.rriDeriv` /
  -- `rrcDeriv`, specs `receiptRecordsInit_retSpec` /
  -- `receiptRecordsClear_retSpec`, bundle-level
  -- `receiptRecords{Init,Clear}_bundleSpec`); byte-identity with the
  -- previous hand-written text checked by assemble+cmp, the renderings
  -- pinned above.  The remaining three entries stay hand-written until
  -- the dual-writable-region story lands (#12991).
  "receipt_records_init:\n" ++
  emitProgram receiptRecordsInitProg ++ "\n" ++
  "receipt_records_clear:\n" ++
  emitProgram receiptRecordsClearProg ++ "\n" ++
  -- All five entries are emitted from the shared instruction lists (the
  -- full bundle image `receiptRecordsBundleProg`); byte-identity with the
  -- previous label-form text checked by assemble+cmp (244 bytes), the
  -- renderings pinned above.  The cross-entry `j receipt_records_append`
  -- is the numeric `jal x0, .-108` (bundle index 35 → 8).
  "receipt_records_append:\n" ++
  emitProgram receiptRecordsAppendProg ++ "\n" ++
  "receipt_records_append_runtime_result:\n" ++
  emitProgram receiptRecordsAppendRuntimeProg ++ "\n" ++
  "receipt_record_nth:\n" ++
  emitProgram receiptRecordNthProg

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


end EvmAsm.Codegen
