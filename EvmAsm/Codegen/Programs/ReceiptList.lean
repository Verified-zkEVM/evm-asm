/-
  EvmAsm.Codegen.Programs.ReceiptList

  Receipt-record arena to RLP receipt-list encoder. This first slice supports
  legacy no-log receipt records; later slices will thread captured LOG
  descriptors, computed blooms, and typed receipt envelopes through the same ABI.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Receipt
import EvmAsm.Codegen.Programs.ReceiptRecords

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## receipt_records_encode_no_logs

    Encode the existing receipt-record arena as one RLP list of receipt values.
    This helper only accepts legacy records with `log_count = 0`; it uses a
    zero logs-bloom and an empty logs list (`0xc0`) for each receipt.

    Calling convention:
      a0 = receipt-record control block
      a1 = output buffer pointer
      a2 = output buffer capacity in bytes
      a3 = u64 out length pointer
      a0 output status:
        0 success
        1 malformed arena or record count above capacity
        2 nonzero log_count, not supported by this first slice
        3 output capacity or internal scratch overflow
        4 unsupported tx type (only legacy is supported by this first slice)
-/
def receiptRecordsEncodeNoLogsFunction : String :=
  "receipt_records_encode_no_logs:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # control\n" ++
  "  mv s1, a1                   # output ptr\n" ++
  "  mv s2, a2                   # output cap\n" ++
  "  mv s3, a3                   # out len ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  ld s4, 0(s0)                # count\n" ++
  "  ld t0, 8(s0)                # capacity\n" ++
  "  bgtu s4, t0, .Lrlen_malformed\n" ++
  "  ld s5, 16(s0)               # record base\n" ++
  "  beqz s5, .Lrlen_malformed\n" ++
  "  li s6, 0                    # index\n" ++
  "  li s7, 0                    # payload cursor\n" ++
  "  li s8, 32768                # payload scratch cap\n" ++
  ".Lrlen_loop:\n" ++
  "  beq s6, s4, .Lrlen_finish\n" ++
  "  slli t0, s6, 6\n" ++
  "  add s9, s5, t0              # record ptr\n" ++
  "  ld t0, 32(s9)               # log_count\n" ++
  "  bnez t0, .Lrlen_logs_unsupported\n" ++
  "  ld s10, 0(s9)               # tx type\n" ++
  "  bnez s10, .Lrlen_type_unsupported\n" ++
  "  ld t1, 8(s9)                # execution status\n" ++
  "  ld t2, 16(s9)               # cumulative gas\n" ++
  "  la s11, rle_payload_buf\n" ++
  "  add s11, s11, s7            # receipt output cursor\n" ++
  "  mv a0, t1\n" ++
  "  mv a1, t2\n" ++
  "  la a2, rle_zero_bloom\n" ++
  "  la a3, rle_empty_logs\n" ++
  "  li a4, 1\n" ++
  "  mv a5, s11\n" ++
  "  la a6, rle_field_len\n" ++
  "  jal ra, receipt_encode\n" ++
  "  j .Lrlen_after_encode\n" ++
  ".Lrlen_after_encode:\n" ++
  "  la t0, rle_field_len; ld t1, 0(t0)\n" ++
  "  add t2, s7, t1\n" ++
  "  bltu t2, s7, .Lrlen_overflow\n" ++
  "  bgtu t2, s8, .Lrlen_overflow\n" ++
  "  mv s7, t2\n" ++
  "  sd s11, 40(s9)              # encoded receipt ptr\n" ++
  "  sd t1, 48(s9)               # encoded receipt len\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lrlen_loop\n" ++
  ".Lrlen_finish:\n" ++
  "  li t0, 9\n" ++
  "  bltu s2, t0, .Lrlen_overflow\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s1\n" ++
  "  la a2, rle_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, rle_prefix_len; ld t1, 0(t0)\n" ++
  "  add t2, t1, s7\n" ++
  "  bltu t2, t1, .Lrlen_overflow\n" ++
  "  bgtu t2, s2, .Lrlen_overflow\n" ++
  "  sd t2, 0(s3)\n" ++
  "  add t3, s1, t1              # dst\n" ++
  "  la t4, rle_payload_buf      # src\n" ++
  "  mv t5, s7                   # remaining\n" ++
  ".Lrlen_copy:\n" ++
  "  beqz t5, .Lrlen_ok\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Lrlen_copy\n" ++
  ".Lrlen_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lrlen_ret\n" ++
  ".Lrlen_malformed:\n" ++
  "  li a0, 1\n" ++
  "  j .Lrlen_ret\n" ++
  ".Lrlen_logs_unsupported:\n" ++
  "  li a0, 2\n" ++
  "  j .Lrlen_ret\n" ++
  ".Lrlen_overflow:\n" ++
  "  li a0, 3\n" ++
  "  j .Lrlen_ret\n" ++
  ".Lrlen_type_unsupported:\n" ++
  "  li a0, 4\n" ++
  ".Lrlen_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_receipt_records_encode_no_logs`: focused probe.

    Input layout (file maps to INPUT+8 at 0x40000000):
      INPUT+8  record count
      INPUT+16 output capacity
      INPUT+24 records, four u64 fields each:
          tx_type, status, cumulative_gas, log_count

    Output layout:
      +0  status
      +8  encoded list length
      +16 encoded list bytes (truncated to ziskemu output cap)
-/
def ziskReceiptRecordsEncodeNoLogsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  li s1, 0xa0010000\n" ++
  "  li t0, 32\n" ++
  "  mv t1, s1\n" ++
  ".Lrlenp_zero_out:\n" ++
  "  beqz t0, .Lrlenp_zero_done\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lrlenp_zero_out\n" ++
  ".Lrlenp_zero_done:\n" ++
  "  ld s2, 8(s0)                # count\n" ++
  "  ld s3, 16(s0)               # output cap\n" ++
  "  la a0, rle_control\n" ++
  "  li a1, 16\n" ++
  "  la a2, rle_records\n" ++
  "  jal ra, receipt_records_init\n" ++
  "  ld s2, 8(s0)                # count (reload after helper call)\n" ++
  "  ld s3, 16(s0)               # output cap\n" ++
  "  li s4, 0                    # index\n" ++
  "  addi s5, s0, 24             # input record cursor\n" ++
  ".Lrlenp_append_loop:\n" ++
  "  beq s4, s2, .Lrlenp_encode\n" ++
  "  ld a1, 0(s5)                # tx type\n" ++
  "  ld a2, 8(s5)                # status\n" ++
  "  ld a3, 16(s5)               # cumulative gas\n" ++
  "  li a4, 0                    # log start\n" ++
  "  ld a5, 24(s5)               # log count\n" ++
  "  li a6, 0\n" ++
  "  li a7, 0\n" ++
  "  la a0, rle_control\n" ++
  "  jal ra, receipt_records_append\n" ++
  "  bnez a0, .Lrlenp_append_fail\n" ++
  "  addi s4, s4, 1\n" ++
  "  addi s5, s5, 32\n" ++
  "  j .Lrlenp_append_loop\n" ++
  ".Lrlenp_encode:\n" ++
  "  la a0, rle_control\n" ++
  "  li a1, 0xa0010010\n" ++
  "  ld a2, 16(s0)               # output cap\n" ++
  "  li a3, 0xa0010008\n" ++
  "  jal ra, receipt_records_encode_no_logs\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lrlenp_done\n" ++
  ".Lrlenp_append_fail:\n" ++
  "  li t0, 9\n" ++
  "  sd t0, 0(s1)\n" ++
  "  j .Lrlenp_done\n" ++
  rlpEncodeU64Function ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  receiptEncodeFunction ++ "\n" ++
  receiptRecordsFunction ++ "\n" ++
  receiptRecordsEncodeNoLogsFunction ++ "\n" ++
  ".Lrlenp_done:"

def ziskReceiptRecordsEncodeNoLogsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rle_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "rle_records:\n  .zero 1024\n" ++
  ".balign 8\n" ++
  "rle_field_len:\n  .zero 8\n" ++
  "rle_prefix_len:\n  .zero 8\n" ++
  "re_field_len:\n  .zero 8\n" ++
  "re_cursor:\n  .zero 8\n" ++
  "re_total_payload:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "rle_empty_logs:\n  .byte 0xc0\n" ++
  ".balign 8\n" ++
  "rle_zero_bloom:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "re_payload_buf:\n  .zero 16384\n" ++
  ".balign 8\n" ++
  "rle_payload_buf:\n  .zero 32768"

def ziskReceiptRecordsEncodeNoLogsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskReceiptRecordsEncodeNoLogsPrologue
  dataAsm     := ziskReceiptRecordsEncodeNoLogsDataSection
}

end EvmAsm.Codegen
