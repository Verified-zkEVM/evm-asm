/-
  EvmAsm.Codegen.Programs.ReceiptList

  Receipt-record arena to RLP receipt-list encoder. This first slice supports
  legacy no-log receipt records; later slices will thread captured LOG
  descriptors, computed blooms, and typed receipt envelopes through the same ABI.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.Receipt
import EvmAsm.Codegen.Programs.ReceiptRecords

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## receipt_records_encode_no_logs (.63.1.6.2.2 -- now full: logs + typed)

    Encode the receipt-record arena as one RLP list of receipt values, writing
    each record's individual wire-format encoding to encoded_ptr@40 / encoded_len@48
    (the descriptors block_validate_receipts_root_indexed builds the receipts trie
    over). Each receipt is `[status, cumulative_gas, logs_bloom(256B), logs]`, with
    EIP-2718 typed receipts prefixed by the type byte (`type_byte || rlp(inner)`).

    Record layout (64B): tx_type@0 / status@8 / cumulative_gas@16 / log_start@24 /
    log_count@32 / encoded_ptr@40 (out) / encoded_len@48 (out) / logs_desc_ptr@56.
      - log_count == 0: zero logs-bloom + empty logs list (0xc0).
      - log_count >  0: read logs_desc_ptr@56 -> {bloom_ptr@0 (256B), logs_rlp_ptr@8,
        logs_rlp_len@16}, filled by the .2.1 materializer (logs_bloom + materialize_log_records).
      - tx_type in 1..4: prepend the EIP-2718 type byte (legacy = 0 = bare rlp).

    Calling convention:
      a0 = receipt-record control block
      a1 = output buffer pointer
      a2 = output buffer capacity in bytes
      a3 = u64 out length pointer
      a0 output status:
        0 success
        1 malformed arena
        2 log_count > 0 but the record carries no logs descriptor (@56 == 0)
        3 output capacity or internal scratch overflow
        4 unsupported tx type (> 4)
        5 record count above capacity
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
  "  bgtu s4, t0, .Lrlen_count_over_capacity\n" ++
  "  ld s5, 16(s0)               # record base\n" ++
  "  beqz s5, .Lrlen_malformed\n" ++
  "  li s6, 0                    # index\n" ++
  "  li s7, 0                    # payload cursor\n" ++
  "  li s8, " ++ toString bvReceiptListPayloadBytes ++ "                # payload scratch cap\n" ++
  ".Lrlen_loop:\n" ++
  "  beq s6, s4, .Lrlen_finish\n" ++
  "  slli t0, s6, 6\n" ++
  "  add s9, s5, t0              # record ptr (64B: tx_type@0/status@8/gas@16/log_start@24/\n" ++
  "                              #  log_count@32/enc_ptr@40/enc_len@48/logs_desc_ptr@56)\n" ++
  "  ld s10, 0(s9)              # tx type (0 legacy / 1..4 EIP-2718 typed)\n" ++
  "  li t0, 4; bgtu s10, t0, .Lrlen_type_unsupported\n" ++
  "  ld t1, 8(s9)              # execution status\n" ++
  "  ld t2, 16(s9)             # cumulative gas\n" ++
  "  la s11, rle_payload_buf; add s11, s11, s7   # receipt start (incl. any type byte)\n" ++
  -- .63.1.6.2.2: typed receipts are `type_byte || rlp(inner)` (EIP-2718).
  "  mv a5, s11                # rlp(inner) output cursor (default = start)\n" ++
  "  beqz s10, .Lrlen_no_typebyte\n" ++
  "  sb s10, 0(s11); addi a5, s11, 1   # write type byte; rlp(inner) starts at +1\n" ++
  ".Lrlen_no_typebyte:\n" ++
  -- with-log records carry logs_desc_ptr @56 -> {bloom_ptr@0, logs_rlp_ptr@8, logs_rlp_len@16}
  -- (filled by the .2.1 materializer: bloom=logs_bloom(tx logs), logs_rlp=materialize_log_records).
  -- no-log records use the zero bloom + empty logs list (0xc0).
  "  ld t0, 32(s9)             # log_count\n" ++
  "  beqz t0, .Lrlen_nolog_in\n" ++
  "  ld t3, 56(s9)             # logs_desc_ptr\n" ++
  "  beqz t3, .Lrlen_logs_unsupported   # log_count>0 but materializer left no descriptor\n" ++
  "  ld a2, 0(t3); ld a3, 8(t3); ld a4, 16(t3)   # bloom_ptr, logs_rlp_ptr, logs_rlp_len\n" ++
  "  j .Lrlen_do_enc\n" ++
  ".Lrlen_nolog_in:\n" ++
  "  la a2, rle_zero_bloom; la a3, rle_empty_logs; li a4, 1\n" ++
  ".Lrlen_do_enc:\n" ++
  "  mv a0, t1; mv a1, t2; la a6, rle_field_len\n" ++
  "  jal ra, receipt_encode\n" ++
  -- receipt_encode clobbers t/a regs; s7/s9/s10/s11 (callee-saved) survive.
  "  la t0, rle_field_len; ld t1, 0(t0)   # rlp(inner) len\n" ++
  "  li t4, 0; beqz s10, .Lrlen_pfx0; li t4, 1\n" ++
  ".Lrlen_pfx0:\n" ++
  "  add t1, t1, t4            # encoded_len = (typed ? 1 : 0) + rlp len\n" ++
  "  add t2, s7, t1\n" ++
  "  bltu t2, s7, .Lrlen_overflow\n" ++
  "  bgtu t2, s8, .Lrlen_overflow\n" ++
  "  mv s7, t2\n" ++
  "  sd s11, 40(s9)            # encoded receipt ptr (start, incl. type byte)\n" ++
  "  sd t1, 48(s9)             # encoded receipt len (type_byte? + rlp)\n" ++
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
  "  j .Lrlen_ret\n" ++
  ".Lrlen_count_over_capacity:\n" ++
  "  li a0, 5\n" ++
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
      INPUT+24 control capacity
      INPUT+32 mode flags: bit0 force null record base, bit1 bypass append
      INPUT+40 records, four u64 fields each:
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
  "  ld s6, 24(s0)               # control capacity\n" ++
  "  ld s7, 32(s0)               # mode flags\n" ++
  "  la a0, rle_control\n" ++
  "  mv a1, s6\n" ++
  "  la a2, rle_records\n" ++
  "  jal ra, receipt_records_init\n" ++
  "  bnez s7, .Lrlenp_direct_control\n" ++
  "  ld s2, 8(s0)                # count (reload after helper call)\n" ++
  "  ld s3, 16(s0)               # output cap\n" ++
  "  li s4, 0                    # index\n" ++
  "  addi s5, s0, 40             # input record cursor\n" ++
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
  ".Lrlenp_direct_control:\n" ++
  "  la t0, rle_control\n" ++
  "  ld t1, 8(s0); sd t1, 0(t0)  # direct count\n" ++
  "  ld t1, 24(s0); sd t1, 8(t0) # direct capacity\n" ++
  "  andi t2, s7, 1; bnez t2, .Lrlenp_direct_null_base\n" ++
  "  la t1, rle_records; sd t1, 16(t0)\n" ++
  "  j .Lrlenp_encode\n" ++
  ".Lrlenp_direct_null_base:\n" ++
  "  sd zero, 16(t0)\n" ++
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
  "rle_records:\n  .zero " ++ toString bvReceiptRecordsBytes ++ "\n" ++
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
  "re_payload_buf:\n  .zero " ++ toString bvReceiptEncodePayloadBytes ++ "\n" ++
  ".balign 8\n" ++
  "rle_payload_buf:\n  .zero " ++ toString bvReceiptListPayloadBytes

def ziskReceiptRecordsEncodeNoLogsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskReceiptRecordsEncodeNoLogsPrologue
  dataAsm     := ziskReceiptRecordsEncodeNoLogsDataSection
}

end EvmAsm.Codegen
