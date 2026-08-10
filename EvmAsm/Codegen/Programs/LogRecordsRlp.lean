/-
  EvmAsm.Codegen.Programs.LogRecordsRlp

  `log_records_encode_rlp` (.63.1.6.2.1 logs leaf) — encode a window of the
  dispatcher's captured LOG descriptors as the spec's RLP logs list
  `rlp([log_0, ..])` with `log_i = rlp([address(20B), [topic..], data])`,
  matching execution-specs `Log` encoding (blocks.py). This is the missing
  primitive between the 8uld3.1a log capture (256-byte native descriptors +
  the evm_log_data full-data buffer) and the receipt encoder's `logs_rlp`
  input (`receipt_encode` field 3 / `logs_desc_ptr@8`): the per-tx bloom can
  then be derived from the same encoding via `logs_list_bloom_add`.

  Descriptor layout (EvmLogHandlers):
    +0    topic_count (u64, 0..4)
    +32   four 32-byte topic slots (stack-word / LE order)
    +192  executing ADDRESS context bytes (canonical 20-byte BE, low-aligned)
  Full data: evm_log_data_meta[i] = {byte offset (u64), data length (u64)}
  into evm_log_data.

  NOT wired into the verdict (that is the .2.1 integration follow-up) —
  soundness-neutral, like the nxio8 gas leaves.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Per-log scratch cap: address item (21) + topics list (≤ 2 + 4×33) + data
    item header (≤ 9). Data bytes are streamed straight into the payload
    buffer, so the cap bounds only the per-log header material. -/
def logRecordsRlpScratchCap : Nat := 256

/-! ## log_records_encode_rlp

    Calling convention:
      a0 = descriptor base ptr (256-byte stride; entry 0 of the WINDOW —
           callers pass `evm_event_logs + first*256`)
      a1 = log count in the window
      a2 = evm_log_data base ptr
      a3 = evm_log_data_meta base ptr (entry 0 of the WINDOW — callers pass
           `evm_log_data_meta + first*16`)
      a4 = output buffer ptr (receives `rlp([log..])`)
      a5 = output buffer capacity in bytes
      a6 = u64 out-length ptr
      a0 (output) status:
        0 success
        1 malformed descriptor (topic_count > 4)
        2 output capacity exceeded
    Zero logs encode as the empty list `0xc0`. -/
def logRecordsEncodeRlpFunction : String :=
  "log_records_encode_rlp:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # descriptor cursor\n" ++
  "  mv s1, a1                   # remaining logs\n" ++
  "  mv s2, a2                   # data base\n" ++
  "  mv s3, a3                   # meta cursor\n" ++
  "  mv s4, a4                   # out ptr\n" ++
  "  mv s5, a5                   # out cap\n" ++
  "  mv s6, a6                   # out len ptr\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li s7, 0                    # logs payload cursor (into lrr_payload)\n" ++
  ".Llrr_log_loop:\n" ++
  "  beqz s1, .Llrr_finish\n" ++
  -- ---- per-log inner payload: address item then topics list then data ----
  -- address: PACKED descriptor bytes +8..+27 are the canonical BE 20-byte address
  -- (copied verbatim from the source +192); topics below remain stack words (reversed).
  "  la t0, lrr_addr_be\n" ++
  "  addi t1, s0, 8\n" ++         -- canonical address bytes (packed header +8)
  "  li t2, 0\n" ++
  ".Llrr_addr_copy:\n" ++
  "  li t3, 20; beq t2, t3, .Llrr_addr_done\n" ++
  "  add t3, t1, t2\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  add t3, t0, t2\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Llrr_addr_copy\n" ++
  ".Llrr_addr_done:\n" ++
  "  la a0, lrr_addr_be; li a1, 20; la a2, lrr_inner; la a3, lrr_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, lrr_len; ld s8, 0(t0)        # s8 = inner cursor\n" ++
  -- topics: each 32-byte LE topic slot reversed to BE, encoded back to back
  -- into lrr_topics; then the topics LIST prefix + payload appended to inner.
  "  ld s9, 0(s0)                # topic_count\n" ++
  "  li t0, 4; bgtu s9, t0, .Llrr_malformed\n" ++
  "  li s10, 0                   # topic index\n" ++
  "  li s11, 0                   # topics payload cursor\n" ++
  ".Llrr_topic_loop:\n" ++
  "  beq s10, s9, .Llrr_topics_done\n" ++
  "  slli t0, s10, 5\n" ++
  "  addi t1, s0, 32\n" ++
  "  add t1, t1, t0              # topic slot (LE)\n" ++
  "  la t0, lrr_topic_be\n" ++
  "  li t2, 0\n" ++
  ".Llrr_topic_rev:\n" ++
  "  li t3, 32; beq t2, t3, .Llrr_topic_rev_done\n" ++
  "  li t3, 31; sub t3, t3, t2\n" ++
  "  add t3, t1, t3\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  add t3, t0, t2\n" ++
  "  sb t4, 0(t3)\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Llrr_topic_rev\n" ++
  ".Llrr_topic_rev_done:\n" ++
  "  la a0, lrr_topic_be; li a1, 32\n" ++
  "  la a2, lrr_topics; add a2, a2, s11\n" ++
  "  la a3, lrr_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, lrr_len; ld t1, 0(t0)\n" ++
  "  add s11, s11, t1\n" ++
  "  addi s10, s10, 1\n" ++
  "  j .Llrr_topic_loop\n" ++
  ".Llrr_topics_done:\n" ++
  "  mv a0, s11\n" ++
  "  la a1, lrr_inner; add a1, a1, s8\n" ++
  "  la a2, lrr_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, lrr_len; ld t1, 0(t0)\n" ++
  "  add s8, s8, t1\n" ++
  "  la t0, lrr_topics\n" ++
  "  la t1, lrr_inner; add t1, t1, s8\n" ++
  "  mv t2, s11\n" ++
  ".Llrr_topics_copy:\n" ++
  "  beqz t2, .Llrr_topics_copied\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Llrr_topics_copy\n" ++
  ".Llrr_topics_copied:\n" ++
  "  add s8, s8, s11\n" ++
  -- data: meta = {offset, len}; the item header goes into lrr_inner, the
  -- data BYTES are accounted into the log length but streamed later
  -- (header-then-stream keeps lrr_inner small for arbitrary data sizes).
  -- Compose: log payload = s8 (inner so far) + data_header + data_len.
  "  ld s10, 8(s3)               # data len\n" ++
  -- data item header into lrr_dhdr: single byte < 0x80 is the bare byte
  -- (header 0), else the string header.
  "  li t0, 1; bne s10, t0, .Llrr_data_hdr\n" ++
  "  ld t1, 0(s3)\n" ++
  "  add t1, s2, t1\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x80; bgeu t2, t3, .Llrr_data_hdr\n" ++
  "  li s11, 0                   # single low byte: no header\n" ++
  "  j .Llrr_data_hdr_done\n" ++
  ".Llrr_data_hdr:\n" ++
  -- reuse rlp_encode_bytes' header logic by encoding a ZERO-length copy is
  -- not possible; build the string header manually (mirrors rlp_encode_bytes):
  "  li t0, 56\n" ++
  "  bltu s10, t0, .Llrr_data_short\n" ++
  -- long form: 0xb7 + len-of-len, then BE length bytes
  "  la t1, lrr_dhdr\n" ++
  "  li t2, 0                    # len-of-len\n" ++
  "  mv t3, s10\n" ++
  ".Llrr_data_lol:\n" ++
  "  beqz t3, .Llrr_data_lol_done\n" ++
  "  srli t3, t3, 8\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Llrr_data_lol\n" ++
  ".Llrr_data_lol_done:\n" ++
  "  li t4, 0xb7\n" ++
  "  add t4, t4, t2\n" ++
  "  sb t4, 0(t1)\n" ++
  "  mv t3, t2\n" ++
  ".Llrr_data_lenbytes:\n" ++
  "  beqz t3, .Llrr_data_long_done\n" ++
  "  addi t3, t3, -1\n" ++
  "  slli t4, t3, 3\n" ++
  "  srl t4, s10, t4\n" ++
  "  andi t4, t4, 0xff\n" ++
  "  sub t5, t2, t3\n" ++
  "  add t5, t1, t5\n" ++
  "  sb t4, 0(t5)\n" ++
  "  j .Llrr_data_lenbytes\n" ++
  ".Llrr_data_long_done:\n" ++
  "  addi s11, t2, 1             # header bytes = 1 + len-of-len\n" ++
  "  j .Llrr_data_hdr_done\n" ++
  ".Llrr_data_short:\n" ++
  "  la t1, lrr_dhdr\n" ++
  "  li t4, 0x80\n" ++
  "  add t4, t4, s10\n" ++
  "  sb t4, 0(t1)\n" ++
  "  li s11, 1\n" ++
  ".Llrr_data_hdr_done:\n" ++
  -- log payload length = inner (s8) + data header (s11) + data (s10)
  "  add t0, s8, s11\n" ++
  "  add t0, t0, s10\n" ++
  -- log list prefix straight into the logs payload buffer
  "  mv a0, t0\n" ++
  "  la a1, lrr_payload; add a1, a1, s7\n" ++
  "  la a2, lrr_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, lrr_len; ld t1, 0(t0)\n" ++
  "  add s7, s7, t1\n" ++
  -- append inner (address + topics list)
  "  la t0, lrr_inner\n" ++
  "  la t1, lrr_payload; add t1, t1, s7\n" ++
  "  mv t2, s8\n" ++
  ".Llrr_inner_copy:\n" ++
  "  beqz t2, .Llrr_inner_copied\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Llrr_inner_copy\n" ++
  ".Llrr_inner_copied:\n" ++
  "  add s7, s7, s8\n" ++
  -- append data header + data bytes
  "  la t0, lrr_dhdr\n" ++
  "  la t1, lrr_payload; add t1, t1, s7\n" ++
  "  mv t2, s11\n" ++
  ".Llrr_dhdr_copy:\n" ++
  "  beqz t2, .Llrr_dhdr_copied\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Llrr_dhdr_copy\n" ++
  ".Llrr_dhdr_copied:\n" ++
  "  add s7, s7, s11\n" ++
  "  ld t0, 0(s3)                # data offset\n" ++
  "  add t0, s2, t0\n" ++
  "  la t1, lrr_payload; add t1, t1, s7\n" ++
  "  mv t2, s10\n" ++
  -- payload overflow guard (cap 131072)
  "  add t3, s7, t2\n" ++
  "  li t4, 2095652\n" ++
  "  bgtu t3, t4, .Llrr_overflow\n" ++
  ".Llrr_data_copy:\n" ++
  "  beqz t2, .Llrr_data_copied\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Llrr_data_copy\n" ++
  ".Llrr_data_copied:\n" ++
  "  add s7, s7, s10\n" ++
  -- vv4hr.3.4.2 PACK: advance by the variable record length (32 + 32*topic_count)
  -- and the 24 B meta stride. topic_count is reloaded from the current descriptor
  -- (s0 has not advanced yet).
  "  ld t0, 0(s0); slli t0, t0, 5; addi t0, t0, 32   # reclen = 32 + 32*topic_count\n" ++
  "  add s0, s0, t0             # advance packed descriptor\n" ++
  "  addi s3, s3, 24            # 24 B meta stride\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Llrr_log_loop\n" ++
  ".Llrr_finish:\n" ++
  -- outer list prefix + payload into the caller buffer
  "  li t0, 9\n" ++
  "  bgtu t0, s5, .Llrr_overflow\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s4\n" ++
  "  la a2, lrr_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, lrr_len; ld t1, 0(t0)\n" ++
  "  add t2, t1, s7\n" ++
  "  bgtu t2, s5, .Llrr_overflow\n" ++
  "  sd t2, 0(s6)\n" ++
  "  add t3, s4, t1\n" ++
  "  la t4, lrr_payload\n" ++
  "  mv t5, s7\n" ++
  ".Llrr_out_copy:\n" ++
  "  beqz t5, .Llrr_ok\n" ++
  "  lbu t6, 0(t4)\n" ++
  "  sb t6, 0(t3)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t5, t5, -1\n" ++
  "  j .Llrr_out_copy\n" ++
  ".Llrr_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Llrr_ret\n" ++
  ".Llrr_malformed:\n" ++
  "  li a0, 1\n" ++
  "  j .Llrr_ret\n" ++
  ".Llrr_overflow:\n" ++
  "  li a0, 2\n" ++
  ".Llrr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- Scratch labels for `log_records_encode_rlp`. The 128 KiB payload buffer
    matches `evm_log_data`'s half: headers are small, so a window whose data
    fits the capture buffer fits here for typical receipts; status 2 reports
    overflow rather than truncating. -/
def logRecordsRlpDataSection : String :=
  ".balign 8\n" ++
  "lrr_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "lrr_addr_be:\n  .zero 20\n" ++
  ".balign 8\n" ++
  "lrr_topic_be:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "lrr_dhdr:\n  .zero 9\n" ++
  ".balign 8\n" ++
  "lrr_topics:\n  .zero 136\n" ++
  ".balign 8\n" ++
  s!"lrr_inner:\n  .zero {logRecordsRlpScratchCap}\n" ++
  ".balign 8\n" ++
  "lrr_payload:\n  .zero 2095652\n"

/-- `zisk_log_records_encode_rlp`: focused probe.

    Input (after the ziskemu length wrapper at 0x40000000):
      +8    log count (u64)
      +16   count × 256-byte descriptors (native layout)
      then  count × 16-byte meta entries {offset, len} (offsets into the
            data blob that follows)
      then  the data blob.
    Output: +0 status, +8 encoded length, +16.. encoded bytes. -/
def ziskLogRecordsEncodeRlpPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # count\n" ++
  "  addi a0, s0, 16             # descriptors\n" ++
  "  mv a1, s1\n" ++
  "  slli t0, s1, 8\n" ++
  "  addi a3, s0, 16\n" ++
  "  add a3, a3, t0              # meta = after descriptors\n" ++
  "  slli t1, s1, 4\n" ++
  "  add a2, a3, t1              # data blob = after meta\n" ++
  "  li a4, 0xa0010010\n" ++
  "  li a5, 8192\n" ++
  "  li a6, 0xa0010008\n" ++
  "  jal ra, log_records_encode_rlp\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Llrrp_done\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  logRecordsEncodeRlpFunction ++ "\n" ++
  ".Llrrp_done:"

def ziskLogRecordsEncodeRlpProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskLogRecordsEncodeRlpPrologue
  dataAsm     := ".section .data\n" ++ logRecordsRlpDataSection
}

end EvmAsm.Codegen
