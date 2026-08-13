/-
  EvmAsm.Codegen.Programs.ExtraDataAtBlockNumber

  Number-keyed `header.extra_data` extractor (RLP field 12,
  variable-length up to 32 bytes). Composes K233 + the
  existing `header_extract_extra_data` (from HeaderU64.lean).

  First variable-length per-block-field primitive: emits
  the bytes and a separate length, since the on-chain
  field is sub-32 but not fixed-32.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## extra_data_at_block_number

    Number-keyed extractor for
    `header.block.extra_data` (RLP field 12, variable-length
    up to 32 bytes per the consensus rules).

    Pipeline (composes K233 scan + existing
    header_extract_extra_data; no new helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_extra_data -> (length, bytes)

    Use cases:
      * Client-attribution audit: extra_data is the
        canonical signature slot for execution clients
        (e.g. "Geth/v1.13...", "Nethermind/v1...");
        callers can identify which client built which
        block.
      * Merge-day audit: pre-merge blocks often carried
        miner-extension data; post-merge clients
        canonicalised it.
      * Trade-style attribution: MEV searchers sometimes
        encode tracking strings here.

    Calling convention (5 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : output bytes ptr (max 32 bytes written)
      a4 (input)  : u64 output length ptr
      ra (input)  : return

      a0 (output) :
        0 = success (bytes + length written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header extra_data extraction failed
            (RLP malformed)
        4 = extra_data > 32 bytes (consensus violation)
-/
def extraDataAtBlockNumberFunction : String :=
  "extra_data_at_block_number:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # extra_data bytes out\n" ++
  "  mv s9, a4                  # extra_data len out\n" ++
  "  sd zero, 0(s9)\n" ++
  "  # Pre-zero output bytes (32 B = 4 x u64).\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Ledbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Ledbn_loop:\n" ++
  "  beq s5, s4, .Ledbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Ledbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Ledbn_have_end\n" ++
  ".Ledbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Ledbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, edbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Ledbn_parse_fail\n" ++
  "  la t0, edbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Ledbn_hit\n" ++
  "  j .Ledbn_step\n" ++
  ".Ledbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Ledbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Ledbn_loop\n" ++
  ".Ledbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  mv a3, s9\n" ++
  "  jal ra, header_extract_extra_data\n" ++
  "  beqz a0, .Ledbn_ret\n" ++
  "  sd zero, 0(s9)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Ledbn_helper_parse\n" ++
  "  li a0, 4                   # >32 B\n" ++
  "  j .Ledbn_ret\n" ++
  ".Ledbn_helper_parse:\n" ++
  "  li a0, 3\n" ++
  "  j .Ledbn_ret\n" ++
  ".Ledbn_finish:\n" ++
  "  bnez s8, .Ledbn_parse_status\n" ++
  ".Ledbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Ledbn_ret\n" ++
  ".Ledbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Ledbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_extra_data_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (48 bytes):
      bytes  0.. 8 : status (0..4)
      bytes  8..16 : extra_data length (u64; 0 on failure)
      bytes 16..48 : extra_data bytes (padded with zeros) -/
def ziskExtraDataAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010010           # bytes out (after status+length)\n" ++
  "  li a4, 0xa0010008           # u64 length out\n" ++
  "  jal ra, extra_data_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ledbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractExtraDataFunction ++ "\n" ++
  extraDataAtBlockNumberFunction ++ "\n" ++
  ".Ledbn_pdone:"

def ziskExtraDataAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "heed_offset:\n" ++
  "  .zero 8\n" ++
  "heed_length:\n" ++
  "  .zero 8\n" ++
  "edbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
