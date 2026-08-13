/-
  EvmAsm.Codegen.Programs.BlobGasUsedAtBlockNumber

  Number-keyed `header.blob_gas_used` extractor (RLP field
  17, u64 BE -- EIP-4844 / Cancun). Composes K233 + the
  existing `header_extract_blob_gas_used` (from
  HeaderU64.lean).

  Complements gas_used / gas_limit primitives for EIP-4844
  fee-market verification.

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

/-! ## blob_gas_used_at_block_number

    Number-keyed extractor for
    `header.block.blob_gas_used` (RLP field 17, u64 BE --
    introduced in Cancun for EIP-4844).

    Pipeline (composes K233 scan + existing
    header_extract_blob_gas_used; no new helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_blob_gas_used -> u64

    Use cases:
      * EIP-4844 fee-market replay: paired with the
        existing excess_blob_gas helper, callers can
        independently derive the per-block blob base fee.
      * Blob-utilisation analysis: chain N calls with
        successive block_numbers to study network demand
        for blob throughput.
      * Audit pre vs post-Cancun headers: a non-zero
        blob_gas_used implies a Cancun-or-later block.

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 blob_gas_used out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (blob_gas_used written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header blob_gas_used extraction failed
            (RLP malformed / field 17 > 8 bytes /
            pre-Cancun header)
-/
def blobGasUsedAtBlockNumberFunction : String :=
  "blob_gas_used_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # blob_gas_used u64 out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lbgbn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lbgbn_loop:\n" ++
  "  beq s5, s4, .Lbgbn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lbgbn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lbgbn_have_end\n" ++
  ".Lbgbn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lbgbn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, bgbn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lbgbn_parse_fail\n" ++
  "  la t0, bgbn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lbgbn_hit\n" ++
  "  j .Lbgbn_step\n" ++
  ".Lbgbn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Lbgbn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lbgbn_loop\n" ++
  ".Lbgbn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_blob_gas_used\n" ++
  "  beqz a0, .Lbgbn_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lbgbn_ret\n" ++
  ".Lbgbn_finish:\n" ++
  "  bnez s8, .Lbgbn_parse_status\n" ++
  ".Lbgbn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbgbn_ret\n" ++
  ".Lbgbn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lbgbn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_blob_gas_used_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : blob_gas_used (u64; 0 on failure) -/
def ziskBlobGasUsedAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 blob_gas_used out\n" ++
  "  jal ra, blob_gas_used_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbgbn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractBlobGasUsedFunction ++ "\n" ++
  blobGasUsedAtBlockNumberFunction ++ "\n" ++
  ".Lbgbn_pdone:"

def ziskBlobGasUsedAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "bgbn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
