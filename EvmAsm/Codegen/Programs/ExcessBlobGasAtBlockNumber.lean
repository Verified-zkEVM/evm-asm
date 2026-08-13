/-
  EvmAsm.Codegen.Programs.ExcessBlobGasAtBlockNumber

  Number-keyed `header.excess_blob_gas` extractor (RLP
  field 18, u64 BE -- EIP-4844). Composes K233 + the
  existing `header_extract_excess_blob_gas` (from
  HeaderU64.lean).

  Companion to blob_gas_used_at_block_number (PR 7611).
  Together they enable independent verification of the
  EIP-4844 blob base-fee formula:

    excess_blob_gas(N+1) =
      max(0, excess_blob_gas(N) + blob_gas_used(N) - target)
    blob_base_fee(N) =
      fake_exp(MIN_BLOB_BASE_FEE, excess_blob_gas(N),
               BLOB_BASE_FEE_UPDATE_FRACTION)

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

/-! ## excess_blob_gas_at_block_number

    Number-keyed extractor for
    `header.block.excess_blob_gas` (RLP field 18, u64 BE
    -- introduced in Cancun for EIP-4844).

    Pipeline (composes K233 scan + existing
    header_extract_excess_blob_gas; no new helpers):
      witness.headers ∋ ?h with h.block.number == target  [K233]
      h -> header_extract_excess_blob_gas -> u64

    Use cases:
      * Blob base-fee derivation cross-check: paired with
        blob_gas_used_at_block_number (PR 7611), callers
        derive blob_base_fee independently.
      * EIP-4844 fee-market analysis: chain N calls and
        plot excess_blob_gas trajectory.
      * Surge-detection: an excess_blob_gas rapidly
        approaching the cap implies sustained blob-heavy
        demand.

    Calling convention (4 args):
      a0 (input)  : target_block_number (u64, by value)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 excess_blob_gas out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (excess_blob_gas written)
        1 = no header with target block_number
        2 = K233 parse failure during scan
        3 = matched header excess_blob_gas extraction failed
            (RLP malformed / field 18 > 8 bytes /
            pre-Cancun header)
-/
def excessBlobGasAtBlockNumberFunction : String :=
  "excess_blob_gas_at_block_number:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # target_block_number\n" ++
  "  mv s1, a1                  # headers ptr\n" ++
  "  mv s2, a2                  # headers len\n" ++
  "  mv s3, a3                  # excess_blob_gas u64 out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s8, 0                   # saw_parse_fail\n" ++
  "  beqz s2, .Lebgn_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # N\n" ++
  "  li s5, 0                   # i\n" ++
  ".Lebgn_loop:\n" ++
  "  beq s5, s4, .Lebgn_finish\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s6, s1, t2             # header start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lebgn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4\n" ++
  "  j .Lebgn_have_end\n" ++
  ".Lebgn_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lebgn_have_end:\n" ++
  "  sub s7, t4, s6\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  la a2, ebgn_number_scratch\n" ++
  "  jal ra, header_extract_number\n" ++
  "  bnez a0, .Lebgn_parse_fail\n" ++
  "  la t0, ebgn_number_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beq t1, s0, .Lebgn_hit\n" ++
  "  j .Lebgn_step\n" ++
  ".Lebgn_parse_fail:\n" ++
  "  li s8, 1\n" ++
  ".Lebgn_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lebgn_loop\n" ++
  ".Lebgn_hit:\n" ++
  "  mv a0, s6\n" ++
  "  mv a1, s7\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_excess_blob_gas\n" ++
  "  beqz a0, .Lebgn_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 3\n" ++
  "  j .Lebgn_ret\n" ++
  ".Lebgn_finish:\n" ++
  "  bnez s8, .Lebgn_parse_status\n" ++
  ".Lebgn_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Lebgn_ret\n" ++
  ".Lebgn_parse_status:\n" ++
  "  li a0, 2\n" ++
  ".Lebgn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_excess_blob_gas_at_block_number`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : target_block_number (u64 LE)
      bytes 24..   : witness.headers
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : excess_blob_gas (u64; 0 on failure) -/
def ziskExcessBlobGasAtBlockNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  ld a0, 16(t4)               # target_block_number\n" ++
  "  addi a1, t4, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 excess_blob_gas out\n" ++
  "  jal ra, excess_blob_gas_at_block_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lebgn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  headerExtractExcessBlobGasFunction ++ "\n" ++
  excessBlobGasAtBlockNumberFunction ++ "\n" ++
  ".Lebgn_pdone:"

def ziskExcessBlobGasAtBlockNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ebgn_number_scratch:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
