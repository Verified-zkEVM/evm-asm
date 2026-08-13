/-
  EvmAsm.Codegen.Programs.GasLimitAtBlockHash

  Hash-keyed `header.gas_limit` extractor. Mirror of
  `gas_limit_at_block_number` (PR 7551) but takes a
  block_hash key.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.BlockHashPredicates

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## gas_limit_at_block_hash

    Hash-keyed extractor for `header.block.gas_limit`
    (RLP field 9, u64 BE).

    Pipeline (composes K19 + existing
    header_extract_gas_limit; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_gas_limit -> u64

    Use cases:
      * Bridge-driven capacity check: caller has a known
        block_hash and wants to know the block's gas_limit
        cap.
      * Cross-witness consistency: compare gas_limit at
        a shared block_hash.
      * EIP-1559 cross-check: pair with
        `gas_used_at_block_hash` to derive base-fee.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 gas_limit out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (gas_limit written)
        1 = block_hash not in witness.headers
        2 = matched header gas_limit extraction failed
            (RLP malformed / field 9 > 8 bytes)
-/
def gasLimitAtBlockHashFunction : String :=
  "gas_limit_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # u64 gas_limit out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, glbh_match_offset\n" ++
  "  la a4, glbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lglbh_no_match\n" ++
  "  la t0, glbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, glbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_gas_limit\n" ++
  "  beqz a0, .Lglbh_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lglbh_ret\n" ++
  ".Lglbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lglbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_gas_limit_at_block_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : gas_limit (u64; 0 on failure) -/
def ziskGasLimitAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 gas_limit out\n" ++
  "  jal ra, gas_limit_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lglbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractGasLimitFunction ++ "\n" ++
  gasLimitAtBlockHashFunction ++ "\n" ++
  ".Lglbh_pdone:"

def ziskGasLimitAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "glbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "glbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
