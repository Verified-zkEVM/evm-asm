/-
  EvmAsm.Codegen.Programs.BlockNumberAtBlockHash

  Hash-keyed historical block number extractor. Given a
  block_hash and witness.headers, find the header and
  extract its block.number field (RLP item 8).

  Composes K19 witness_lookup_by_hash + K233
  header_extract_number.

  Useful for "what block height does this hash represent?"
  during chain walks.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderU64

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_number_at_block_hash

    Pipeline:
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -- header_extract_number -> u64 block.number     [K233]

    Use cases:
      * Chain walk audit: "what's the block height of the
        deepest reached anchor?" -- chain a #7355 walk +
        this primitive on the final hash.
      * Off-chain reconciliation: caller has a block_hash
        from a log / oracle and needs to know its position
        in the canonical chain.
      * Replay validation: many txes' validity depends on
        block.number (EIP activation, withdrawal queue
        index). Given a hash, get the number.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 block_number out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (block_number written)
        1 = block_hash not in witness.headers
        2 = K233 status code propagated (parse/decode fail)
-/
def blockNumberAtBlockHashFunction : String :=
  "block_number_at_block_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a3                  # u64 number out ptr\n" ++
  "  mv s3, a2                  # witness.headers len (preserved across K19)\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: K19 lookup.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s3\n" ++
  "  mv a2, s0\n" ++
  "  la a3, bnbh_match_offset\n" ++
  "  la a4, bnbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lbnbh_no_match\n" ++
  "  # Step 2: K233 number extract.\n" ++
  "  la t0, bnbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add a0, s1, t1             # header start\n" ++
  "  la t0, bnbh_match_length\n" ++
  "  ld a1, 0(t0)               # header len\n" ++
  "  mv a2, s2                  # u64 number out\n" ++
  "  jal ra, header_extract_number\n" ++
  "  beqz a0, .Lbnbh_done\n" ++
  "  li a0, 2                   # parse/decode fail\n" ++
  "  j .Lbnbh_ret\n" ++
  ".Lbnbh_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbnbh_ret\n" ++
  ".Lbnbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lbnbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_number_at_block_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : block_number (u64) -/
def ziskBlockNumberAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # block_hash ptr\n" ++
  "  addi a1, a6, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 block_number out\n" ++
  "  jal ra, block_number_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbnbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractNumberFunction ++ "\n" ++
  blockNumberAtBlockHashFunction ++ "\n" ++
  ".Lbnbh_pdone:"

def ziskBlockNumberAtBlockHashDataSection : String :=
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
  "bnbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "bnbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
