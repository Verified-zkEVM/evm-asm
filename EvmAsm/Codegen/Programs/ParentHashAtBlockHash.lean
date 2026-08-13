/-
  EvmAsm.Codegen.Programs.ParentHashAtBlockHash

  Hash-keyed `header.parent_hash` extractor. Mirror of
  parent_hash_at_block_number (PR 7621) but takes a
  block_hash key.

  Useful for direct chain-walk-back-by-one operations
  without the K233 number scan overhead.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## parent_hash_at_block_hash

    Hash-keyed extractor for `header.block.parent_hash`
    (RLP field 0, 32 bytes).

    Pipeline (composes K19 + the existing
    header_extract_parent_hash; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_parent_hash -> 32 B

    Use cases:
      * Direct one-step chain walk back: given a block_hash
        for block N, return the block_hash of block (N-1).
      * Reorg discrimination: given two block_hashes claimed
        to be at the same height, recurse via parent_hash to
        find the divergence point.
      * Backward-walk audit: verify that two consecutive
        block_hashes in a witness are actually
        parent-linked.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte parent_hash out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (parent_hash written)
        1 = block_hash not in witness.headers
        2 = matched header parent_hash extraction failed
            (RLP malformed / field 0 size != 32)
-/
def parentHashAtBlockHashFunction : String :=
  "parent_hash_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # parent_hash out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, phbh_match_offset\n" ++
  "  la a4, phbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lphbh_no_match\n" ++
  "  la t0, phbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, phbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  beqz a0, .Lphbh_ret\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lphbh_ret\n" ++
  ".Lphbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lphbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_parent_hash_at_block_hash`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers
    Output layout (40 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..40 : parent_hash (32 B; 0 on failure) -/
def ziskParentHashAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 32 B parent_hash out\n" ++
  "  jal ra, parent_hash_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lphbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  parentHashAtBlockHashFunction ++ "\n" ++
  ".Lphbh_pdone:"

def ziskParentHashAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "phbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "phbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
