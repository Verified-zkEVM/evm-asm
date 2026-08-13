/-
  EvmAsm.Codegen.Programs.DifficultyAtBlockHash

  Hash-keyed `header.difficulty` extractor (RLP field 7,
  u64). Mirror of the number-keyed
  `difficulty_at_block_number` probe but takes a block_hash
  key.

  Per EIP-3675, post-merge canonical headers have
  `difficulty = 0`; pre-merge headers may have a full
  uint256 -- this thin wrapper only handles values that
  fit in u64.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## difficulty_at_block_hash

    Hash-keyed extractor for `header.block.difficulty`
    (RLP field 7, u64).

    Pipeline (composes K19 + existing
    header_extract_difficulty; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_difficulty -> u64

    Spec-defining check: per EIP-3675 (the Merge),
    every post-merge canonical header satisfies
    `difficulty == 0`. Reading difficulty hash-keyed lets a
    bridge / light-client verify that invariant
    without first translating block_hash to a block_number.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 difficulty out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (difficulty u64 written)
        1 = block_hash not in witness.headers
        2 = matched header difficulty extraction failed
            (RLP malformed / field 7 > 8 bytes BE)
-/
def difficultyAtBlockHashFunction : String :=
  "difficulty_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # difficulty u64 out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, dfbh_match_offset\n" ++
  "  la a4, dfbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Ldfbh_no_match\n" ++
  "  la t0, dfbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, dfbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_difficulty\n" ++
  "  beqz a0, .Ldfbh_ret\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Ldfbh_ret\n" ++
  ".Ldfbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Ldfbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_difficulty_at_block_hash`: probe BuildUnit.
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : difficulty u64 LE (0 on failure) -/
def ziskDifficultyAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # u64 difficulty out\n" ++
  "  jal ra, difficulty_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ldfbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractDifficultyFunction ++ "\n" ++
  difficultyAtBlockHashFunction ++ "\n" ++
  ".Ldfbh_pdone:"

def ziskDifficultyAtBlockHashDataSection : String :=
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
  "dfbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "dfbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
