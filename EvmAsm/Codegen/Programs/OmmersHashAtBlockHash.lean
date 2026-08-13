/-
  EvmAsm.Codegen.Programs.OmmersHashAtBlockHash

  Hash-keyed `header.ommers_hash` extractor (RLP field 1,
  32 bytes). Mirror of the number-keyed
  `ommers_hash_at_block_number` probe but takes a
  block_hash key.

  Per EIP-3675, post-merge headers MUST have
  `ommers_hash = EMPTY_LIST_KECCAK`; verifying this for a
  caller-supplied block_hash is a one-shot post-merge
  sanity check.

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

/-! ## ommers_hash_at_block_hash

    Hash-keyed extractor for `header.block.ommers_hash`
    (RLP field 1, 32 B).

    Pipeline (composes K19 + existing
    header_extract_ommers_hash; no new helpers):
      witness.headers ∋ ?h with keccak(h) == block_hash  [K19]
      h -> header_extract_ommers_hash -> 32 B

    Spec-defining check: per EIP-3675 (the Merge), every
    post-merge canonical header satisfies
    `ommers_hash = keccak(rlp([])) =
       1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347`.
    Reading the ommers_hash hash-keyed lets a bridge or
    light-client verify that invariant without first
    translating block_hash to a block_number.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte ommers_hash out ptr
      ra (input)  : return

      a0 (output) :
        0 = success
        1 = block_hash not in witness.headers
        2 = matched header ommers_hash extraction failed
            (RLP malformed / field 1 size != 32)
-/
def ommersHashAtBlockHashFunction : String :=
  "ommers_hash_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # ommers_hash out (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, ohbh_match_offset\n" ++
  "  la a4, ohbh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lohbh_no_match\n" ++
  "  la t0, ohbh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, ohbh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_ommers_hash\n" ++
  "  beqz a0, .Lohbh_ret\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li a0, 2\n" ++
  "  j .Lohbh_ret\n" ++
  ".Lohbh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lohbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_ommers_hash_at_block_hash`: probe BuildUnit. -/
def ziskOmmersHashAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # 32 B ommers_hash out\n" ++
  "  jal ra, ommers_hash_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lohbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractOmmersHashFunction ++ "\n" ++
  ommersHashAtBlockHashFunction ++ "\n" ++
  ".Lohbh_pdone:"

def ziskOmmersHashAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "heoh_offset:\n" ++
  "  .zero 8\n" ++
  "heoh_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ohbh_match_offset:\n" ++
  "  .zero 8\n" ++
  "ohbh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
