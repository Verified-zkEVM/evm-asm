/-
  EvmAsm.Codegen.Programs.PostMergeInvariantsAtBlockHash

  Hash-keyed EIP-3675 post-merge invariant canary. Mirrors
  the Python `validate_header` checks added at the Merge:
    assert header.ommers_hash == EMPTY_OMMERS_HASH
    assert header.difficulty == 0
    assert header.nonce       == b'\x00' * 8
  but takes a 32-byte block_hash key instead of a raw
  header. One status byte, no scalar payload.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## post_merge_invariants_at_block_hash

    Hash-keyed EIP-3675 invariant canary. Composes K19 +
    existing K67 `header_validate_post_merge`; no new
    helpers.

    Why a composite over three singletons: the per-field
    hash-keyed mirrors (`ommers_hash_at_block_hash`,
    `difficulty_at_block_hash`, `header_nonce_at_block_hash`)
    each pay a full keccak over the matched header. The
    Merge spec needs all three checked together as a single
    `validate_header` predicate; this combined wrapper runs
    one keccak via K19 and then K67 reads the three RLP
    fields off the already-matched header buffer.

    Calling convention (3 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      ra (input)  : return

      a0 (output) :
        0 = all three invariants hold
        1 = block_hash not in witness.headers
        2 = ommers_hash mismatch (post-merge invariant 1)
        3 = difficulty != 0      (post-merge invariant 2)
        4 = nonce not 8 zero bytes (post-merge invariant 3)
        5 = matched header RLP parse failure
-/
def postMergeInvariantsAtBlockHashFunction : String :=
  "post_merge_invariants_at_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, pmibh_match_offset\n" ++
  "  la a4, pmibh_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lpmibh_no_match\n" ++
  "  la t0, pmibh_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s4, s1, t1\n" ++
  "  la t0, pmibh_match_length\n" ++
  "  ld s5, 0(t0)\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  jal ra, header_validate_post_merge\n" ++
  "  beqz a0, .Lpmibh_ret\n" ++
  "  # K67 status:\n" ++
  "  #   1 ommers_hash mismatch -> remap to 2\n" ++
  "  #   2 difficulty != 0      -> remap to 3\n" ++
  "  #   3 nonce != 8 zero bytes -> remap to 4\n" ++
  "  #   4 RLP parse failure    -> remap to 5\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lpmibh_ret\n" ++
  ".Lpmibh_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lpmibh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_post_merge_invariants_at_block_hash`: probe BuildUnit.
    Output layout (8 bytes):
      bytes 0..8 : status (0..5) -/
def ziskPostMergeInvariantsAtBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a2, 8(t4)                # witness_headers_len\n" ++
  "  addi a0, t4, 16             # block_hash ptr\n" ++
  "  addi a1, t4, 48             # witness.headers ptr\n" ++
  "  jal ra, post_merge_invariants_at_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lpmibh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  postMergeInvariantsAtBlockHashFunction ++ "\n" ++
  ".Lpmibh_pdone:"

def ziskPostMergeInvariantsAtBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n" ++
  "  .zero 8\n" ++
  "hvpm_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "pmibh_match_offset:\n" ++
  "  .zero 8\n" ++
  "pmibh_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
