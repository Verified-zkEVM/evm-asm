/-
  EvmAsm.Codegen.Programs.ChainWalkNStepsBack

  Multi-step backward chain walk. Given anchor block_hash
  and step count N, iterates one-step backward walks until
  either N hops complete or a parent isn't found in
  witness.headers.

  Single-call counterpart of #7348 used in a loop.
  Useful for "extend trust N blocks from anchor".

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

/-! ## chain_walk_n_steps_back_from_block_hash

    Iterate one-step backward walks from start_block_hash
    for up to N hops. Each hop:
      1. Locate the current header in witness.headers via K19.
      2. Extract its parent_hash via K202.
      3. Verify parent_hash is also in witness.headers via K19.
      4. Advance: current_hash := parent_hash, valid_steps++.
    Stops early if any step fails (parent not in witness,
    or RLP parse failure on the current header).

    Returns:
      * final_block_hash -- the last reached block_hash
        (== start_block_hash if 0 valid steps; == ancestor
        N-blocks-back if N valid steps).
      * valid_steps_count -- 0..N.

    Distinct from #7348 (single step) and #7289 (iterates
    indices, not hashes):
      * #7348: one hash-keyed hop, caller drives the loop.
      * #7289: validates ALL consecutive index pairs across
        the whole section.
      * THIS: drives N hops by hash-chasing, returning the
        deepest reachable ancestor.

    Use cases:
      * Extend trust N blocks back from an anchor.
      * Find the deepest reachable ancestor in a chain that
        spans more blocks than the witness provides.

    Calling convention (6 args):
      a0 (input)  : start_block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : N (u64; max hops)
      a4 (input)  : 32-byte final_block_hash out ptr
      a5 (input)  : u64 valid_steps_count out ptr
      ra (input)  : return

      a0 (output) :
        0 = walk completed (could be N steps or fewer)
        1 = start_block_hash not in witness.headers
        2 = RLP parse failure on some intermediate header
            (valid_steps_count records how many steps
             completed before the failure)
-/
def chainWalkNStepsBackFromBlockHashFunction : String :=
  "chain_walk_n_steps_back_from_block_hash:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # start_block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # N (max hops)\n" ++
  "  mv s4, a4                  # final_block_hash out (32 B)\n" ++
  "  mv s5, a5                  # valid_steps_count out\n" ++
  "  sd zero, 0(s5)             # pre-zero count\n" ++
  "  # Copy start into current scratch (current = start).\n" ++
  "  la s6, cwnsb_current_hash\n" ++
  "  ld t0,  0(s0); sd t0,  0(s6)\n" ++
  "  ld t0,  8(s0); sd t0,  8(s6)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s6)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s6)\n" ++
  "  # Verify start is in witness via K19 (need this for status 1).\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s6\n" ++
  "  la a3, cwnsb_match_offset\n" ++
  "  la a4, cwnsb_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lcwnsb_start_miss\n" ++
  "  li s7, 0                   # s7 = hops_done\n" ++
  ".Lcwnsb_loop:\n" ++
  "  beq s7, s3, .Lcwnsb_done\n" ++
  "  # Use match_offset / match_length (set by previous K19).\n" ++
  "  la t0, cwnsb_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add a0, s1, t1             # header start\n" ++
  "  la t0, cwnsb_match_length\n" ++
  "  ld a1, 0(t0)               # header len\n" ++
  "  la s8, cwnsb_parent_hash\n" ++
  "  mv a2, s8\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  beqz a0, .Lcwnsb_check_parent\n" ++
  "  # K202 fail -> status 2, stop.\n" ++
  "  li a0, 2\n" ++
  "  j .Lcwnsb_finalize\n" ++
  ".Lcwnsb_check_parent:\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s8                  # target = parent_hash\n" ++
  "  la a3, cwnsb_match_offset\n" ++
  "  la a4, cwnsb_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lcwnsb_done      # parent not in witness, stop\n" ++
  "  # parent located -> advance.\n" ++
  "  ld t0,  0(s8); sd t0,  0(s6)\n" ++
  "  ld t0,  8(s8); sd t0,  8(s6)\n" ++
  "  ld t0, 16(s8); sd t0, 16(s6)\n" ++
  "  ld t0, 24(s8); sd t0, 24(s6)\n" ++
  "  addi s7, s7, 1\n" ++
  "  ld t1, 0(s5); addi t1, t1, 1; sd t1, 0(s5)\n" ++
  "  j .Lcwnsb_loop\n" ++
  ".Lcwnsb_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcwnsb_finalize:\n" ++
  "  # Write current to final_block_hash out.\n" ++
  "  ld t0,  0(s6); sd t0,  0(s4)\n" ++
  "  ld t0,  8(s6); sd t0,  8(s4)\n" ++
  "  ld t0, 16(s6); sd t0, 16(s4)\n" ++
  "  ld t0, 24(s6); sd t0, 24(s4)\n" ++
  "  j .Lcwnsb_ret\n" ++
  ".Lcwnsb_start_miss:\n" ++
  "  # final_block_hash zeroed, count zero.\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4)\n" ++
  "  sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  li a0, 1\n" ++
  ".Lcwnsb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_chain_walk_n_steps_back_from_block_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : N (u64 LE; max hops)
      bytes 24..56 : start_block_hash (32 bytes)
      bytes 56..   : witness.headers section bytes
    Output layout (48 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..40 : final_block_hash (32 B)
      bytes 40..48 : valid_steps_count (u64) -/
def ziskChainWalkNStepsBackFromBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  ld a3, 16(a6)               # N\n" ++
  "  addi a0, a6, 24             # start_block_hash ptr\n" ++
  "  addi a1, a6, 56             # witness.headers ptr\n" ++
  "  li a4, 0xa0010008           # final_block_hash out\n" ++
  "  li a5, 0xa0010028           # valid_steps_count out\n" ++
  "  jal ra, chain_walk_n_steps_back_from_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcwnsb_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  chainWalkNStepsBackFromBlockHashFunction ++ "\n" ++
  ".Lcwnsb_pdone:"

def ziskChainWalkNStepsBackFromBlockHashDataSection : String :=
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
  "cwnsb_match_offset:\n" ++
  "  .zero 8\n" ++
  "cwnsb_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "cwnsb_current_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "cwnsb_parent_hash:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
