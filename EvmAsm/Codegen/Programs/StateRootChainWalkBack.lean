/-
  EvmAsm.Codegen.Programs.StateRootChainWalkBack

  Multi-step chain walk that also extracts the state_root
  of the deepest reachable block. Fused composition of
  #7355 (N-step walk) + K201 (state_root extract).

  Saves a host round-trip vs running #7355 then K201
  separately when the caller's goal is "what was the
  state_root N blocks back?"

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

/-! ## state_root_chain_walk_back_n_steps_from_block_hash

    Walk back up to N hops via parent_hash links from
    start_block_hash, then extract the state_root of the
    deepest reachable block.

    Output:
      * state_root_out  -- state_root field of the header
                           at the final reached block
                           (or zero if start missed)
      * valid_steps_out -- 0..N hops successfully traversed

    Use case: light-client historical query "give me the
    state_root from N blocks before this recent block."
    Caller can then feed that state_root into the
    inclusion-proof / extract family (#7193/#7197/#7233/...).

    Distinct from a #7355 + K201 chain:
      * Two-call: caller stores intermediate final_block_hash,
        passes it back, primitive re-locates via K19.
      * THIS: reuses the last K19 match offsets from the walk
        loop, avoiding a redundant K19.

    Calling convention (6 args):
      a0 (input)  : start_block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : N (u64; max hops)
      a4 (input)  : 32-byte state_root_out ptr
      a5 (input)  : u64 valid_steps_out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (state_root + valid_steps both valid)
        1 = start_block_hash not in witness.headers
        2 = parent_hash extraction failure during walk
        3 = final header state_root field extraction failure
-/
def stateRootChainWalkBackNStepsFromBlockHashFunction : String :=
  "state_root_chain_walk_back_n_steps_from_block_hash:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                  # start_block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # N\n" ++
  "  mv s4, a4                  # state_root_out (32 B)\n" ++
  "  mv s5, a5                  # valid_steps_out\n" ++
  "  sd zero, 0(s5)\n" ++
  "  sd zero,  0(s4); sd zero,  8(s4)\n" ++
  "  sd zero, 16(s4); sd zero, 24(s4)\n" ++
  "  # Copy start -> current scratch.\n" ++
  "  la s6, srcw_current_hash\n" ++
  "  ld t0,  0(s0); sd t0,  0(s6)\n" ++
  "  ld t0,  8(s0); sd t0,  8(s6)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s6)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s6)\n" ++
  "  # Initial K19 to confirm start is in witness.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s6\n" ++
  "  la a3, srcw_match_offset\n" ++
  "  la a4, srcw_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsrcw_start_miss\n" ++
  "  li s7, 0                   # hops_done\n" ++
  ".Lsrcw_loop:\n" ++
  "  beq s7, s3, .Lsrcw_extract\n" ++
  "  la t0, srcw_match_offset; ld t1, 0(t0)\n" ++
  "  add a0, s1, t1\n" ++
  "  la t0, srcw_match_length; ld a1, 0(t0)\n" ++
  "  la s8, srcw_parent_hash\n" ++
  "  mv a2, s8\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  beqz a0, .Lsrcw_lookup_parent\n" ++
  "  li a0, 2\n" ++
  "  j .Lsrcw_ret\n" ++
  ".Lsrcw_lookup_parent:\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s8\n" ++
  "  la a3, srcw_match_offset\n" ++
  "  la a4, srcw_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsrcw_extract   # parent not in witness -> boundary\n" ++
  "  # Advance current.\n" ++
  "  ld t0,  0(s8); sd t0,  0(s6)\n" ++
  "  ld t0,  8(s8); sd t0,  8(s6)\n" ++
  "  ld t0, 16(s8); sd t0, 16(s6)\n" ++
  "  ld t0, 24(s8); sd t0, 24(s6)\n" ++
  "  addi s7, s7, 1\n" ++
  "  ld t1, 0(s5); addi t1, t1, 1; sd t1, 0(s5)\n" ++
  "  j .Lsrcw_loop\n" ++
  ".Lsrcw_extract:\n" ++
  "  # match_offset/length point to the current (final) header.\n" ++
  "  la t0, srcw_match_offset; ld t1, 0(t0)\n" ++
  "  add a0, s1, t1\n" ++
  "  la t0, srcw_match_length; ld a1, 0(t0)\n" ++
  "  mv a2, s4                  # caller's state_root buffer\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lsrcw_done\n" ++
  "  li a0, 3\n" ++
  "  j .Lsrcw_ret\n" ++
  ".Lsrcw_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsrcw_ret\n" ++
  ".Lsrcw_start_miss:\n" ++
  "  li a0, 1\n" ++
  ".Lsrcw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_state_root_chain_walk_back_n_steps_from_block_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : N (u64 LE)
      bytes 24..56 : start_block_hash (32 bytes)
      bytes 56..   : witness.headers section bytes
    Output layout (48 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..40 : state_root (32 B)
      bytes 40..48 : valid_steps_count (u64) -/
def ziskStateRootChainWalkBackNStepsFromBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  ld a3, 16(a6)               # N\n" ++
  "  addi a0, a6, 24             # start_block_hash ptr\n" ++
  "  addi a1, a6, 56             # witness.headers ptr\n" ++
  "  li a4, 0xa0010008           # state_root out\n" ++
  "  li a5, 0xa0010028           # valid_steps_count out\n" ++
  "  jal ra, state_root_chain_walk_back_n_steps_from_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrcw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  stateRootChainWalkBackNStepsFromBlockHashFunction ++ "\n" ++
  ".Lsrcw_pdone:"

def ziskStateRootChainWalkBackNStepsFromBlockHashDataSection : String :=
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
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "srcw_match_offset:\n" ++
  "  .zero 8\n" ++
  "srcw_match_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "srcw_current_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "srcw_parent_hash:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
