/-
  EvmAsm.Codegen.Programs.ChainWalkOneStepBack

  One-step backward chain walk. Given a current_block_hash
  and witness.headers, find the header whose keccak matches,
  extract its parent_hash, and check whether the parent is
  also present in witness.headers.

  Useful as a building block for caller-driven N-step trust
  extension: caller iterates this primitive N times, each
  call advancing one block backward through parent_hash
  links.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_walk_one_step_back_from_block_hash

    Pipeline:
      witness.headers ∋ ?h with keccak(h) == current_hash
                     -- via K19 witness_lookup_by_hash
      h -- header_extract_parent_hash -- 32 B parent_hash
      witness.headers ∋ ?h' with keccak(h') == parent_hash
                     -- second K19 -- sets parent_in_witness

    Returns the extracted parent_hash regardless of whether
    the parent header is present in witness.headers. The
    parent_in_witness flag distinguishes "valid trust hop"
    (parent walkable) from "boundary reached" (we know the
    parent hash but can't go further).

    Use cases:
      * N-step trust walk: caller iterates this primitive
        starting from an anchor block; each successful
        iteration where parent_in_witness == 1 extends
        trust one block.
      * Chain prefix audit: given trusted anchor, find the
        deepest reachable ancestor by walking until
        parent_in_witness == 0.
      * Fork detection: an inconsistent witness might have
        a chain where some headers can be walked but their
        parents can't be located in the same section.

    Distinct from #7222 / #7276:
      * #7222 takes two SEPARATE header RLPs.
      * #7276 takes a witness + index pair.
      * THIS takes a witness + current_block_hash, does the
        whole hash-to-hash walk in one call (no caller-
        supplied indices or RLPs).

    Calling convention (5 args):
      a0 (input)  : current_block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : 32-byte parent_hash out ptr
      a4 (input)  : u64 parent_in_witness out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (parent_hash written;
            parent_in_witness valid)
        1 = current_block_hash not in witness.headers
        2 = current header RLP parse failure
        3 = parent_hash field size unexpected (not 32 B)
-/
def chainWalkOneStepBackFromBlockHashFunction : String :=
  "chain_walk_one_step_back_from_block_hash:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # current_block_hash ptr\n" ++
  "  mv s1, a1                  # witness.headers ptr\n" ++
  "  mv s2, a2                  # witness.headers len\n" ++
  "  mv s3, a3                  # parent_hash out ptr (32 B)\n" ++
  "  mv s4, a4                  # parent_in_witness out\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # Step 1: find current's header.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s0\n" ++
  "  la a3, cwosb_match_offset\n" ++
  "  la a4, cwosb_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lcwosb_no_match\n" ++
  "  la t0, cwosb_match_offset\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add a0, s1, t1             # current header start\n" ++
  "  la t0, cwosb_match_length\n" ++
  "  ld a1, 0(t0)               # current header len\n" ++
  "  # Step 2: extract parent_hash into caller's buffer.\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  beqz a0, .Lcwosb_check_parent\n" ++
  "  # K202: 1 -> 2 (parse fail), 2 -> 3 (size mismatch).\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lcwosb_ret\n" ++
  ".Lcwosb_check_parent:\n" ++
  "  # Step 3: K19 over witness.headers with parent_hash.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s3                  # target = parent_hash\n" ++
  "  la a3, cwosb_parent_offset\n" ++
  "  la a4, cwosb_parent_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lcwosb_done\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)               # parent_in_witness = 1\n" ++
  ".Lcwosb_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lcwosb_ret\n" ++
  ".Lcwosb_no_match:\n" ++
  "  li a0, 1\n" ++
  ".Lcwosb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_walk_one_step_back_from_block_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : current_block_hash (32 bytes)
      bytes 48..   : witness.headers section bytes
    Output layout (48 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..40 : parent_hash (32 B; zero on early-out)
      bytes 40..48 : parent_in_witness (u64; 0 or 1) -/
def ziskChainWalkOneStepBackFromBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # current_block_hash ptr\n" ++
  "  addi a1, a6, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # parent_hash out (32 B)\n" ++
  "  li a4, 0xa0010028           # parent_in_witness out (u64)\n" ++
  "  jal ra, chain_walk_one_step_back_from_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcwosb_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  chainWalkOneStepBackFromBlockHashFunction ++ "\n" ++
  ".Lcwosb_pdone:"

def ziskChainWalkOneStepBackFromBlockHashDataSection : String :=
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
  "cwosb_match_offset:\n" ++
  "  .zero 8\n" ++
  "cwosb_match_length:\n" ++
  "  .zero 8\n" ++
  "cwosb_parent_offset:\n" ++
  "  .zero 8\n" ++
  "cwosb_parent_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
