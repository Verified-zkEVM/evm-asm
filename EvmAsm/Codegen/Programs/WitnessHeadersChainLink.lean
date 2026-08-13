/-
  EvmAsm.Codegen.Programs.WitnessHeadersChainLink

  In-witness chain-link verifier: given the witness.headers
  SSZ list section and a parent_idx, verify that
  keccak(witness.headers[parent_idx]) ==
    witness.headers[parent_idx + 1].parent_hash.

  Distinct from #7222 (`parent_keccak_matches_child_parent_hash`):
    * #7222 takes two SEPARATE header RLPs across host
      boundary.
    * THIS takes a single witness.headers section and an
      index pair (parent_idx, parent_idx+1), iterating
      within the same section -- no host round-trip per
      pair, useful for batch chain-link validation.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_chain_link_at_index

    Given (witness.headers section, parent_idx), verify
    keccak(headers[parent_idx]) ==
      headers[parent_idx + 1].parent_hash.

    Composes SSZ inner-offset traversal (twice -- once for
    parent slice, once for child slice) + K3 zkvm_keccak256
    + K202 header_extract_parent_hash + 32-byte compare.

    Use cases:
      * Validate full witness.headers chain consistency by
        iterating parent_idx = 0..N-2 and counting valid
        links.
      * Verify a specific hop in the chain without paying
        for the full chain validator.
      * Detect tampering: any single-byte modification of
        headers[parent_idx]'s bytes flips this from valid
        to invalid.

    Calling convention (4 args):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : parent_idx (u64)
      a3 (input)  : u64 is_valid out ptr
      ra (input)  : return

      a0 (output) :
        0 = success (is_valid set; 0 or 1)
        1 = parent_idx out of bounds
        2 = parent_idx + 1 out of bounds (only one header
            available -- no chain link to verify)
        3 = child header at parent_idx+1 RLP parse failure
        4 = child parent_hash field size unexpected
-/
def witnessHeadersChainLinkAtIndexFunction : String :=
  "witness_headers_chain_link_at_index:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # parent_idx\n" ++
  "  mv s3, a3                  # is_valid out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  beqz s1, .Lwhcl_oob_p\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  bgeu s2, s4, .Lwhcl_oob_p\n" ++
  "  addi t6, s2, 1\n" ++
  "  bgeu t6, s4, .Lwhcl_oob_c\n" ++
  "  # Compute parent element bounds (i = s2).\n" ++
  "  slli t0, s2, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s5, s0, t2             # parent start\n" ++
  "  slli t3, t6, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # parent end = child start\n" ++
  "  sub s6, t4, s5             # parent len\n" ++
  "  mv s7, t4                  # child start (saved)\n" ++
  "  # Compute child element bounds (i+1 = t6).\n" ++
  "  addi t5, t6, 1\n" ++
  "  beq t5, s4, .Lwhcl_use_end\n" ++
  "  slli t5, t5, 2\n" ++
  "  add t5, s0, t5\n" ++
  "  lwu t0, 0(t5)\n" ++
  "  add t0, s0, t0             # child end\n" ++
  "  j .Lwhcl_have_end\n" ++
  ".Lwhcl_use_end:\n" ++
  "  add t0, s0, s1             # child end = section end\n" ++
  ".Lwhcl_have_end:\n" ++
  "  sub s8, t0, s7             # child len\n" ++
  "  # Step 1: extract child.parent_hash.\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  la a2, whcl_child_ph\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  beqz a0, .Lwhcl_after_ph\n" ++
  "  # K202: 1 = parse fail -> map to 3, 2 = size -> map to 4.\n" ++
  "  addi a0, a0, 2\n" ++
  "  j .Lwhcl_ret\n" ++
  ".Lwhcl_after_ph:\n" ++
  "  # Step 2: keccak(parent_rlp).\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  la a2, whcl_parent_keccak\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 3: 32-byte compare.\n" ++
  "  la t0, whcl_child_ph\n" ++
  "  la t1, whcl_parent_keccak\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwhcl_diff\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwhcl_diff\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwhcl_diff\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwhcl_diff\n" ++
  "  li t4, 1\n" ++
  "  sd t4, 0(s3)\n" ++
  ".Lwhcl_diff:\n" ++
  "  li a0, 0\n" ++
  "  j .Lwhcl_ret\n" ++
  ".Lwhcl_oob_p:\n" ++
  "  li a0, 1\n" ++
  "  j .Lwhcl_ret\n" ++
  ".Lwhcl_oob_c:\n" ++
  "  li a0, 2\n" ++
  ".Lwhcl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_witness_headers_chain_link_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : parent_idx (u64 LE)
      bytes 24..   : witness.headers section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..4)
      bytes  8..16 : is_valid (u64; 0 or 1) -/
def ziskWitnessHeadersChainLinkAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_headers_len\n" ++
  "  ld a2, 16(a6)               # parent_idx\n" ++
  "  addi a0, a6, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # is_valid out\n" ++
  "  jal ra, witness_headers_chain_link_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhcl_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  witnessHeadersChainLinkAtIndexFunction ++ "\n" ++
  ".Lwhcl_pdone:"

def ziskWitnessHeadersChainLinkAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "whcl_child_ph:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "whcl_parent_keccak:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
