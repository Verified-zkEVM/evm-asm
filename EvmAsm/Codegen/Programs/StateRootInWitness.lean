/-
  EvmAsm.Codegen.Programs.StateRootInWitness

  Precondition primitive for state-trie verification:
  given a parent_header_rlp and the witness.state SSZ list
  section, extract `header.state_root` and answer whether
  witness.state contains a node whose keccak256 equals that
  state_root.

  Distinct from the inclusion-proof primitives (#7187, #7193,
  #7194, #7197): this does NOT walk the MPT. It only checks
  that the root is REACHABLE -- i.e. that any subsequent
  walk has a chance of starting. A useful screening pass
  before invoking a full state-walk primitive.

  Composes K201 `header_extract_state_root` + K19
  `witness_lookup_by_hash`.

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

/-! ## parent_state_root_present_in_witness_state

    Given a parent_header_rlp + witness.state, return whether
    `keccak256(node) == header.state_root` for some node in
    witness.state. Doesn't decode the matched node, doesn't
    walk -- pure presence check.

    Useful for:
      * Pre-screening before a full state-walk (#7187, #7193).
      * Detecting structurally invalid witness.state where the
        committed root is missing entirely (common bug: stale
        witness from a previous block).
      * Cheap aggregate validation: run this for many headers
        in a chain and rule out any whose state_root is
        unreachable before doing expensive per-account walks.

    Calling convention (5 args):
      a0 (input)  : parent_header_rlp ptr
      a1 (input)  : parent_header_rlp len
      a2 (input)  : witness.state ptr
      a3 (input)  : witness.state len
      a4 (input)  : u64 out ptr (is_present)
      ra (input)  : return

      a0 (output) :
        0 = success (is_present valid)
        1 = header parse failure
        2 = state_root field has unexpected size
-/
def parentStateRootPresentInWitnessStateFunction : String :=
  "parent_state_root_present_in_witness_state:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp len\n" ++
  "  mv s2, a2                  # witness.state ptr\n" ++
  "  mv s3, a3                  # witness.state len\n" ++
  "  mv s4, a4                  # is_present out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # Step 1: extract state_root into psrp_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, psrp_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lpsrp_ret      # status 1 (parse) or 2 (size) propagate.\n" ++
  "  # Step 2: K19 over witness.state with state_root as target.\n" ++
  "  mv a0, s2                  # section ptr\n" ++
  "  mv a1, s3                  # section_len\n" ++
  "  la a2, psrp_state_root\n" ++
  "  la a3, psrp_match_offset   # discard\n" ++
  "  la a4, psrp_match_length   # discard\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  # K19: a0 = 0 (hit) or 1 (miss).\n" ++
  "  bnez a0, .Lpsrp_miss\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)               # is_present = 1\n" ++
  ".Lpsrp_miss:\n" ++
  "  li a0, 0                   # success (is_present already set)\n" ++
  ".Lpsrp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_parent_state_root_present_in_witness_state`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : parent_header_rlp_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..   : parent_header_rlp ++ witness.state bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : is_present (u64; 0 or 1) -/
def ziskParentStateRootPresentInWitnessStatePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # parent_header_rlp_len\n" ++
  "  ld a3, 16(a6)               # witness_state_len\n" ++
  "  addi a0, a6, 24             # parent_header_rlp ptr\n" ++
  "  add  a2, a0, a1             # witness.state ptr = header ptr + header_len\n" ++
  "  li a4, 0xa0010008           # is_present out\n" ++
  "  jal ra, parent_state_root_present_in_witness_state\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lpsrp_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  parentStateRootPresentInWitnessStateFunction ++ "\n" ++
  ".Lpsrp_pdone:"

def ziskParentStateRootPresentInWitnessStateDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "psrp_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "psrp_match_offset:\n" ++
  "  .zero 8\n" ++
  "psrp_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
