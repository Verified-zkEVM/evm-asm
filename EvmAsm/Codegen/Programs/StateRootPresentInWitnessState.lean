/-
  EvmAsm.Codegen.Programs.StateRootPresentInWitnessState

  Pure presence predicate: given a state_root (passed
  directly, no header) and witness.state, check whether
  witness.state contains a node whose keccak256 equals
  state_root.

  Symmetric counterpart to #7204
  (`storage_root_present_in_witness_storage`): state-trie
  side. Lighter than #7200
  (`parent_state_root_present_in_witness_state`) which
  parses the state_root from a header first.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## state_root_present_in_witness_state

    Cheapest presence check: K19 over witness.state with a
    caller-supplied state_root as target. Does NOT walk the
    MPT, does NOT decode any node.

    Symmetric to #7204:

      | PR    | section            | root input         |
      |-------|--------------------|--------------------|
      | #7200 | witness.state      | extracted from hdr |
      | this  | witness.state      | caller-supplied    |
      | #7204 | witness.storage    | caller-supplied    |

    Use cases:
      * Pre-check when caller already has a trusted
        state_root (from a bridge oracle or upstream
        extraction) -- skip header parsing entirely.
      * Fail-fast before invoking the full inclusion-proof
        family (#7193, #7197, #7206, #7209, #7212).
      * Witness self-test: caller has computed state_root
        from a single-leaf witness reconstruction and wants
        to confirm the witness round-trips against itself.

    Calling convention (4 args):
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : witness.state ptr
      a2 (input)  : witness.state len
      a3 (input)  : u64 out ptr (is_present)
      ra (input)  : return

      a0 (output) : status (always 0; predicate has no
                    structural failure modes -- K19 handles
                    empty section and malformed offsets
                    internally)
-/
def stateRootPresentInWitnessStateFunction : String :=
  "state_root_present_in_witness_state:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a3                  # is_present out\n" ++
  "  sd zero, 0(s1)\n" ++
  "  mv a0, a1                  # section ptr\n" ++
  "  mv a1, a2                  # section_len\n" ++
  "  mv a2, s0                  # target_hash\n" ++
  "  la a3, srpws_match_offset\n" ++
  "  la a4, srpws_match_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lsrpws_miss\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s1)\n" ++
  ".Lsrpws_miss:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_state_root_present_in_witness_state`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..   : witness.state section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : is_present (u64; 0 or 1) -/
def ziskStateRootPresentInWitnessStatePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # witness.state ptr\n" ++
  "  li a3, 0xa0010008           # is_present out\n" ++
  "  jal ra, state_root_present_in_witness_state\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsrpws_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  stateRootPresentInWitnessStateFunction ++ "\n" ++
  ".Lsrpws_pdone:"

def ziskStateRootPresentInWitnessStateDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "srpws_match_offset:\n" ++
  "  .zero 8\n" ++
  "srpws_match_length:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
