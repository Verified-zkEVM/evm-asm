/-
  EvmAsm.Codegen.Programs.StateCodeHashProof

  Light-client code-hash inclusion proof against a trusted
  state_root. Distinct from the storage / account variants:
  this is the cheapest predicate for "does this address run
  this code?" (and especially for "is this address an EOA?"
  via expected = EMPTY_CODE_HASH).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## state_code_hash_inclusion_proof_verify

    Light-client code-hash inclusion-proof primitive: given a
    trusted `state_root`, an address, an expected 32-byte
    code_hash, and a `witness.state` SSZ list section, verify
    that walking the MPT from `state_root` with key
    `keccak256(address)` yields an account whose `code_hash`
    field matches.

    Smaller surface than `state_account_inclusion_proof_verify`
    (#7193): comparing only the 32-byte code_hash, not the
    full 104-byte struct. The cheapest primitive for asking:

      * "Is this address an EOA?"
            expected = EMPTY_CODE_HASH
              (keccak256("") = c5d2460186f7233c927e7db2dcc703c0
                              e500b653ca82273b7bfad8045d85a470)
      * "Does this address run contract X?"
            expected = keccak256(X's bytecode)

    Distinct from `verify_code_hash_matches` (PR #7189): #7189
    takes `(header, address, ...)` and derives state_root from
    header[3]. This primitive accepts a caller-supplied
    state_root directly, useful when sourced from non-header
    contexts (bridge snapshot, light-client checkpoint).

    Spec-defining edge case: account-absent semantics. A
    non-existent address has `code_hash = EMPTY_CODE_HASH`
    (spec default). So `expected = EMPTY_CODE_HASH` with the
    address missing from the trie reports
    `is_match = 1` (EOA-by-default) AND `status = 1` (absent).

    Composes K28 `account_at_address` + 32-byte compare on
    the `code_hash` field (struct offset +72).

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : expected_code_hash ptr (32 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : u64 out ptr (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (is_match valid; walked code_hash matches)
        1 = account not in trie (is_match = expected==EMPTY_CODE_HASH)
        2 = mpt_walk parse error
        3 = account RLP decode failure
-/
def stateCodeHashInclusionProofVerifyFunction : String :=
  "state_code_hash_inclusion_proof_verify:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # expected_code_hash ptr\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # is_match out\n" ++
  "  sd zero, 0(s5)\n" ++
  "  # account_at_address(addr, state_root, witness.state).\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root ptr\n" ++
  "  mv a3, s3                  # witness.state ptr\n" ++
  "  mv a4, s4                  # witness.state len\n" ++
  "  la a5, schip_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lschip_compare_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lschip_compare_absent\n" ++
  "  # status 2/3 propagate.\n" ++
  "  j .Lschip_ret\n" ++
  ".Lschip_compare_present:\n" ++
  "  # Walked struct: code_hash at offset +72.\n" ++
  "  la t0, schip_walked_struct\n" ++
  "  ld t2, 72(t0); ld t3,  0(s2); bne t2, t3, .Lschip_no_match\n" ++
  "  ld t2, 80(t0); ld t3,  8(s2); bne t2, t3, .Lschip_no_match\n" ++
  "  ld t2, 88(t0); ld t3, 16(s2); bne t2, t3, .Lschip_no_match\n" ++
  "  ld t2, 96(t0); ld t3, 24(s2); bne t2, t3, .Lschip_no_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lschip_no_match:\n" ++
  "  li a0, 0\n" ++
  "  j .Lschip_ret\n" ++
  ".Lschip_compare_absent:\n" ++
  "  # Absent: spec default code_hash = EMPTY_CODE_HASH.\n" ++
  "  # is_match = 1 iff caller's expected == EMPTY_CODE_HASH.\n" ++
  "  la t1, schip_empty_code_hash\n" ++
  "  ld t2,  0(s2); ld t3,  0(t1); bne t2, t3, .Lschip_absent_done\n" ++
  "  ld t2,  8(s2); ld t3,  8(t1); bne t2, t3, .Lschip_absent_done\n" ++
  "  ld t2, 16(s2); ld t3, 16(t1); bne t2, t3, .Lschip_absent_done\n" ++
  "  ld t2, 24(s2); ld t3, 24(t1); bne t2, t3, .Lschip_absent_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lschip_absent_done:\n" ++
  "  li a0, 1\n" ++
  ".Lschip_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_state_code_hash_inclusion_proof_verify`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..68 : address (20 bytes)
      bytes 68..100: expected_code_hash (32 bytes)
      bytes 100..  : witness.state section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : is_match (u64) -/
def ziskStateCodeHashInclusionProofVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a4, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # expected_code_hash ptr\n" ++
  "  addi a3, a6, 100            # witness.state ptr\n" ++
  "  li a5, 0xa0010008           # is_match out\n" ++
  "  jal ra, state_code_hash_inclusion_proof_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lschip_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  stateCodeHashInclusionProofVerifyFunction ++ "\n" ++
  ".Lschip_pdone:"

def ziskStateCodeHashInclusionProofVerifyDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "schip_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "schip_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"


end EvmAsm.Codegen
