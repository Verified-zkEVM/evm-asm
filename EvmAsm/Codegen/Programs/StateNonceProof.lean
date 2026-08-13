/-
  EvmAsm.Codegen.Programs.StateNonceProof

  Light-client u64 nonce inclusion proof against a trusted
  state_root. Completes the per-field family:
    * state_code_hash_inclusion_proof_verify (#7197)
    * state_storage_root_inclusion_proof_verify (#7206)
    * state_balance_inclusion_proof_verify (#7209)
    * state_nonce_inclusion_proof_verify (this)

  All four primitives accept a trusted state_root, walk to
  the account, and compare a single field against an
  expected value. Together they cover all 4 RLP fields of
  the account struct.

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

/-! ## state_nonce_inclusion_proof_verify

    Light-client nonce inclusion-proof primitive: given a
    trusted `state_root`, address, expected u64 nonce, and
    witness.state SSZ list section, verify that walking the
    MPT yields an account whose nonce field (struct offset
    +0, 8 bytes little-endian) equals the expected value.

    Distinction from siblings: nonce is a u64 (8 bytes),
    not a u256 or 32-byte hash. So the expected value is
    passed directly in a register, not via a pointer. This
    is the only per-field primitive where the calling
    convention differs from the others by this much.

    Common use cases:
      * EIP-7702 / replay-protection: verify the
        signature's claimed nonce matches the chain's view.
      * Anti-frontrun checks: bridge / relayer wants to
        commit a transaction at nonce N -- this verifies
        the chain's current nonce is exactly N.
      * "Is this a fresh account?" expected = 0 covers both
        the present-with-zero-nonce AND absent paths.

    Spec edge case: a non-existent address has nonce = 0
    (spec default). So absent + expected = 0 reports
    is_match = 1 AND status = 1. Two signals -- callers
    caring about presence use status; those caring only
    about nonce value use is_match.

    Composes K28 `account_at_address` + u64 LE compare.

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : expected_nonce (u64, passed by value)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : u64 out ptr (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (walked nonce matches)
        1 = account not in trie (is_match = expected==0)
        2 = mpt_walk parse error
        3 = account RLP decode failure
-/
def stateNonceInclusionProofVerifyFunction : String :=
  "state_nonce_inclusion_proof_verify:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # expected_nonce (u64)\n" ++
  "  mv s3, a3                  # witness.state ptr\n" ++
  "  mv s4, a4                  # witness.state len\n" ++
  "  mv s5, a5                  # is_match out\n" ++
  "  sd zero, 0(s5)\n" ++
  "  # K28 account_at_address.\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root ptr\n" ++
  "  mv a3, s3                  # witness.state ptr\n" ++
  "  mv a4, s4                  # witness.state len\n" ++
  "  la a5, snip_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsnip_compare_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsnip_compare_absent\n" ++
  "  # status 2/3 propagate.\n" ++
  "  j .Lsnip_ret\n" ++
  ".Lsnip_compare_present:\n" ++
  "  # Walked struct: nonce u64 LE at offset +0.\n" ++
  "  la t0, snip_walked_struct\n" ++
  "  ld t2, 0(t0)\n" ++
  "  bne t2, s2, .Lsnip_no_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lsnip_no_match:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsnip_ret\n" ++
  ".Lsnip_compare_absent:\n" ++
  "  # Absent: spec default nonce = 0. is_match = (expected == 0).\n" ++
  "  bnez s2, .Lsnip_absent_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lsnip_absent_done:\n" ++
  "  li a0, 1\n" ++
  ".Lsnip_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_state_nonce_inclusion_proof_verify`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..24 : expected_nonce (u64 LE)
      bytes 24..56 : state_root (32 bytes)
      bytes 56..76 : address (20 bytes)
      bytes 76..   : witness.state section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : is_match -/
def ziskStateNonceInclusionProofVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a4, 8(a6)                # witness_state_len\n" ++
  "  ld a2, 16(a6)               # expected_nonce u64\n" ++
  "  addi a0, a6, 24             # state_root ptr\n" ++
  "  addi a1, a6, 56             # address ptr\n" ++
  "  addi a3, a6, 76             # witness.state ptr\n" ++
  "  li a5, 0xa0010008           # is_match out\n" ++
  "  jal ra, state_nonce_inclusion_proof_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsnip_pdone\n" ++
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
  stateNonceInclusionProofVerifyFunction ++ "\n" ++
  ".Lsnip_pdone:"

def ziskStateNonceInclusionProofVerifyDataSection : String :=
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
  "snip_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
