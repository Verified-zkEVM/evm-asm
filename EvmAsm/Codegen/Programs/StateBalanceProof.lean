/-
  EvmAsm.Codegen.Programs.StateBalanceProof

  Light-client balance inclusion proof against a trusted
  state_root. Third sibling in the per-field family:
    * state_code_hash_inclusion_proof_verify (#7197)
    * state_storage_root_inclusion_proof_verify (#7206)
    * state_balance_inclusion_proof_verify (this)

  Compares the 32-byte big-endian u256 balance field at
  account struct offset +8. Cheaper than checking the full
  104-byte struct (#7193) when the caller only cares about
  the balance.

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

/-! ## state_balance_inclusion_proof_verify

    Light-client balance inclusion-proof primitive: given a
    trusted `state_root`, address, expected 32-byte big-endian
    u256 balance, and witness.state SSZ list section, verify
    that walking the MPT yields an account whose balance
    field (struct offset +8, 32 BE bytes) matches.

    Common predicates this enables (caller composes):
      * "Does this address have AT LEAST X wei?"
        Call this with expected = X. is_match=1 iff exact;
        for "at least", caller needs a separate u256 compare
        primitive. This primitive answers only the exact-
        match case.
      * "Is this account broke?" expected = 0; covers both
        the present-with-zero and absent cases via is_match=1.
      * Bridge snapshot freshness check: caller has a
        (state_root, address, balance) record; this verifies
        the triple is consistent.

    Spec edge case: non-existent address has balance = 0
    (spec default). So absent + expected=0 reports
    is_match=1 (zero-balance default) AND status=1 (absent).
    Two signals -- callers caring about presence use status;
    those caring only about balance value use is_match.

    Composes K28 `account_at_address` + 32-byte u256 BE
    comparison.

    Calling convention:
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : expected_balance_be ptr (32 bytes BE u256)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : u64 out ptr (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (walked balance matches expected exactly)
        1 = account not in trie (is_match = expected==0)
        2 = mpt_walk parse error
        3 = account RLP decode failure
-/
def stateBalanceInclusionProofVerifyFunction : String :=
  "state_balance_inclusion_proof_verify:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # expected_balance_be ptr\n" ++
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
  "  la a5, sbip_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lsbip_compare_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lsbip_compare_absent\n" ++
  "  # status 2/3 propagate.\n" ++
  "  j .Lsbip_ret\n" ++
  ".Lsbip_compare_present:\n" ++
  "  # Walked struct: balance at offset +8 (32 BE bytes).\n" ++
  "  la t0, sbip_walked_struct\n" ++
  "  ld t2,  8(t0); ld t3,  0(s2); bne t2, t3, .Lsbip_no_match\n" ++
  "  ld t2, 16(t0); ld t3,  8(s2); bne t2, t3, .Lsbip_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 16(s2); bne t2, t3, .Lsbip_no_match\n" ++
  "  ld t2, 32(t0); ld t3, 24(s2); bne t2, t3, .Lsbip_no_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lsbip_no_match:\n" ++
  "  li a0, 0\n" ++
  "  j .Lsbip_ret\n" ++
  ".Lsbip_compare_absent:\n" ++
  "  # Absent: spec default balance = 0. is_match = 1 iff\n" ++
  "  # expected_balance_be is all zeros.\n" ++
  "  ld t2,  0(s2); bnez t2, .Lsbip_absent_done\n" ++
  "  ld t2,  8(s2); bnez t2, .Lsbip_absent_done\n" ++
  "  ld t2, 16(s2); bnez t2, .Lsbip_absent_done\n" ++
  "  ld t2, 24(s2); bnez t2, .Lsbip_absent_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lsbip_absent_done:\n" ++
  "  li a0, 1\n" ++
  ".Lsbip_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_state_balance_inclusion_proof_verify`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..48 : state_root (32 bytes)
      bytes 48..68 : address (20 bytes)
      bytes 68..100: expected_balance_be (32 bytes BE)
      bytes 100..  : witness.state section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status
      bytes  8..16 : is_match -/
def ziskStateBalanceInclusionProofVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a4, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # state_root ptr\n" ++
  "  addi a1, a6, 48             # address ptr\n" ++
  "  addi a2, a6, 68             # expected_balance_be ptr\n" ++
  "  addi a3, a6, 100            # witness.state ptr\n" ++
  "  li a5, 0xa0010008           # is_match out\n" ++
  "  jal ra, state_balance_inclusion_proof_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsbip_pdone\n" ++
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
  stateBalanceInclusionProofVerifyFunction ++ "\n" ++
  ".Lsbip_pdone:"

def ziskStateBalanceInclusionProofVerifyDataSection : String :=
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
  "sbip_walked_struct:\n" ++
  "  .zero 104"


end EvmAsm.Codegen
