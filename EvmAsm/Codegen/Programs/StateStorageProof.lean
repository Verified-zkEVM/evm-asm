/-
  EvmAsm.Codegen.Programs.StateStorageProof

  End-to-end light-client slot inclusion proof: given a
  trusted state_root, address, slot_idx, and expected slot
  value, walk both the state trie (to find the account's
  storage_root) and then the storage trie (to find the
  slot value). The intermediate storage_root is never
  exposed to the caller.

  Composes K28 `account_at_address` + K29 `slot_at_index`.

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

/-! ## state_slot_inclusion_proof_verify

    Composes the two halves of light-client slot verification
    into a single primitive: trusted `state_root`, walked
    through `witness.state` to find the account at `address`,
    then through `witness.storage` to find the value at
    `slot_idx`, compared against `expected_value_be`.

    Distinct from the two-step sequence:
      * `state_account_inclusion_proof_verify` (PR #7193)
        verifies an entire account struct against a trusted
        state_root.
      * `storage_slot_inclusion_proof_verify` (PR #7191)
        verifies a slot against a trusted storage_root.

    This primitive starts from a trusted **state_root** alone
    (no intermediate storage_root needed) and verifies the
    final slot value end-to-end. The intermediate
    storage_root is computed internally and discarded -- not
    exposed to the caller.

    SLOAD-spec semantics propagate through:
      * If account absent from state trie: account has empty
        storage trie, all slots read as 0 (SLOAD spec). So
        is_match = 1 iff expected_value == 0.
      * If slot absent from the walked storage trie: SLOAD
        yields 0. Same rule: is_match = 1 iff expected == 0.

    Calling convention (8 args + scratch stash):
      a0 (input)  : state_root ptr (32 bytes)
      a1 (input)  : address ptr (20 bytes)
      a2 (input)  : slot_idx_be ptr (32 bytes BE)
      a3 (input)  : expected_value_be ptr (32 bytes BE)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : witness.storage ptr
      a7 (input)  : witness.storage len
      ssip_is_match_out  : u64* (caller-set scratch label)
      ra (input)  : return

      a0 (output) :
        0 = success (is_match valid; slot value matches)
        1 = account not in state trie (is_match = expected==0)
        2 = state-trie mpt walk error
        3 = account RLP decode failure
        4 = slot not in storage trie (is_match = expected==0)
        5 = storage-trie mpt walk error
        6 = slot RLP decode failure
-/
def stateSlotInclusionProofVerifyFunction : String :=
  "state_slot_inclusion_proof_verify:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                  # state_root ptr\n" ++
  "  mv s1, a1                  # address ptr\n" ++
  "  mv s2, a2                  # slot_idx_be ptr\n" ++
  "  mv s3, a3                  # expected_value_be ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # witness.storage ptr\n" ++
  "  mv s7, a7                  # witness.storage len\n" ++
  "  la s8, ssip_is_match_out\n" ++
  "  sd zero, 0(s8)             # pre-clear is_match\n" ++
  "  # Reset walked-value buffer.\n" ++
  "  la t0, ssip_walked_value_be\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  # Step 1: account_at_address(addr, state_root, witness.state).\n" ++
  "  mv a0, s1                  # address ptr\n" ++
  "  li a1, 20\n" ++
  "  mv a2, s0                  # state_root ptr\n" ++
  "  mv a3, s4                  # witness.state ptr\n" ++
  "  mv a4, s5                  # witness.state len\n" ++
  "  la a5, ssip_walked_struct\n" ++
  "  jal ra, account_at_address\n" ++
  "  beqz a0, .Lssipv_state_ok\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lssipv_account_absent\n" ++
  "  # status 2 (mpt error) or 3 (acct decode) propagate.\n" ++
  "  j .Lssipv_ret\n" ++
  ".Lssipv_account_absent:\n" ++
  "  # SLOAD: absent account = empty storage trie = all-zero slots.\n" ++
  "  # is_match = 1 iff expected_value_be is all-zero.\n" ++
  "  ld t2,  0(s3); bnez t2, .Lssipv_absent_a_done\n" ++
  "  ld t2,  8(s3); bnez t2, .Lssipv_absent_a_done\n" ++
  "  ld t2, 16(s3); bnez t2, .Lssipv_absent_a_done\n" ++
  "  ld t2, 24(s3); bnez t2, .Lssipv_absent_a_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s8)\n" ++
  ".Lssipv_absent_a_done:\n" ++
  "  li a0, 1\n" ++
  "  j .Lssipv_ret\n" ++
  ".Lssipv_state_ok:\n" ++
  "  # Account is present. Storage root is at struct + 40.\n" ++
  "  la s9, ssip_walked_struct\n" ++
  "  addi s9, s9, 40            # storage_root ptr (inside struct)\n" ++
  "  # Step 2: slot_at_index(slot_idx, storage_root, witness.storage).\n" ++
  "  mv a0, s2                  # slot_idx_be ptr\n" ++
  "  li a1, 32\n" ++
  "  mv a2, s9                  # storage_root ptr\n" ++
  "  mv a3, s6                  # witness.storage ptr\n" ++
  "  mv a4, s7                  # witness.storage len\n" ++
  "  la a5, ssip_walked_value_be\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lssipv_compare_present\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lssipv_slot_absent\n" ++
  "  # status 2/3 from slot_at_index = remap to 5/6.\n" ++
  "  addi a0, a0, 3             # 2 -> 5, 3 -> 6\n" ++
  "  j .Lssipv_ret\n" ++
  ".Lssipv_slot_absent:\n" ++
  "  # SLOAD: absent slot = 0. is_match=1 iff expected==0.\n" ++
  "  ld t2,  0(s3); bnez t2, .Lssipv_absent_s_done\n" ++
  "  ld t2,  8(s3); bnez t2, .Lssipv_absent_s_done\n" ++
  "  ld t2, 16(s3); bnez t2, .Lssipv_absent_s_done\n" ++
  "  ld t2, 24(s3); bnez t2, .Lssipv_absent_s_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s8)\n" ++
  ".Lssipv_absent_s_done:\n" ++
  "  li a0, 4\n" ++
  "  j .Lssipv_ret\n" ++
  ".Lssipv_compare_present:\n" ++
  "  # Compare ssip_walked_value_be vs expected_value_be.\n" ++
  "  la t0, ssip_walked_value_be\n" ++
  "  ld t2,  0(t0); ld t3,  0(s3); bne t2, t3, .Lssipv_present_done\n" ++
  "  ld t2,  8(t0); ld t3,  8(s3); bne t2, t3, .Lssipv_present_done\n" ++
  "  ld t2, 16(t0); ld t3, 16(s3); bne t2, t3, .Lssipv_present_done\n" ++
  "  ld t2, 24(t0); ld t3, 24(s3); bne t2, t3, .Lssipv_present_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s8)\n" ++
  ".Lssipv_present_done:\n" ++
  "  li a0, 0\n" ++
  ".Lssipv_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_state_slot_inclusion_proof_verify`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes   0.. 8 : (ziskemu metadata)
      bytes   8..16 : witness_state_len (u64 LE)
      bytes  16..24 : witness_storage_len (u64 LE)
      bytes  24..56 : state_root (32 bytes)
      bytes  56..76 : address (20 bytes)
      bytes  76..108: slot_idx_be (32 bytes)
      bytes 108..140: expected_value_be (32 bytes)
      bytes 140..   : witness.state section bytes,
                      then witness.storage section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (0..6)
      bytes  8..16 : is_match (u64; 0 or 1) -/
def ziskStateSlotInclusionProofVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t4, 0x40000000\n" ++
  "  ld a5, 8(t4)                # witness_state_len\n" ++
  "  ld a7, 16(t4)               # witness_storage_len\n" ++
  "  addi a0, t4, 24             # state_root ptr\n" ++
  "  addi a1, t4, 56             # address ptr\n" ++
  "  addi a2, t4, 76             # slot_idx_be ptr\n" ++
  "  addi a3, t4, 108            # expected_value_be ptr\n" ++
  "  addi a4, t4, 140            # witness.state ptr\n" ++
  "  add  a6, a4, a5             # witness.storage ptr = state ptr + state len\n" ++
  "  jal ra, state_slot_inclusion_proof_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  la t1, ssip_is_match_out\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)                # is_match\n" ++
  "  j .Lssipv_pdone\n" ++
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
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  stateSlotInclusionProofVerifyFunction ++ "\n" ++
  ".Lssipv_pdone:"

def ziskStateSlotInclusionProofVerifyDataSection : String :=
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
  ".balign 8\n" ++
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "ssip_walked_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "ssip_walked_value_be:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ssip_is_match_out:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
