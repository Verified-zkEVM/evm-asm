/-
  EvmAsm.Codegen.Programs.StorageVerify

  Storage verification primitives: given (header, address,
  slot_idx, expected_value, witness.state, witness.storage),
  walk the state trie to the account, walk the storage trie to
  the slot, and check whether the decoded u256 matches the
  expected value.

  Sibling of `AccountVerify.lean` (state-side equality checks).

  Currently hosts `verify_slot_value_matches`.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## verify_slot_value_matches

    Walk the state trie at header.state_root to the account
    leaf, then walk the per-account storage trie to the slot,
    and bytewise-compare the decoded u256 value against a
    caller-supplied expected u256. Returns `is_match = 1` iff
    they match.

    Spec-side use case: a stateless-guest test harness wants to
    confirm that witness.storage encodes a specific slot value
    for a specific account. Rather than calling
    `slot_at_header_state_root` and writing the compare in the
    caller, this primitive does one full walk + 4 u64 compares.

    Distinct from:
      * PR `slot_at_header_state_root` (#7145) -- RETURNS the
        u256 value; doesn't compare.
      * PR `sload_at_header_state_root` (#7161) -- returns the
        u256 value flattening missing to 0 (SLOAD spec).
      * PR `verify_account_struct_matches` (#7187) -- the
        state-side sibling of THIS primitive (account-level
        equality vs storage-slot equality).

    Note: the expected value is passed via the scratch label
    `vsvm_expected_value_be` (32-byte BE) rather than as an
    argument register, because the function already needs all
    8 a0..a7 slots for the other inputs.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : slot_idx_be ptr (32 bytes; big-endian u256)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : witness.storage ptr
      a7 (input)  : witness.storage len
      (caller pre-populates `vsvm_expected_value_be` with 32 B BE)
      ra (input)  : return

      a0 (output) :
        0 = success (`vsvm_is_match` holds 0 or 1)
        1 = account not in state trie (is_match = 0)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        5 = slot not in storage trie (is_match = 0
            unless expected value is itself zero)
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure

      The is_match flag is meaningful on status 0 OR 5 -- the
      latter because a missing slot defaults to 0 per SLOAD
      spec, and the caller might legitimately expect zero.
-/
def verifySlotValueMatchesFunction : String :=
  "verify_slot_value_matches:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,   8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4,  40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8,  72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # address ptr\n" ++
  "  mv s3, a3                  # slot_idx_be ptr\n" ++
  "  mv s4, a4                  # witness.state ptr\n" ++
  "  mv s5, a5                  # witness.state len\n" ++
  "  mv s6, a6                  # witness.storage ptr\n" ++
  "  mv s7, a7                  # witness.storage len\n" ++
  "  # Reset is_match output and the walked-value buffer.\n" ++
  "  la t0, vsvm_is_match\n" ++
  "  sd zero, 0(t0)\n" ++
  "  la t0, vsvm_walked_value_be\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  # Step 1: header.state_root -> vsvm_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vsvm_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lvsvm_step2\n" ++
  "  li a0, 4\n" ++
  "  j .Lvsvm_ret\n" ++
  ".Lvsvm_step2:\n" ++
  "  # Step 2: account_at_address.\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 20\n" ++
  "  la a2, vsvm_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  la s8, vsvm_acct_struct\n" ++
  "  mv a5, s8\n" ++
  "  jal ra, account_at_address\n" ++
  "  bnez a0, .Lvsvm_ret        # 1/2/3 propagate; is_match stays 0\n" ++
  "  # Step 3: slot_at_index over witness.storage.\n" ++
  "  mv a0, s3                  # slot_idx_be\n" ++
  "  li a1, 32\n" ++
  "  addi a2, s8, 40            # &acct.storage_root\n" ++
  "  mv a3, s6                  # witness.storage ptr\n" ++
  "  mv a4, s7                  # witness.storage len\n" ++
  "  la a5, vsvm_walked_value_be\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lvsvm_compare    # 0 -> value in vsvm_walked_value_be\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lvsvm_slot_miss_compare  # 1 -> value is zero\n" ++
  "  # 2 -> 6, 3 -> 7\n" ++
  "  addi a0, a0, 4\n" ++
  "  j .Lvsvm_ret\n" ++
  ".Lvsvm_slot_miss_compare:\n" ++
  "  # slot not found -> walked value is zero (already zeroed).\n" ++
  "  # Compare against expected; if expected is also zero, is_match = 1.\n" ++
  "  la t0, vsvm_walked_value_be\n" ++
  "  la t1, vsvm_expected_value_be\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvsvm_set_no_match_slot_miss\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvsvm_set_no_match_slot_miss\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvsvm_set_no_match_slot_miss\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvsvm_set_no_match_slot_miss\n" ++
  "  la t0, vsvm_is_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lvsvm_set_no_match_slot_miss:\n" ++
  "  li a0, 5                   # propagate slot-miss status\n" ++
  "  j .Lvsvm_ret\n" ++
  ".Lvsvm_compare:\n" ++
  "  la t0, vsvm_walked_value_be\n" ++
  "  la t1, vsvm_expected_value_be\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvsvm_no_match\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvsvm_no_match\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvsvm_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvsvm_no_match\n" ++
  "  la t0, vsvm_is_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  ".Lvsvm_no_match:\n" ++
  "  li a0, 0\n" ++
  ".Lvsvm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,   8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4,  40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8,  72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_verify_slot_value_matches`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len      (u64 LE)
      bytes 16..24 : witness_state_len   (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..64 : slot_idx_be (32-byte BE u256)
      bytes 64..96 : expected_value_be (32-byte BE u256)
      bytes 96..116: address (20 bytes)
      bytes 116..116+H            : header_rlp
      bytes 116+H..116+H+WS       : witness.state
      bytes 116+H+WS..            : witness.storage
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_match (u64; 0 or 1) -/
def ziskVerifySlotValueMatchesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000\n" ++
  "  ld t2,  8(t1)               # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # witness_storage_len\n" ++
  "  addi a3, t1, 32             # slot_idx_be ptr\n" ++
  "  addi t5, t1, 64             # expected_value_be ptr\n" ++
  "  addi a2, t1, 96             # address ptr\n" ++
  "  # Copy expected_value_be into vsvm_expected_value_be (32 B).\n" ++
  "  la t6, vsvm_expected_value_be\n" ++
  "  ld t0,  0(t5); sd t0,  0(t6)\n" ++
  "  ld t0,  8(t5); sd t0,  8(t6)\n" ++
  "  ld t0, 16(t5); sd t0, 16(t6)\n" ++
  "  ld t0, 24(t5); sd t0, 24(t6)\n" ++
  "  addi a0, t1, 116            # header_rlp ptr\n" ++
  "  mv a1, t2\n" ++
  "  add a4, a0, t2              # witness.state ptr\n" ++
  "  mv a5, t3\n" ++
  "  add a6, a4, t3              # witness.storage ptr\n" ++
  "  mv a7, t4\n" ++
  "  jal ra, verify_slot_value_matches\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, vsvm_is_match; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Lvsvm_pdone\n" ++
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
  headerExtractStateRootFunction ++ "\n" ++
  verifySlotValueMatchesFunction ++ "\n" ++
  ".Lvsvm_pdone:"

def ziskVerifySlotValueMatchesDataSection : String :=
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
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "vsvm_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vsvm_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "vsvm_walked_value_be:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "vsvm_expected_value_be:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vsvm_is_match:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
