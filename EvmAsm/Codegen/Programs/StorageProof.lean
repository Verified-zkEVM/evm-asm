/-
  EvmAsm.Codegen.Programs.StorageProof

  Storage-proof verification primitives that operate on a
  caller-supplied storage_root (rather than one extracted from
  a header). Useful for light-client / bridge proofs where the
  storage_root comes from a trusted source other than the
  parent header.

  Currently hosts `storage_slot_inclusion_proof_verify`.

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

/-! ## storage_slot_inclusion_proof_verify

    Light-client storage-inclusion-proof primitive: given a
    trusted `storage_root` (e.g., obtained from a bridge / state
    snapshot rather than walked from a parent header), a
    `slot_idx`, an expected u256 `slot_value`, and a
    `witness.storage` SSZ list section, verify that walking the
    MPT from `storage_root` with key `keccak256(slot_idx)`
    yields `slot_value`.

    Spec-defining edge case: slot-absent vs explicit-zero
    distinction. SLOAD semantics say uninitialised slots are 0,
    so an `expected_value = 0` with a missing slot in the trie
    is reported as `is_match = 1` (the values agree per SLOAD
    spec) AND status 1 (the slot wasn't actually in the trie).
    Callers caring about presence distinguish via status; those
    caring only about value equality use `is_match` directly.

    Distinct from PR `verify_slot_value_matches` (#7188):
      * #7188 takes `(header, address, ...)` and walks the
        state trie to derive the storage_root.
      * THIS primitive takes a trusted `storage_root` directly.
        Useful when the storage_root comes from a non-header
        source (bridge contract, light-client snapshot, etc.).

    Composes K29 `slot_at_index` + 4 u64 compares.

    Calling convention:
      a0 (input)  : storage_root ptr (32 bytes)
      a1 (input)  : slot_idx_be ptr (32 bytes; big-endian u256)
      a2 (input)  : expected_value_be ptr (32 bytes; big-endian u256)
      a3 (input)  : witness.storage ptr
      a4 (input)  : witness.storage len
      a5 (input)  : u64 out ptr (is_match)
      ra (input)  : return

      a0 (output) :
        0 = success (is_match valid; value walked from trie matches)
        1 = slot not in trie (is_match = expected == 0)
        2 = mpt_walk parse error
        3 = slot RLP decode failure
-/
def storageSlotInclusionProofVerifyFunction : String :=
  "storage_slot_inclusion_proof_verify:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # storage_root ptr\n" ++
  "  mv s1, a1                  # slot_idx_be ptr\n" ++
  "  mv s2, a2                  # expected_value_be ptr\n" ++
  "  mv s3, a3                  # witness.storage ptr\n" ++
  "  mv s4, a4                  # witness.storage len\n" ++
  "  mv s5, a5                  # is_match out\n" ++
  "  sd zero, 0(s5)\n" ++
  "  # Reset walked value buffer.\n" ++
  "  la t0, ssip_walked_value_be\n" ++
  "  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  # Step 1: slot_at_index over witness.storage with the trusted storage_root.\n" ++
  "  mv a0, s1                  # slot_idx_be\n" ++
  "  li a1, 32\n" ++
  "  mv a2, s0                  # storage_root ptr\n" ++
  "  mv a3, s3                  # witness.storage ptr\n" ++
  "  mv a4, s4                  # witness.storage len\n" ++
  "  la a5, ssip_walked_value_be\n" ++
  "  jal ra, slot_at_index\n" ++
  "  beqz a0, .Lssip_compare\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lssip_slot_miss_compare\n" ++
  "  # 2/3 propagate.\n" ++
  "  j .Lssip_ret\n" ++
  ".Lssip_slot_miss_compare:\n" ++
  "  # Walked value is zero (per slot_at_index's contract on miss);\n" ++
  "  # match iff expected is also zero.\n" ++
  "  la t0, ssip_walked_value_be\n" ++
  "  ld t2,  0(t0); ld t3,  0(s2); bne t2, t3, .Lssip_slot_miss_done\n" ++
  "  ld t2,  8(t0); ld t3,  8(s2); bne t2, t3, .Lssip_slot_miss_done\n" ++
  "  ld t2, 16(t0); ld t3, 16(s2); bne t2, t3, .Lssip_slot_miss_done\n" ++
  "  ld t2, 24(t0); ld t3, 24(s2); bne t2, t3, .Lssip_slot_miss_done\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lssip_slot_miss_done:\n" ++
  "  li a0, 1                   # propagate slot-miss status\n" ++
  "  j .Lssip_ret\n" ++
  ".Lssip_compare:\n" ++
  "  la t0, ssip_walked_value_be\n" ++
  "  ld t2,  0(t0); ld t3,  0(s2); bne t2, t3, .Lssip_no_match\n" ++
  "  ld t2,  8(t0); ld t3,  8(s2); bne t2, t3, .Lssip_no_match\n" ++
  "  ld t2, 16(t0); ld t3, 16(s2); bne t2, t3, .Lssip_no_match\n" ++
  "  ld t2, 24(t0); ld t3, 24(s2); bne t2, t3, .Lssip_no_match\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(s5)\n" ++
  ".Lssip_no_match:\n" ++
  "  li a0, 0\n" ++
  ".Lssip_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_storage_slot_inclusion_proof_verify`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_storage_len (u64 LE)
      bytes 16..48 : storage_root (32 bytes)
      bytes 48..80 : slot_idx_be (32 bytes BE)
      bytes 80..112: expected_value_be (32 bytes BE)
      bytes 112..  : witness.storage section bytes
    Output layout:
      bytes  0.. 8 : status (0 / 1 / 2 / 3)
      bytes  8..16 : is_match (u64; 0 or 1) -/
def ziskStorageSlotInclusionProofVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a4, 8(a6)                # witness_storage_len\n" ++
  "  addi a0, a6, 16             # storage_root ptr\n" ++
  "  addi a1, a6, 48             # slot_idx_be ptr\n" ++
  "  addi a2, a6, 80             # expected_value_be ptr\n" ++
  "  addi a3, a6, 112            # witness.storage ptr\n" ++
  "  li a5, 0xa0010008           # is_match out\n" ++
  "  jal ra, storage_slot_inclusion_proof_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lssip_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  storageSlotInclusionProofVerifyFunction ++ "\n" ++
  ".Lssip_pdone:"

def ziskStorageSlotInclusionProofVerifyDataSection : String :=
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
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 32\n" ++
  "ssip_walked_value_be:\n" ++
  "  .zero 32"


end EvmAsm.Codegen
