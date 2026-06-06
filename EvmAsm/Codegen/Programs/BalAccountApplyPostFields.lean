/-
  EvmAsm.Codegen.Programs.BalAccountApplyPostFields

  Compose BAL AccountChanges post-value extraction with account RLP rewriting.

  This is the account-value half of BAL replay for post-state-root recompute:
  given the pre-state account RLP and one BAL AccountChanges item, apply the
  final nonce and/or balance post-values reported by the BAL entry. Storage and
  code changes are handled by separate trie/account-root machinery.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.MptStateRootIns

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## baap_delete_single_leaf_storage

    Conservative storage-delete helper for BAL post-state replay. It handles
    only the common one-slot trie case: if the account's prior storageRoot is
    exactly a leaf at the cleared slot, deleting that slot makes the storage
    root the empty trie root. Other trie shapes stay conservative.

    a0 = account RLP ptr        a1 = account RLP length
    a2 = slot key ptr (32 B)    a3 = output account ptr
    a4 = u64 out account length ptr
    a0 (output) = 0 ok / 1 conservative or parse failure. -/
def baapDeleteSingleLeafStorageFunction : String :=
  "baap_delete_single_leaf_storage:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # account\n" ++
  "  mv s1, a1                   # account len\n" ++
  "  mv s2, a2                   # slot key\n" ++
  "  mv s3, a3                   # out account\n" ++
  "  mv s4, a4                   # out len\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2; la a3, aps_off; la a4, aps_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaapdsl_fail\n" ++
  "  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lbaapdsl_fail\n" ++
  "  la t0, aps_off; ld t1, 0(t0); add t1, s0, t1; la t0, baap_storage_root_ptr; sd t1, 0(t0)\n" ++
  "  # Deleting from an empty storage trie is a no-op.\n" ++
  "  mv t2, t1; la t3, aps_empty_root; li t4, 32\n" ++
  ".Lbaapdsl_empty_cmp:\n" ++
  "  beqz t4, .Lbaapdsl_copy_current\n" ++
  "  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lbaapdsl_nonempty\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lbaapdsl_empty_cmp\n" ++
  ".Lbaapdsl_nonempty:\n" ++
  "  mv a0, s2; li a1, 32; la a2, srss_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, srss_key; li a1, 32; la a2, baap_storage_paths\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, aps_witness_ptr; ld a0, 0(t0); beqz a0, .Lbaapdsl_fail\n" ++
  "  la t0, aps_witness_len; ld a1, 0(t0); la t0, baap_storage_root_ptr; ld a2, 0(t0)\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lbaapdsl_fail\n" ++
  "  la t0, aps_witness_ptr; ld t1, 0(t0); la t0, baap_item_off; ld t2, 0(t0); add a0, t1, t2\n" ++
  "  la t0, baap_item_len; ld a1, 0(t0); la a2, baap_walk_val; la a3, baap_walk_val_len\n" ++
  "  la a4, baap_code_item_ptr; la a5, baap_val_len\n" ++
  "  jal ra, mpt_leaf_extract\n" ++
  "  bnez a0, .Lbaapdsl_fail\n" ++
  "  la t0, baap_walk_val_len; ld t0, 0(t0); li t1, 64; bne t0, t1, .Lbaapdsl_fail\n" ++
  "  la t0, baap_walk_val; la t1, baap_storage_paths; li t2, 64\n" ++
  ".Lbaapdsl_path_cmp:\n" ++
  "  beqz t2, .Lbaapdsl_set_empty\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbaapdsl_fail\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbaapdsl_path_cmp\n" ++
  ".Lbaapdsl_set_empty:\n" ++
  "  mv a0, s0; mv a1, s1; la a2, aps_empty_root; mv a3, s3; mv a4, s4\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Lbaapdsl_fail\n" ++
  "  li a0, 0; j .Lbaapdsl_ret\n" ++
  ".Lbaapdsl_copy_current:\n" ++
  "  mv a0, s3; mv a1, s0; mv a2, s1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  sd s1, 0(s4)\n" ++
  "  li a0, 0; j .Lbaapdsl_ret\n" ++
  ".Lbaapdsl_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbaapdsl_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-! ## bal_account_apply_post_fields -- account RLP + BAL item -> post account RLP

    a0 = account RLP ptr        a1 = account RLP length
    a2 = AccountChanges ptr     a3 = AccountChanges length
    a4 = output buffer ptr      a5 = u64 out length ptr
    a0 (output) = 0 ok / 1 parse fail or value length > 32.

    A missing BAL nonce/balance change list leaves that account field unchanged.
    A zero post-value is represented by length 0 from `bal_account_post_fields`
    and is spliced as the canonical RLP integer zero.

    If `baap_force_storage_clear` is nonzero, storage replay starts from
    `EMPTY_TRIE_ROOT` even when the pre-account carries a non-empty storage
    root. This mirrors execution-specs `storage_clears`: pre-existing storage is
    dropped before post-wipe storage writes are applied. -/
def balAccountApplyPostFieldsFunction : String :=
  "bal_account_apply_post_fields:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # original account ptr\n" ++
  "  mv s1, a1                   # original account len\n" ++
  "  mv s2, a2                   # AccountChanges ptr\n" ++
  "  mv s3, a3                   # AccountChanges len\n" ++
  "  mv s4, a4                   # out ptr\n" ++
  "  mv s5, a5                   # out len ptr\n" ++
  "  mv s6, s0                   # current account ptr\n" ++
  "  mv s7, s1                   # current account len\n" ++
  "  la t0, baap_fail_code; sd zero, 0(t0)\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, baap_bal; la a3, baap_bal_len; la a4, baap_nonce; la a5, baap_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  # Apply the final BAL code change first, when present. CodeChanges items are\n" ++
  "  # [blockAccessIndex, newCode]; the account field stores keccak256(newCode).\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 5; la a3, baap_code_list_off; la a4, baap_code_list_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_list_off; ld t0, 0(t0); add t0, s2, t0; la t1, baap_code_list_ptr; sd t0, 0(t1)\n" ++
  "  la t1, baap_code_list_len; ld a1, 0(t1); mv a0, t0; la a2, baap_code_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_count; ld t0, 0(t0); beqz t0, .Lbaap_storage_gate\n" ++
  "  addi a2, t0, -1; la t1, baap_code_list_ptr; ld a0, 0(t1); la t1, baap_code_list_len; ld a1, 0(t1)\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_list_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); la t2, baap_code_item_ptr; sd t0, 0(t2)\n" ++
  "  mv a0, t0; mv a1, t1; li a2, 1; la a3, baap_code_off; la a4, baap_code_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_item_ptr; ld t0, 0(t0); la t1, baap_code_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, baap_code_len; ld a1, 0(t1); la a2, baap_code_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, baap_code_hash; li a1, 32; la a2, aab_enc; la a3, aab_enc_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 3; la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0)\n" ++
  "  la a5, baap_tmp3; la a6, baap_tmp3_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp3; la t0, baap_tmp3_len; ld s7, 0(t0)\n" ++
  ".Lbaap_storage_gate:\n" ++
  "  # Apply one BAL storage change first when present. Storage-only user-tx\n" ++
  "  # writes still affect the post-state account even without balance/nonce\n" ++
  "  # changes; an empty storage_changes list falls through unchanged.\n" ++
  ".Lbaap_try_storage:\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 1; la a3, baap_sc_off; la a4, baap_sc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_off; ld t0, 0(t0); add t0, s2, t0; la t1, baap_sc_ptr; sd t0, 0(t1)\n" ++
  "  la t1, baap_sc_len; ld a1, 0(t1); mv a0, t0; la a2, baap_sc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_count; ld t0, 0(t0); beqz t0, .Lbaap_maybe_clear_only\n" ++
  "  la t1, baap_force_storage_clear; ld t1, 0(t1); bnez t1, .Lbaap_multi_storage\n" ++
  "  li t1, 1; bne t0, t1, .Lbaap_multi_storage\n" ++
  ".Lbaap_one_storage:\n" ++
  "  la t1, baap_sc_ptr; ld a0, 0(t1); la t1, baap_sc_len; ld a1, 0(t1); li a2, 0\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); la t2, baap_code_item_ptr; sd t0, 0(t2)\n" ++
  "  mv a0, t0; mv a1, t1; li a2, 0; la a3, baap_val_off; la a4, baap_val_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_val_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  la t0, baap_slot; li t1, 0\n" ++
  ".Lbaap_slot_zero:\n" ++
  "  li t2, 32; beq t1, t2, .Lbaap_slot_zero_done\n" ++
  "  add t3, t0, t1; sb zero, 0(t3); addi t1, t1, 1; j .Lbaap_slot_zero\n" ++
  ".Lbaap_slot_zero_done:\n" ++
  "  la t0, baap_val_len; ld t1, 0(t0); li t2, 32; sub t2, t2, t1; la t3, baap_slot; add t3, t3, t2\n" ++
  "  la t0, baap_code_item_ptr; ld t0, 0(t0); la t2, baap_val_off; ld t2, 0(t2); add t0, t0, t2\n" ++
  ".Lbaap_slot_cp:\n" ++
  "  beqz t1, .Lbaap_slot_done\n" ++
  "  lbu t2, 0(t0); sb t2, 0(t3); addi t0, t0, 1; addi t3, t3, 1; addi t1, t1, -1; j .Lbaap_slot_cp\n" ++
  ".Lbaap_slot_done:\n" ++
  "  la t0, baap_sc_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); mv a0, t0; mv a1, t1; li a2, 1\n" ++
  "  la a3, baap_slot_changes_off; la a4, baap_slot_changes_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_slot_changes_off; ld t1, 0(t1); add t0, t0, t1; la t2, baap_slot_changes_ptr; sd t0, 0(t2)\n" ++
  "  la t1, baap_slot_changes_len; ld a1, 0(t1); mv a0, t0; la a2, baap_slot_changes_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_slot_changes_count; ld t0, 0(t0); beqz t0, .Lbaap_fail\n" ++
  "  addi a2, t0, -1; la t1, baap_slot_changes_ptr; ld a0, 0(t1); la t1, baap_slot_changes_len; ld a1, 0(t1)\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_slot_changes_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); mv a0, t0; mv a1, t1; li a2, 1; la a3, baap_val_off; la a4, baap_val_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_val_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  beqz t0, .Lbaap_one_storage_delete\n" ++
  "  la t1, baap_slot_changes_ptr; ld t1, 0(t1); la t2, baap_item_off; ld t2, 0(t2); add t1, t1, t2\n" ++
  "  la t2, baap_val_off; ld t2, 0(t2); add a3, t1, t2\n" ++
  "  mv a4, t0\n" ++
  ".Lbaap_one_value_strip_zero:\n" ++
  "  beqz a4, .Lbaap_one_storage_delete\n" ++
  "  lbu t0, 0(a3); bnez t0, .Lbaap_one_value_ready\n" ++
  "  addi a3, a3, 1; addi a4, a4, -1; j .Lbaap_one_value_strip_zero\n" ++
  ".Lbaap_one_value_ready:\n" ++
  "  mv a0, s6; mv a1, s7; la a2, baap_slot; la a5, baap_tmp2; la a6, baap_tmp2_len\n" ++
  "  jal ra, account_apply_storage_slot_acc\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp2; la t0, baap_tmp2_len; ld s7, 0(t0)\n" ++
  "  j .Lbaap_nonce\n" ++
  ".Lbaap_one_storage_delete:\n" ++
  "  mv a0, s6; mv a1, s7; la a2, baap_slot; mv a3, zero; mv a4, zero; la a5, baap_tmp2; la a6, baap_tmp2_len\n" ++
  "  jal ra, account_apply_storage_slot_acc\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp2; la t0, baap_tmp2_len; ld s7, 0(t0)\n" ++
  "  j .Lbaap_nonce\n" ++
  ".Lbaap_multi_storage:\n" ++
  "  # Multi-slot BAL storage replay is supported when the account's prior\n" ++
  "  # storage trie is empty: build all storage insert descriptors and apply\n" ++
  "  # them together so the intermediate trie root need not be in the witness.\n" ++
  "  # Final zero slot values are trie-default no-ops for an empty storage trie.\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 2; la a3, aps_off; la a4, aps_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lbaap_fail\n" ++
  "  la t0, aps_off; ld t1, 0(t0); add t1, s6, t1; la t0, baap_storage_root_ptr; sd t1, 0(t0)\n" ++
  "  la t0, baap_force_storage_clear; ld t0, 0(t0); bnez t0, .Lbaap_force_empty_ok\n" ++
  "  la t2, aps_empty_root; li t3, 32\n" ++
  ".Lbaap_empty_cmp:\n" ++
  "  beqz t3, .Lbaap_empty_ok\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbaap_nonempty_ok\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbaap_empty_cmp\n" ++
  ".Lbaap_empty_ok:\n" ++
  "  li t0, 1; la t1, baap_storage_empty_flag; sd t0, 0(t1)\n" ++
  "  j .Lbaap_multi_init\n" ++
  ".Lbaap_force_empty_ok:\n" ++
  "  li t0, 1; la t1, baap_storage_empty_flag; sd t0, 0(t1)\n" ++
  "  j .Lbaap_multi_init\n" ++
  ".Lbaap_nonempty_ok:\n" ++
  "  la t0, baap_storage_empty_flag; sd zero, 0(t0)\n" ++
  ".Lbaap_multi_init:\n" ++
  "  la t0, baap_storage_values; la t1, baap_storage_value_cursor; sd t0, 0(t1)\n" ++
  "  la t0, baap_sc_index; sd zero, 0(t0)\n" ++
  "  la t0, baap_sc_out_count; sd zero, 0(t0)\n" ++
  "  la t0, baap_storage_delete_flag; sd zero, 0(t0)\n" ++
  "  la t0, baap_storage_delete_count; sd zero, 0(t0)\n" ++
  ".Lbaap_multi_loop:\n" ++
  "  la t0, baap_sc_index; ld t0, 0(t0); la t1, baap_sc_count; ld t1, 0(t1)\n" ++
  "  beq t0, t1, .Lbaap_multi_apply\n" ++
  "  li t2, 60000; bgeu t0, t2, .Lbaap_fail\n" ++
  "  la t1, baap_sc_ptr; ld a0, 0(t1); la t1, baap_sc_len; ld a1, 0(t1); mv a2, t0\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); la t2, baap_code_item_ptr; sd t0, 0(t2)\n" ++
  "  mv a0, t0; mv a1, t1; li a2, 0; la a3, baap_val_off; la a4, baap_val_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_val_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  la t0, baap_slot; li t1, 0\n" ++
  ".Lbaap_mslot_zero:\n" ++
  "  li t2, 32; beq t1, t2, .Lbaap_mslot_zero_done\n" ++
  "  add t3, t0, t1; sb zero, 0(t3); addi t1, t1, 1; j .Lbaap_mslot_zero\n" ++
  ".Lbaap_mslot_zero_done:\n" ++
  "  la t0, baap_val_len; ld t1, 0(t0); li t2, 32; sub t2, t2, t1; la t3, baap_slot; add t3, t3, t2\n" ++
  "  la t0, baap_code_item_ptr; ld t0, 0(t0); la t2, baap_val_off; ld t2, 0(t2); add t0, t0, t2\n" ++
  ".Lbaap_mslot_cp:\n" ++
  "  beqz t1, .Lbaap_mslot_done\n" ++
  "  lbu t2, 0(t0); sb t2, 0(t3); addi t0, t0, 1; addi t3, t3, 1; addi t1, t1, -1; j .Lbaap_mslot_cp\n" ++
  ".Lbaap_mslot_done:\n" ++
  "  la t0, baap_code_item_ptr; ld t0, 0(t0); la t1, baap_item_len; ld t1, 0(t1); mv a0, t0; mv a1, t1; li a2, 1\n" ++
  "  la a3, baap_slot_changes_off; la a4, baap_slot_changes_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_item_ptr; ld t0, 0(t0); la t1, baap_slot_changes_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t2, baap_slot_changes_ptr; sd t0, 0(t2)\n" ++
  "  la t1, baap_slot_changes_len; ld a1, 0(t1); mv a0, t0; la a2, baap_slot_changes_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_slot_changes_count; ld t0, 0(t0); beqz t0, .Lbaap_fail\n" ++
  "  addi a2, t0, -1; la t1, baap_slot_changes_ptr; ld a0, 0(t1); la t1, baap_slot_changes_len; ld a1, 0(t1)\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_slot_changes_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); mv a0, t0; mv a1, t1; li a2, 1; la a3, baap_val_off; la a4, baap_val_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_val_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  la t1, baap_slot_changes_ptr; ld t1, 0(t1); la t2, baap_item_off; ld t2, 0(t2); add t1, t1, t2\n" ++
  "  la t2, baap_val_off; ld t2, 0(t2); add a0, t1, t2\n" ++
  "  mv a1, t0; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, aab_enc_len\n" ++
  ".Lbaap_multi_value_strip_zero:\n" ++
  "  beqz a1, .Lbaap_multi_zero_value\n" ++
  "  lbu t0, 0(a0); bnez t0, .Lbaap_multi_encode_value\n" ++
  "  addi a0, a0, 1; addi a1, a1, -1; j .Lbaap_multi_value_strip_zero\n" ++
  ".Lbaap_multi_zero_value:\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_multi_skip_zero\n" ++
  "  la t0, baap_storage_delete_count; ld t0, 0(t0); li t1, 60000; bgeu t0, t1, .Lbaap_fail\n" ++
  "  li t1, 1; la t2, baap_storage_delete_flag; sd t1, 0(t2)\n" ++
  "  la a0, baap_slot; li a1, 32; la a2, srss_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, baap_storage_delete_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_delete_paths; add a2, t2, t1\n" ++
  "  la a0, srss_key; li a1, 32\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_delete_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  j .Lbaap_multi_skip_zero\n" ++
  ".Lbaap_multi_encode_value:\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_multi_encode_nonzero\n" ++
  ".Lbaap_multi_encode_nonzero:\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la a0, baap_slot; li a1, 32; la a2, srss_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1\n" ++
  "  la a0, srss_key; li a1, 32\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_mslot_insert\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0)\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0)\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a3, t2, t1\n" ++
  "  li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbaap_mslot_modify\n" ++
  "  li t0, 1; bne a0, t0, .Lbaap_fail\n" ++
  ".Lbaap_mslot_insert:\n" ++
  "  li t5, 1; j .Lbaap_mslot_have_mode\n" ++
  ".Lbaap_mslot_modify:\n" ++
  "  li t5, 0\n" ++
  ".Lbaap_mslot_have_mode:\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2\n" ++
  "  la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1)\n" ++
  "  li t2, 64; sd t2, 8(t1)\n" ++
  "  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1)\n" ++
  "  la t4, aab_enc_len; ld t4, 0(t4); sd t4, 24(t1)\n" ++
  "  sd t5, 32(t1)\n" ++
  "  add t3, t3, t4; addi t3, t3, 7; andi t3, t3, -8; sd t3, 0(t2)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)\n" ++
  ".Lbaap_multi_skip_zero:\n" ++
  "  la t0, baap_sc_index; ld t0, 0(t0)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_index; sd t0, 0(t1); j .Lbaap_multi_loop\n" ++
  ".Lbaap_multi_apply:\n" ++
  "  la t0, baap_sc_out_count; ld a4, 0(t0); beqz a4, .Lbaap_multi_no_nonzero\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_multi_apply_empty\n" ++
  "  j .Lbaap_multi_apply_nonempty\n" ++
  ".Lbaap_multi_apply_empty:\n" ++
  "  la a0, aps_empty_root; mv a1, zero; mv a2, zero; la a3, baap_storage_desc\n" ++
  "  j .Lbaap_multi_apply_call\n" ++
  ".Lbaap_multi_apply_nonempty:\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0)\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0); la a3, baap_storage_desc\n" ++
  ".Lbaap_multi_apply_call:\n" ++
  "  la a5, aps_newsroot\n" ++
  "  jal ra, mpt_state_root_ins\n" ++
  "  bnez a0, .Lbaap_fail_storage_apply\n" ++
  "  j .Lbaap_multi_delete_init\n" ++
  ".Lbaap_multi_delete_loop:\n" ++
  "  la t0, baap_storage_delete_index; ld t0, 0(t0); la t1, baap_storage_delete_count; ld t1, 0(t1)\n" ++
  "  beq t0, t1, .Lbaap_multi_set_account\n" ++
  "  la a0, aps_newsroot\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0)\n" ++
  "  la t0, baap_storage_delete_index; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_delete_paths; add a3, t2, t1\n" ++
  "  li a4, 64; la a7, aps_newsroot\n" ++
  "  jal ra, mpt_delete_acc\n" ++
  "  beqz a0, .Lbaap_multi_delete_ok\n" ++
  "  li t0, 1; bne a0, t0, .Lbaap_fail_storage_delete\n" ++
  ".Lbaap_multi_delete_ok:\n" ++
  "  la t0, baap_storage_delete_index; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  j .Lbaap_multi_delete_loop\n" ++
  ".Lbaap_multi_delete_init:\n" ++
  "  la t0, baap_storage_delete_index; sd zero, 0(t0)\n" ++
  "  j .Lbaap_multi_delete_loop\n" ++
  ".Lbaap_multi_set_account:\n" ++
  "  mv a0, s6; mv a1, s7; la a2, aps_newsroot; la a3, baap_tmp2; la a4, baap_tmp2_len\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Lbaap_fail_storage_root\n" ++
  "  la s6, baap_tmp2; la t0, baap_tmp2_len; ld s7, 0(t0)\n" ++
  "  # Apply nonce first if present.\n" ++
  "  j .Lbaap_nonce\n" ++
  ".Lbaap_multi_no_nonzero:\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbaap_maybe_clear_only\n" ++
  "  la t0, baap_storage_delete_count; ld t0, 0(t0); beqz t0, .Lbaap_nonce\n" ++
  "  la t0, baap_storage_root_ptr; ld t0, 0(t0); la t1, aps_newsroot; li t2, 32\n" ++
  ".Lbaap_copy_root_loop:\n" ++
  "  beqz t2, .Lbaap_multi_delete_only_init\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbaap_copy_root_loop\n" ++
  ".Lbaap_multi_delete_only_init:\n" ++
  "  la t0, baap_storage_delete_index; sd zero, 0(t0)\n" ++
  ".Lbaap_multi_delete_only_loop:\n" ++
  "  la t0, baap_storage_delete_index; ld t0, 0(t0); la t1, baap_storage_delete_count; ld t1, 0(t1)\n" ++
  "  beq t0, t1, .Lbaap_multi_set_account\n" ++
  "  la a0, aps_newsroot\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0); la t0, aps_witness_len; ld a2, 0(t0)\n" ++
  "  la t0, baap_storage_delete_index; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_delete_paths; add a3, t2, t1\n" ++
  "  li a4, 64; la a7, aps_newsroot\n" ++
  "  jal ra, mpt_delete_acc\n" ++
  "  beqz a0, .Lbaap_multi_delete_only_ok\n" ++
  "  li t0, 1; bne a0, t0, .Lbaap_fail_storage_delete_only\n" ++
  ".Lbaap_multi_delete_only_ok:\n" ++
  "  la t0, baap_storage_delete_index; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)\n" ++
  "  j .Lbaap_multi_delete_only_loop\n" ++
  ".Lbaap_maybe_clear_only:\n" ++
  "  la t0, baap_force_storage_clear; ld t0, 0(t0); beqz t0, .Lbaap_nonce\n" ++
  "  mv a0, s6; mv a1, s7; la a2, aps_empty_root; la a3, baap_tmp2; la a4, baap_tmp2_len\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Lbaap_fail_storage_root\n" ++
  "  la s6, baap_tmp2; la t0, baap_tmp2_len; ld s7, 0(t0)\n" ++
  ".Lbaap_nonce:\n" ++
  "  la t0, baap_nonce_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbaap_balance\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 0\n" ++
  "  la a3, baap_nonce; mv a4, t0; la a5, baap_tmp; la a6, baap_tmp_len\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbaap_fail_nonce\n" ++
  "  la s6, baap_tmp; la t0, baap_tmp_len; ld s7, 0(t0)\n" ++
  ".Lbaap_balance:\n" ++
  "  # Apply balance if present; otherwise copy the current account to the final output.\n" ++
  "  la t0, baap_bal_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbaap_copy_current\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 1\n" ++
  "  la a3, baap_bal; mv a4, t0; mv a5, s4; mv a6, s5\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbaap_fail_balance\n" ++
  "  j .Lbaap_ret\n" ++
  ".Lbaap_copy_current:\n" ++
  "  mv a0, s4; mv a1, s6; mv a2, s7\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  sd s7, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbaap_ret\n" ++
  ".Lbaap_fail_storage_apply:\n" ++
  "  li t0, 501; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_storage_delete:\n" ++
  "  li t0, 502; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_storage_root:\n" ++
  "  li t0, 503; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_storage_delete_only:\n" ++
  "  li t0, 504; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_nonce:\n" ++
  "  li t0, 505; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail_balance:\n" ++
  "  li t0, 506; la t1, baap_fail_code; sd t0, 0(t1); j .Lbaap_fail\n" ++
  ".Lbaap_fail:\n" ++
  "  la t1, baap_fail_code; ld t0, 0(t1); bnez t0, .Lbaap_fail_have_code\n" ++
  "  li t0, 599; sd t0, 0(t1)\n" ++
  ".Lbaap_fail_have_code:\n" ++
  "  li a0, 1\n" ++
  ".Lbaap_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_bal_account_apply_post_fields`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account RLP length (u64)
      +16 AccountChanges RLP length (u64)
      +24 account RLP bytes, padded to 8 bytes
      then AccountChanges RLP bytes
    Output layout:
      OUTPUT+0   : new account RLP length
      OUTPUT+8   : new account RLP bytes
      OUTPUT+240 : internal fail code (0 on success)
      OUTPUT+248 : status -/
def ziskBalAccountApplyPostFieldsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a3, 16(t0)               # AccountChanges len\n" ++
  "  addi a0, t0, 24             # account ptr\n" ++
  "  add a2, a0, a1              # AccountChanges ptr after padded account\n" ++
  "  addi a2, a2, 7; andi a2, a2, -8\n" ++
  "  li a4, 0xa0010008           # out account bytes at OUTPUT+8\n" ++
  "  li a5, 0xa0010000           # out account length at OUTPUT+0\n" ++
  "  jal ra, bal_account_apply_post_fields\n" ++
  "  la t1, baap_fail_code; ld t2, 0(t1); li t0, 0xa00100f0; sd t2, 0(t0)   # fail_code at OUTPUT+240\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)   # status at OUTPUT+248\n" ++
  "  j .Lbaap_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  accountApplyStorageSlotAccFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  ".Lbaap_pdone:"

def ziskBalAccountApplyPostFieldsDataSection : String :=
  ziskMptStateRootInsDataSection ++ "\n" ++
  ziskBalAccountPostFieldsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "aab_bal_off:\n  .zero 8\n" ++
  "aab_bal_len:\n  .zero 8\n" ++
  "aab_enc_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aab_bal32:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_enc:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "sltr_field_len:\n  .zero 8\n" ++
  "sltr_nibble_count:\n  .zero 8\n" ++
  "sltr_hp_len:\n  .zero 8\n" ++
  "sltr_cursor:\n  .zero 8\n" ++
  "sltr_total_payload:\n  .zero 8\n" ++
  "sltr_nibbles:\n  .zero 2048\n" ++
  "sltr_hp_buf:\n  .zero 1024\n" ++
  "sltr_payload_buf:\n  .zero 16384\n" ++
  "sltr_node_buf:\n  .zero 16384\n" ++
  ".balign 32\n" ++
  "srss_key:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "srss_rlpval:\n  .zero 40\n" ++
  "srss_rlpval_len:\n  .zero 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  "aps_witness_ptr:\n  .zero 8\n" ++
  "aps_witness_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aps_newsroot:\n  .zero 32\n" ++
  "aps_path:\n  .zero 64\n" ++
  "aps_empty_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 8\n" ++
  "baap_bal_len:\n  .zero 8\n" ++
  "baap_nonce_len:\n  .zero 8\n" ++
  "baap_tmp_len:\n  .zero 8\n" ++
  "baap_tmp2_len:\n  .zero 8\n" ++
  "baap_fail_code:\n  .zero 8\n" ++
  "baap_sc_off:\n  .zero 8\n" ++
  "baap_sc_len:\n  .zero 8\n" ++
  "baap_sc_ptr:\n  .zero 8\n" ++
  "baap_sc_count:\n  .zero 8\n" ++
  "baap_sc_index:\n  .zero 8\n" ++
  "baap_sc_out_count:\n  .zero 8\n" ++
  "baap_storage_empty_flag:\n  .zero 8\n" ++
  "baap_force_storage_clear:\n  .zero 8\n" ++
  "baap_storage_delete_flag:\n  .zero 8\n" ++
  "baap_storage_delete_count:\n  .zero 8\n" ++
  "baap_storage_delete_index:\n  .zero 8\n" ++
  "baap_storage_root_ptr:\n  .zero 8\n" ++
  "baap_walk_val_len:\n  .zero 8\n" ++
  "baap_item_off:\n  .zero 8\n" ++
  "baap_item_len:\n  .zero 8\n" ++
  "baap_slot_changes_off:\n  .zero 8\n" ++
  "baap_slot_changes_len:\n  .zero 8\n" ++
  "baap_slot_changes_ptr:\n  .zero 8\n" ++
  "baap_slot_changes_count:\n  .zero 8\n" ++
  "baap_val_off:\n  .zero 8\n" ++
  "baap_val_len:\n  .zero 8\n" ++
  "baap_code_list_off:\n  .zero 8\n" ++
  "baap_code_list_len:\n  .zero 8\n" ++
  "baap_code_list_ptr:\n  .zero 8\n" ++
  "baap_code_count:\n  .zero 8\n" ++
  "baap_code_item_ptr:\n  .zero 8\n" ++
  "baap_code_off:\n  .zero 8\n" ++
  "baap_code_len:\n  .zero 8\n" ++
  "baap_tmp3_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "baap_bal:\n  .zero 32\n" ++
  "baap_nonce:\n  .zero 32\n" ++
  "baap_slot:\n  .zero 32\n" ++
  "baap_code_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "baap_tmp2:\n  .zero 512\n" ++
  "baap_tmp3:\n  .zero 512\n" ++
  "baap_storage_value_cursor:\n  .zero 8\n" ++
  "baap_walk_val:\n  .zero 128\n" ++
  "baap_storage_desc:\n  .zero 2400000\n" ++
  "baap_storage_paths:\n  .zero 3840000\n" ++
  "baap_storage_delete_paths:\n  .zero 3840000\n" ++
  "baap_storage_values:\n  .zero 3840000\n" ++
  "baap_out_pad:\n  .zero 8"

def ziskBalAccountApplyPostFieldsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountApplyPostFieldsPrologue
  dataAsm     := ziskBalAccountApplyPostFieldsDataSection
}

end EvmAsm.Codegen
