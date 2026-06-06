/-
  EvmAsm.Codegen.Programs.BalAccountDescriptorArray

  Build an `mpt_state_root_ins` descriptor array from a BAL AccountChanges list
  and caller-supplied pre-account records. This is the list-level adapter above
  the per-item BAL descriptor helpers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalAccountChangeDescriptor

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_descriptor_array -- BAL list -> descriptor array

    a0 = BAL AccountChanges list ptr   a1 = BAL AccountChanges list length
    a2 = account records ptr           a3 = n records/items
    a4 = descriptors out ptr           a5 = path arena out ptr
    a6 = value arena out ptr
    a0 (output) = 0 ok / 1 failure.

    Account record layout is 24 bytes per selected BAL item:
      +0 account_ptr | +8 account_len | +16 is_insert.
    An is_insert value of 3 marks a read-only BAL row already classified by
    `bal_account_record_array`; the descriptor pass emits a no-op descriptor
    without parsing that BAL item again.

    Descriptor layout matches `mpt_state_root_ins`, 40 bytes per item. Paths are
    written densely as 64-byte nibble arrays. Values are written densely in the
    value arena, each rounded up to an 8-byte boundary before the next value. -/
def balAccountDescriptorArrayFunction : String :=
  "bal_account_descriptor_array:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # BAL list ptr\n" ++
  "  mv s1, a1                   # BAL list len\n" ++
  "  mv s2, a2                   # account records\n" ++
  "  mv s3, a3                   # n\n" ++
  "  mv s4, a4                   # descriptor cursor\n" ++
  "  mv s5, a5                   # path cursor\n" ++
  "  mv s6, a6                   # value cursor\n" ++
  "  la t0, baada_fail_code; sd zero, 0(t0)\n" ++
  "  la t0, baada_fail_index; sd zero, 0(t0)\n" ++
  "  li s7, 0                    # i\n" ++
  ".Lbaada_loop:\n" ++
  "  beq s7, s3, .Lbaada_ok\n" ++
  "  slli t0, s7, 4; slli t1, s7, 3; add t0, t0, t1; add t0, s2, t0\n" ++
  "  ld a0, 0(t0)                # account ptr\n" ++
  "  ld a1, 8(t0)                # account len\n" ++
  "  ld a4, 16(t0)               # is_insert\n" ++
  "  mv s8, t0                   # record ptr, preserved across classifier\n" ++
  "  li t1, 3; beq a4, t1, .Lbaada_readonly\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s7\n" ++
  "  la a3, baada_item_off; la a4, baada_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaada_fail_nth\n" ++
  "  la t1, baada_item_off; ld t1, 0(t1); add a2, s0, t1\n" ++
  "  la t1, baada_item_len; ld a3, 0(t1)\n" ++
  "  mv a0, a2; mv a1, a3; jal ra, bal_account_has_state_change\n" ++
  "  li t1, 1; beq a0, t1, .Lbaada_changed\n" ++
  "  bnez a0, .Lbaada_fail_desc\n" ++
  "  ld t1, 0(s8); sd s5, 0(s4); li t2, 64; sd t2, 8(s4); sd t1, 16(s4)\n" ++
  "  ld t1, 8(s8); sd t1, 24(s4); li t2, 3; sd t2, 32(s4); j .Lbaada_desc_done\n" ++
  ".Lbaada_readonly:\n" ++
  "  ld t1, 0(s8); sd s5, 0(s4); li t2, 64; sd t2, 8(s4); sd t1, 16(s4)\n" ++
  "  ld t1, 8(s8); sd t1, 24(s4); li t2, 3; sd t2, 32(s4); j .Lbaada_desc_done\n" ++
  ".Lbaada_changed:\n" ++
  "  ld a0, 0(s8); ld a1, 8(s8); ld a4, 16(s8)\n" ++
  "  la t1, baada_item_off; ld t1, 0(t1); add a2, s0, t1\n" ++
  "  la t1, baada_item_len; ld a3, 0(t1)\n" ++
  "  mv a5, s4; mv a6, s5; mv a7, s6\n" ++
  "  jal ra, bal_account_change_descriptor\n" ++
  "  bnez a0, .Lbaada_fail_desc\n" ++
  ".Lbaada_desc_done:\n" ++
  "  ld s8, 24(s4)               # value length from descriptor\n" ++
  "  addi s4, s4, 40\n" ++
  "  addi s5, s5, 64\n" ++
  "  add s6, s6, s8; addi s6, s6, 7; andi s6, s6, -8\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lbaada_loop\n" ++
  ".Lbaada_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbaada_ret\n" ++
  ".Lbaada_fail_nth:\n" ++
  "  li t0, 201; la t1, baada_fail_code; sd t0, 0(t1); la t1, baada_fail_index; sd s7, 0(t1)\n" ++
  "  j .Lbaada_ret\n" ++
  ".Lbaada_fail_desc:\n" ++
  "  li t0, 202; la t1, baada_fail_code; sd t0, 0(t1); la t1, baada_fail_index; sd s7, 0(t1)\n" ++
  ".Lbaada_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-! ## bal_account_final_descriptor_array -- keep final non-noop descriptor per path

    a0 = BAL AccountChanges list ptr   a1 = BAL AccountChanges list length
    a2 = account records ptr           a3 = n records/items
    a4 = final descriptors out ptr     a5 = final path arena out ptr
    a6 = final value arena out ptr     a7 = out_count ptr
    a0 (output) = 0 ok / 1 failure.

    This adapter reuses `bal_account_descriptor_array` for parsing and account
    value construction, then compacts its output by skipping no-op descriptors
    and keeping only the last non-noop descriptor for each 64-nibble account
    path. Later post-state-root slices can feed the compact table directly into
    `mpt_state_root_ins`. -/
def balAccountFinalDescriptorArrayFunction : String :=
  "bal_account_final_descriptor_array:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # BAL list ptr\n" ++
  "  mv s1, a1                   # BAL list len\n" ++
  "  mv s2, a2                   # account records\n" ++
  "  mv s3, a3                   # n\n" ++
  "  mv s4, a4                   # final descriptor base\n" ++
  "  mv s5, a5                   # final path cursor\n" ++
  "  mv s6, a6                   # final value cursor\n" ++
  "  mv s7, a7                   # out_count ptr\n" ++
  "  la a4, badf_tmp_desc; la a5, badf_tmp_paths; la a6, badf_tmp_values\n" ++
  "  jal ra, bal_account_descriptor_array\n" ++
  "  bnez a0, .Lbadf_ret\n" ++
  "  sd zero, 0(s7)\n" ++
  "  li s8, 0                    # input index\n" ++
  "  li s9, 0                    # output count\n" ++
  ".Lbadf_loop:\n" ++
  "  beq s8, s3, .Lbadf_done\n" ++
  "  slli t0, s8, 5; slli t1, s8, 3; add t0, t0, t1; la t1, badf_tmp_desc; add s10, t1, t0\n" ++
  "  ld t0, 32(s10); li t1, 3; beq t0, t1, .Lbadf_next\n" ++
  "  la t1, badf_cur_mode; sd t0, 0(t1)\n" ++
  "  ld t0, 0(s10); la t1, badf_cur_path; sd t0, 0(t1)\n" ++
  "  ld t0, 16(s10); la t1, badf_cur_value; sd t0, 0(t1)\n" ++
  "  ld t0, 24(s10); la t1, badf_cur_vlen; sd t0, 0(t1)\n" ++
  "  addi s11, s8, 1             # scan later rows for same path\n" ++
  ".Lbadf_dup_scan:\n" ++
  "  beq s11, s3, .Lbadf_keep\n" ++
  "  slli t0, s11, 5; slli t1, s11, 3; add t0, t0, t1; la t1, badf_tmp_desc; add t0, t1, t0\n" ++
  "  ld t1, 32(t0); li t2, 3; beq t1, t2, .Lbadf_dup_next\n" ++
  "  ld t2, 0(t0)                # later path ptr\n" ++
  "  la t3, badf_cur_path; ld t3, 0(t3)\n" ++
  "  li t4, 64\n" ++
  ".Lbadf_path_cmp:\n" ++
  "  beqz t4, .Lbadf_next        # later same-path row wins\n" ++
  "  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lbadf_dup_next\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1\n" ++
  "  j .Lbadf_path_cmp\n" ++
  ".Lbadf_dup_next:\n" ++
  "  addi s11, s11, 1; j .Lbadf_dup_scan\n" ++
  ".Lbadf_keep:\n" ++
  "  la t0, badf_cur_path; ld a1, 0(t0); mv a0, s5; li a2, 64\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  la t0, badf_cur_value; ld a1, 0(t0); la t0, badf_cur_vlen; ld a2, 0(t0); mv a0, s6\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  slli t0, s9, 5; slli t1, s9, 3; add t0, t0, t1; add t0, s4, t0\n" ++
  "  sd s5, 0(t0); li t1, 64; sd t1, 8(t0); sd s6, 16(t0)\n" ++
  "  la t1, badf_cur_vlen; ld t2, 0(t1); sd t2, 24(t0)\n" ++
  "  la t1, badf_cur_mode; ld t2, 0(t1); sd t2, 32(t0)\n" ++
  "  addi s5, s5, 64\n" ++
  "  la t1, badf_cur_vlen; ld t2, 0(t1); add s6, s6, t2; addi s6, s6, 7; andi s6, s6, -8\n" ++
  "  addi s9, s9, 1; sd s9, 0(s7)\n" ++
  ".Lbadf_next:\n" ++
  "  addi s8, s8, 1; j .Lbadf_loop\n" ++
  ".Lbadf_done:\n" ++
  "  li a0, 0\n" ++
  ".Lbadf_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

def balAccountDescriptorArrayDeps : String :=
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
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
  accountIsEip161EmptyFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountDescriptorArrayFunction

/-- `zisk_bal_account_descriptor_array`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  BAL list length (u64)
      +16 n (u64)
      +24 table: n x (account_len:u64, is_insert:u64)
      then account RLP blobs, each padded to 8 bytes
      then BAL AccountChanges list bytes
    Output layout:
      OUTPUT+0   : status
      OUTPUT+8   : descriptor array
      OUTPUT+88  : path arena (for two probe rows)
      OUTPUT+216 : value arena (for compact probe accounts)
      OUTPUT+248 : duplicate status -/
def ziskBalAccountDescriptorArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # BAL list len\n" ++
  "  ld a3, 16(t0)               # n\n" ++
  "  addi t1, t0, 24             # input table\n" ++
  "  slli t2, a3, 4; add t3, t1, t2   # blob cursor after 16*n table\n" ++
  "  la t4, baada_records        # record table out\n" ++
  "  li t5, 0\n" ++
  ".Lbaadap_records:\n" ++
  "  beq t5, a3, .Lbaadap_records_done\n" ++
  "  slli t6, t5, 4; add t6, t1, t6\n" ++
  "  ld a4, 0(t6)                # account len\n" ++
  "  ld a5, 8(t6)                # is_insert\n" ++
  "  slli t6, t5, 4; slli a6, t5, 3; add t6, t6, a6; add t6, t4, t6\n" ++
  "  sd t3, 0(t6); sd a4, 8(t6); sd a5, 16(t6)\n" ++
  "  add t3, t3, a4; addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Lbaadap_records\n" ++
  ".Lbaadap_records_done:\n" ++
  "  mv a0, t3                   # BAL list ptr\n" ++
  "  la a2, baada_records\n" ++
  "  li a4, 0xa0010008           # descriptors\n" ++
  "  li a5, 0xa0010058           # paths\n" ++
  "  li a6, 0xa00100d8           # values\n" ++
  "  jal ra, bal_account_descriptor_array\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)\n" ++
  "  j .Lbaada_pdone\n" ++
  balAccountDescriptorArrayDeps ++ "\n" ++
  balAccountHasStateChangeFunction ++ "\n" ++
  ".Lbaada_pdone:"

def ziskBalAccountDescriptorArrayDataSection : String :=
  ziskMptStateRootInsDataSection ++ "\n" ++
  ziskBalAccountHasStateChangeDataSection ++ "\n" ++
  ".balign 8\n" ++
  "aab_bal_off:\n  .zero 8\n" ++
  "aab_bal_len:\n  .zero 8\n" ++
  "aab_enc_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aab_bal32:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_enc:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
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
  "baap_storage_desc:\n  .zero 20480\n" ++
  "baap_storage_paths:\n  .zero 32768\n" ++
  "baap_storage_delete_paths:\n  .zero 32768\n" ++
  "baap_storage_values:\n  .zero 32768\n" ++
  "bacp_off:\n  .zero 8\n" ++
  "bacp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  "baacd_value_len:\n  .zero 8\n" ++
  "baacd_is_empty:\n  .zero 8\n" ++
  "baacd_fail_code:\n  .zero 8\n" ++
  "aie_offset:\n  .zero 8\n" ++
  "aie_length:\n  .zero 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  "bacv_fail_code:\n  .zero 8\n" ++
  "baada_item_off:\n  .zero 8\n" ++
  "baada_item_len:\n  .zero 8\n" ++
  "baada_fail_code:\n  .zero 8\n" ++
  "baada_fail_index:\n  .zero 8\n" ++
  "baada_records:\n  .zero 768\n" ++
  "badf_cur_path:\n  .zero 8\n" ++
  "badf_cur_value:\n  .zero 8\n" ++
  "badf_cur_vlen:\n  .zero 8\n" ++
  "badf_cur_mode:\n  .zero 8\n" ++
  "badf_tmp_desc:\n  .zero 4096\n" ++
  "badf_tmp_paths:\n  .zero 8192\n" ++
  "badf_tmp_values:\n  .zero 32768\n" ++
  "baada_pad:\n  .zero 8"

def ziskBalAccountDescriptorArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountDescriptorArrayPrologue
  dataAsm     := ziskBalAccountDescriptorArrayDataSection
}

/-- `zisk_bal_account_final_descriptor_array`: compact descriptor probe.
    Input layout matches `zisk_bal_account_descriptor_array`.
    Output layout:
      OUTPUT+0   : status
      OUTPUT+8   : final descriptor count
      OUTPUT+16  : final descriptor array
      OUTPUT+96  : final path arena
      OUTPUT+224 : final value arena. -/
def ziskBalAccountFinalDescriptorArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # BAL list len\n" ++
  "  ld a3, 16(t0)               # n\n" ++
  "  addi t1, t0, 24             # input table\n" ++
  "  slli t2, a3, 4; add t3, t1, t2   # blob cursor after 16*n table\n" ++
  "  la t4, baada_records        # record table out\n" ++
  "  li t5, 0\n" ++
  ".Lbadfp_records:\n" ++
  "  beq t5, a3, .Lbadfp_records_done\n" ++
  "  slli t6, t5, 4; add t6, t1, t6\n" ++
  "  ld a4, 0(t6)                # account len\n" ++
  "  ld a5, 8(t6)                # is_insert\n" ++
  "  slli t6, t5, 4; slli a6, t5, 3; add t6, t6, a6; add t6, t4, t6\n" ++
  "  sd t3, 0(t6); sd a4, 8(t6); sd a5, 16(t6)\n" ++
  "  add t3, t3, a4; addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Lbadfp_records\n" ++
  ".Lbadfp_records_done:\n" ++
  "  mv a0, t3                   # BAL list ptr\n" ++
  "  la a2, baada_records\n" ++
  "  li a4, 0xa0010010           # final descriptors\n" ++
  "  li a5, 0xa0010060           # final paths\n" ++
  "  li a6, 0xa00100e0           # final values\n" ++
  "  li a7, 0xa0010008           # final count\n" ++
  "  jal ra, bal_account_final_descriptor_array\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lbadf_pdone\n" ++
  balAccountDescriptorArrayDeps ++ "\n" ++
  balAccountHasStateChangeFunction ++ "\n" ++
  balAccountFinalDescriptorArrayFunction ++ "\n" ++
  ".Lbadf_pdone:"

def ziskBalAccountFinalDescriptorArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountFinalDescriptorArrayPrologue
  dataAsm     := ziskBalAccountDescriptorArrayDataSection
}

end EvmAsm.Codegen
