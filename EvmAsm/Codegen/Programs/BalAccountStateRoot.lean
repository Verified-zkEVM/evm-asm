/-
  EvmAsm.Codegen.Programs.BalAccountStateRoot

  Bridge BAL account descriptor preparation into `mpt_state_root_ins`: given a
  pre-state root/witness, a BAL AccountChanges list, and caller-supplied
  pre-account records, recompute the post state root for those account changes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalAccountDescriptorArray
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.BalAccountRecordArray
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.MptDeleteAcc

import EvmAsm.Codegen.Programs.MptEncodeLeafBranch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_state_root -- BAL descriptors + mpt_state_root_ins

    a0 = root_hash ptr        a1 = witness ptr       a2 = witness length
    a3 = BAL list ptr         a4 = BAL list length   a5 = account records ptr
    a6 = n records/items      a7 = out root ptr
    a0 (output) = 0 ok / nonzero failure.

    Account records use `bal_account_descriptor_array`'s 24-byte layout:
      +0 account_ptr | +8 account_len | +16 is_insert. -/
def balAccountStateRootFunction : String :=
  "bal_account_state_root:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # root hash ptr\n" ++
  "  mv s1, a1                   # witness ptr\n" ++
  "  mv s2, a2                   # witness len\n" ++
  "  mv s3, a5                   # account records\n" ++
  "  mv s4, a6                   # n\n" ++
  "  mv s5, a7                   # out root\n" ++
  "  la t0, aps_witness_ptr; sd s1, 0(t0); la t0, aps_witness_len; sd s2, 0(t0)\n" ++
  "  mv a0, a3; mv a1, a4; mv a2, s3; mv a3, s4\n" ++
  "  la a4, basr_desc; la a5, basr_paths; la a6, basr_values\n" ++
  "  jal ra, bal_account_descriptor_array\n" ++
  "  bnez a0, .Lbasr_ret\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; la a3, basr_desc; mv a4, s4; mv a5, s5\n" ++
  "  jal ra, mpt_state_root_ins\n" ++
  ".Lbasr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-! ## bal_account_state_root_auto -- derive records + replay BAL account changes

    a0 = root_hash ptr        a1 = witness ptr       a2 = witness length
    a3 = BAL list ptr         a4 = BAL list length   a5 = n records/items
    a6 = out root ptr         a0 (output) = 0 ok / nonzero failure. -/
def balAccountStateRootAutoFunction : String :=
  "bal_account_state_root_auto:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # root hash ptr\n" ++
  "  mv s1, a1                   # witness ptr\n" ++
  "  mv s2, a2                   # witness len\n" ++
  "  mv s3, a3                   # BAL list ptr\n" ++
  "  mv s4, a4                   # BAL list len\n" ++
  "  mv s5, a5                   # n\n" ++
  "  mv s6, a6                   # out root\n" ++
  "  la t0, aps_witness_ptr; sd s1, 0(t0); la t0, aps_witness_len; sd s2, 0(t0)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4; mv a5, s5\n" ++
  "  la a6, basr_records; la a7, basr_accounts\n" ++
  "  jal ra, bal_account_record_array\n" ++
  "  bnez a0, .Lbasra_ret\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3; mv a4, s4\n" ++
  "  la a5, basr_records; mv a6, s5; mv a7, s6\n" ++
  "  jal ra, bal_account_state_root\n" ++
  ".Lbasra_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_bal_account_state_root`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness length (u64)
      +16 n (u64)
      +24 BAL list length (u64)
      +32 root hash (32 bytes)
      +64 table: n x (account_len:u64, is_insert:u64)
      then account RLP blobs, each padded to 8 bytes
      then BAL AccountChanges list bytes, padded to 8 bytes
      then witness section
    Output: OUTPUT+0 = final root, OUTPUT+32 = status. -/
def ziskBalAccountStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness len\n" ++
  "  ld a6, 16(t0)               # n\n" ++
  "  ld a4, 24(t0)               # BAL list len\n" ++
  "  addi a0, t0, 32             # root hash ptr\n" ++
  "  addi t1, t0, 64             # input table\n" ++
  "  slli t2, a6, 4; add t3, t1, t2   # account blob cursor\n" ++
  "  la a5, basr_records         # account records out\n" ++
  "  li t4, 0\n" ++
  ".Lbasrp_records:\n" ++
  "  beq t4, a6, .Lbasrp_records_done\n" ++
  "  slli t5, t4, 4; add t5, t1, t5\n" ++
  "  ld s6, 0(t5)                # account len\n" ++
  "  ld s7, 8(t5)                # is_insert\n" ++
  "  slli t5, t4, 4; slli t6, t4, 3; add t5, t5, t6; add t5, a5, t5\n" ++
  "  sd t3, 0(t5); sd s6, 8(t5); sd s7, 16(t5)\n" ++
  "  add t3, t3, s6; addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  addi t4, t4, 1\n" ++
  "  j .Lbasrp_records\n" ++
  ".Lbasrp_records_done:\n" ++
  "  mv a3, t3                   # BAL list ptr\n" ++
  "  add t3, t3, a4; addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  mv a1, t3                   # witness ptr\n" ++
  "  li a7, 0xa0010000           # out root\n" ++
  "  jal ra, bal_account_state_root\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Lbasr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  accountApplyStorageSlotAccFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  mptExtensionExtractFunction ++ "\n" ++
  mptDeleteAccFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  accountIsEip161EmptyFunction ++ "\n" ++
  balAccountHasStateChangeFunction ++ "\n" ++
  balAccountIsModeledSystemFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  baapDeleteSingleLeafStorageFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountDescriptorArrayFunction ++ "\n" ++
  balAccountRecordArrayFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  balAccountStateRootFunction ++ "\n" ++
  balAccountStateRootAutoFunction ++ "\n" ++
  ".Lbasr_pdone:"

/-- Data section combines the MPT state-root driver scratch with only the
    BAL/account-rewrite labels that are not already provided by MPT scratch. -/
def ziskBalAccountStateRootDataSection : String :=
  ziskMptStateRootInsDataSection ++ "\n" ++
  ".balign 8\n" ++
  ziskBalAccountHasStateChangeDataSection ++
  "aab_enc_len:\n  .zero 8\n" ++
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
  ".balign 8\n" ++
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
  "basr_records:\n  .zero 98304\n" ++    -- 4096 * 24
  "basr_desc:\n  .zero 163840\n" ++     -- 4096 * 40
  "basr_paths:\n  .zero 262144\n" ++     -- 4096 * 64
  "basr_values:\n  .zero 1048576\n" ++   -- 4096 * 256
  "basr_accounts:\n  .zero 1048576\n" ++ -- 4096 * 256
  ziskBalAccountIsModeledSystemDataSection ++ "\n" ++
  "bara_item_off:\n  .zero 8\n" ++
  "bara_item_len:\n  .zero 8\n" ++
  "bara_acct_len:\n  .zero 8\n" ++
  "bara_bal_end:\n  .zero 8\n" ++
  "bara_next_item:\n  .zero 8\n" ++
  "bara_skip_modeled_system:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bara_path:\n  .zero 64\n" ++
  "bara_acct:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bara_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  "basr_pad:\n  .zero 8"

def ziskBalAccountStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountStateRootPrologue
  dataAsm     := ziskBalAccountStateRootDataSection
}

/-- `zisk_bal_account_state_root_auto`: same as `bal_account_state_root`, but
    derives account records from the pre-state witness instead of reading them
    from the input.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness length (u64)
      +16 n (u64)
      +24 BAL list length (u64)
      +32 root hash (32 bytes)
      +64 BAL AccountChanges list bytes, padded to 8 bytes
      then witness section
    Output: OUTPUT+0 = final root, OUTPUT+32 = status. -/
def ziskBalAccountStateRootAutoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness len\n" ++
  "  ld a5, 16(t0)               # n\n" ++
  "  ld a4, 24(t0)               # BAL list len\n" ++
  "  addi a0, t0, 32             # root hash ptr\n" ++
  "  addi a3, t0, 64             # BAL list ptr\n" ++
  "  add t1, a3, a4; addi t1, t1, 7; andi t1, t1, -8\n" ++
  "  mv a1, t1                   # witness ptr\n" ++
  "  li a6, 0xa0010000           # out root\n" ++
  "  jal ra, bal_account_state_root_auto\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Lbasra_pdone\n" ++
  ziskBalAccountStateRootPrologue ++ "\n" ++
  ".Lbasra_pdone:"

def ziskBalAccountStateRootAutoProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountStateRootAutoPrologue
  dataAsm     := ziskBalAccountStateRootDataSection
}

end EvmAsm.Codegen
