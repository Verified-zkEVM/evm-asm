/-
  EvmAsm.Codegen.Programs.BlockVerdictSysChange

  Assembly helpers for recording system-contract storage-write changes in
  the block state root computation: bsr_sys_change and bsr_beacon_change.
  Carved out of BlockVerdict.lean to stay within the 1500-line file-size cap.
-/

namespace EvmAsm.Codegen

/-! ## bsr_sys_change -- record one system-contract storage-write change.
    a0 = contract addr ptr (20 B)   a1 = slot_key ptr (32 B)
    a2 = value ptr   a3 = value len   a4 = change index
    Reads shared state from bsr_root_p / bsr_wit_p / bsr_wl_v; writes the change
    entry at bsr_changes[index]. a0 (output) = 0 ok / 1 conservative. -/
def bsrSysChangeFunction : String :=
  "bsr_sys_change:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  # keccak(addr, 20) -> bsr_kbuf\n" ++
  "  mv a0, s0; li a1, 20; la a2, bsr_kbuf; jal ra, zkvm_keccak256\n" ++
  "  # path = bsr_paths + 64*index; bytes_to_nibbles(bsr_kbuf, 32, path)\n" ++
  "  slli t0, s4, 6; la t1, bsr_paths; add t2, t1, t0\n" ++
  "  la t3, bsr_pathp; sd t2, 0(t3)              # stash path ptr\n" ++
  "  la a0, bsr_kbuf; li a1, 32; mv a2, t2; jal ra, bytes_to_nibbles\n" ++
  "  # mpt_walk(root, witness, wlen, path, 64, bsr_acct, bsr_acct_len)\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, bsr_pathp; ld a3, 0(t0); li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  bnez a0, .Lbsc_fail\n" ++
  "  # account_apply_storage_slot_acc(acct, len, slot, val, vlen, newacct, bsr_tmplen)\n" ++
  "  # The accumulator helper replays non-empty system-contract storage roots.\n" ++
  "  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); mv a2, s1; mv a3, s2; mv a4, s3\n" ++
  "  slli t0, s4, 7; la t1, bsr_newaccts; add a5, t1, t0; la a6, bsr_tmplen\n" ++
  "  jal ra, account_apply_storage_slot_acc\n" ++
  "  bnez a0, .Lbsc_fail\n" ++
  "  # record change[index] = (path, 64, newacct, tmplen, is_insert=0) -- 40 B\n" ++
  "  slli t0, s4, 5; slli t4, s4, 3; add t0, t0, t4; la t1, bsr_changes; add t1, t1, t0\n" ++
  "  la t2, bsr_pathp; ld t2, 0(t2); sd t2, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  slli t0, s4, 7; la t2, bsr_newaccts; add t2, t2, t0; sd t2, 16(t1)\n" ++
  "  la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1)\n" ++
  "  sd zero, 32(t1)             # is_insert = 0 (system contract MODIFY)\n" ++
  "  li a0, 0; j .Lbsc_ret\n" ++
  ".Lbsc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-! ## bsr_beacon_change -- record the EIP-4788 two-slot account change.
    EIP-4788 writes two storage slots in the same beacon-roots account.  The
    state trie must therefore receive one account-leaf descriptor whose
    storageRoot reflects both slot writes, not two duplicate state descriptors.
    a4 = change index. -/
def bsrBeaconChangeFunction : String :=
  "bsr_beacon_change:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a4                   # state change index\n" ++
  "  la a0, bsr_addr_4788; li a1, 20; la a2, bsr_kbuf; jal ra, zkvm_keccak256\n" ++
  "  slli t0, s0, 6; la t1, bsr_paths; add t2, t1, t0\n" ++
  "  la t3, bsr_pathp; sd t2, 0(t3)\n" ++
  "  la a0, bsr_kbuf; li a1, 32; mv a2, t2; jal ra, bytes_to_nibbles\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, bsr_pathp; ld a3, 0(t0); li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len\n" ++
  "  jal ra, mpt_walk\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); li a2, 2; la a3, aps_off; la a4, aps_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lbbc_fail\n" ++
  "  la t0, aps_off; ld t0, 0(t0); la t1, bsr_acct; add t1, t1, t0; la t0, baap_storage_root_ptr; sd t1, 0(t0)\n" ++
  "  la t2, aps_empty_root; li t3, 32\n" ++
  ".Lbbc_empty_cmp:\n" ++
  "  beqz t3, .Lbbc_empty\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbbc_nonempty\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbbc_empty_cmp\n" ++
  ".Lbbc_empty:\n" ++
  "  li t0, 1; la t1, baap_storage_empty_flag; sd t0, 0(t1); j .Lbbc_init\n" ++
  ".Lbbc_nonempty:\n" ++
  "  la t0, baap_storage_empty_flag; sd zero, 0(t0)\n" ++
  ".Lbbc_init:\n" ++
  "  la t0, baap_storage_values; la t1, baap_storage_value_cursor; sd t0, 0(t1)\n" ++
  "  la t0, baap_sc_out_count; sd zero, 0(t0)\n" ++
  "  # Descriptor 0: timestamp slot -> timestamp value.\n" ++
  "  la t0, swd_4788_vlen; ld a1, 0(t0); beqz a1, .Lbbc_after_ts\n" ++
  "  la a0, swd_4788_val; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, srss_rlpval_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la a0, swd_4788_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256\n" ++
  "  la a0, srss_key; li a1, 32; la a2, baap_storage_paths; jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_ts_insert\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la a3, baap_storage_paths; li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbbc_ts_modify\n" ++
  "  li t0, 1; bne a0, t0, .Lbbc_fail\n" ++
  ".Lbbc_ts_insert:\n" ++
  "  li t5, 1; j .Lbbc_ts_mode\n" ++
  ".Lbbc_ts_modify:\n" ++
  "  li t5, 0\n" ++
  ".Lbbc_ts_mode:\n" ++
  "  la t1, baap_storage_desc; la t2, baap_storage_paths; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)\n" ++
  "  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1); la t4, srss_rlpval_len; ld t4, 0(t4); sd t4, 24(t1); sd t5, 32(t1)\n" ++
  "  add t3, t3, t4; addi t3, t3, 7; andi t3, t3, -8; sd t3, 0(t2)\n" ++
  "  la t0, baap_sc_out_count; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lbbc_after_ts:\n" ++
  "  # Descriptor 1: timestamp+8191 slot -> parent_beacon_block_root.\n" ++
  "  la t0, swd_4788_root_vlen; ld a1, 0(t0); beqz a1, .Lbbc_root_zero\n" ++
  "  la a0, swd_4788_root_val; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, srss_rlpval_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la a0, swd_4788_root_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1\n" ++
  "  la a0, srss_key; li a1, 32; jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_root_insert\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a3, t2, t1\n" ++
  "  li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbbc_root_modify\n" ++
  "  li t0, 1; bne a0, t0, .Lbbc_fail\n" ++
  ".Lbbc_root_insert:\n" ++
  "  li t5, 1; j .Lbbc_root_mode\n" ++
  ".Lbbc_root_modify:\n" ++
  "  li t5, 0\n" ++
  ".Lbbc_root_mode:\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)\n" ++
  "  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1); la t4, srss_rlpval_len; ld t4, 0(t4); sd t4, 24(t1); sd t5, 32(t1)\n" ++
  "  add t3, t3, t4; addi t3, t3, 7; andi t3, t3, -8; sd t3, 0(t2)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)\n" ++
  "  j .Lbbc_apply_storage\n" ++
  ".Lbbc_root_zero:\n" ++
  "  # EIP-4788 writes zero to the root slot as a storage deletion. If the\n" ++
  "  # storage trie is empty or the key is absent, deleting is a no-op.\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_apply_storage\n" ++
  "  la a0, swd_4788_root_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1\n" ++
  "  la a0, srss_key; li a1, 32; jal ra, bytes_to_nibbles\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a3, t2, t1\n" ++
  "  li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk\n" ++
  "  beqz a0, .Lbbc_root_delete_desc\n" ++
  "  li t0, 1; beq a0, t0, .Lbbc_apply_storage\n" ++
  "  j .Lbbc_fail\n" ++
  ".Lbbc_root_delete_desc:\n" ++
  "  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1\n" ++
  "  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)\n" ++
  "  sd zero, 16(t1); sd zero, 24(t1); li t5, 2; sd t5, 32(t1)\n" ++
  "  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)\n" ++
  ".Lbbc_apply_storage:\n" ++
  "  la t0, baap_sc_out_count; ld a4, 0(t0); beqz a4, .Lbbc_fail\n" ++
  "  la t0, baap_storage_empty_flag; ld t0, 0(t0); beqz t0, .Lbbc_apply_nonempty\n" ++
  "  la a0, aps_empty_root; mv a1, zero; mv a2, zero; la a3, baap_storage_desc; j .Lbbc_apply_call\n" ++
  ".Lbbc_apply_nonempty:\n" ++
  "  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0); la a3, baap_storage_desc\n" ++
  ".Lbbc_apply_call:\n" ++
  "  la a5, aps_newsroot; jal ra, mpt_state_root_ins\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); la a2, aps_newsroot\n" ++
  "  slli t0, s0, 7; la t1, bsr_newaccts; add a3, t1, t0; la a4, bsr_tmplen\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Lbbc_fail\n" ++
  "  slli t0, s0, 5; slli t4, s0, 3; add t0, t0, t4; la t1, bsr_changes; add t1, t1, t0\n" ++
  "  la t2, bsr_pathp; ld t2, 0(t2); sd t2, 0(t1); li t3, 64; sd t3, 8(t1)\n" ++
  "  slli t0, s0, 7; la t2, bsr_newaccts; add t2, t2, t0; sd t2, 16(t1)\n" ++
  "  la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1); sd zero, 32(t1)\n" ++
  "  li a0, 0; j .Lbbc_ret\n" ++
  ".Lbbc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

end EvmAsm.Codegen
