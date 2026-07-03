bsr_beacon_change:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a4                   # state change index
  la a0, bsr_addr_4788; li a1, 20; la a2, bsr_kbuf; jal ra, zkvm_keccak256
  slli t0, s0, 6; la t1, bsr_paths; add t2, t1, t0
  la t3, bsr_pathp; sd t2, 0(t3)
  la a0, bsr_kbuf; li a1, 32; mv a2, t2; jal ra, bytes_to_nibbles
  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)
  la t0, bsr_pathp; ld a3, 0(t0); li a4, 64; la a5, bsr_acct; la a6, bsr_acct_len
  jal ra, mpt_walk
  bnez a0, .Lbbc_fail
  la t0, bsr_wit_p; ld t1, 0(t0); la t0, aps_witness_ptr; sd t1, 0(t0)
  la t0, bsr_wl_v;  ld t1, 0(t0); la t0, aps_witness_len; sd t1, 0(t0)
  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); li a2, 2; la a3, aps_off; la a4, aps_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lbbc_fail
  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lbbc_fail
  la t0, aps_off; ld t0, 0(t0); la t1, bsr_acct; add t1, t1, t0; la t0, baap_storage_root_ptr; sd t1, 0(t0)
  la t2, aps_empty_root; li t3, 32
.Lbbc_empty_cmp:
  beqz t3, .Lbbc_empty
  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbbc_nonempty
  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbbc_empty_cmp
.Lbbc_empty:
  li t0, 1; la t1, baap_storage_empty_flag; sd t0, 0(t1); j .Lbbc_init
.Lbbc_nonempty:
  la t0, baap_storage_empty_flag; sd zero, 0(t0)
.Lbbc_init:
  la t0, baap_storage_values; la t1, baap_storage_value_cursor; sd t0, 0(t1)
  la t0, baap_sc_out_count; sd zero, 0(t0)
  # Descriptor 0: timestamp slot -> timestamp value.
  la t0, swd_4788_vlen; ld a1, 0(t0); beqz a1, .Lbbc_after_ts
  la a0, swd_4788_val; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, srss_rlpval_len
  jal ra, rlp_encode_bytes
  la a0, swd_4788_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256
  la a0, srss_key; li a1, 32; la a2, baap_storage_paths; jal ra, bytes_to_nibbles
  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_ts_insert
  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)
  la a3, baap_storage_paths; li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk
  beqz a0, .Lbbc_ts_modify
  li t0, 1; bne a0, t0, .Lbbc_fail
.Lbbc_ts_insert:
  li t5, 1; j .Lbbc_ts_mode
.Lbbc_ts_modify:
  li t5, 0
.Lbbc_ts_mode:
  la t1, baap_storage_desc; la t2, baap_storage_paths; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)
  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1); la t4, srss_rlpval_len; ld t4, 0(t4); sd t4, 24(t1); sd t5, 32(t1)
  add t3, t3, t4; addi t3, t3, 7; andi t3, t3, -8; sd t3, 0(t2)
  la t0, baap_sc_out_count; li t1, 1; sd t1, 0(t0)
.Lbbc_after_ts:
  # Descriptor 1: timestamp+8191 slot -> parent_beacon_block_root.
  la t0, swd_4788_root_vlen; ld a1, 0(t0); beqz a1, .Lbbc_root_zero
  la a0, swd_4788_root_val; la t2, baap_storage_value_cursor; ld a2, 0(t2); la a3, srss_rlpval_len
  jal ra, rlp_encode_bytes
  la a0, swd_4788_root_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256
  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1
  la a0, srss_key; li a1, 32; jal ra, bytes_to_nibbles
  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_root_insert
  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)
  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a3, t2, t1
  li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk
  beqz a0, .Lbbc_root_modify
  li t0, 1; bne a0, t0, .Lbbc_fail
.Lbbc_root_insert:
  li t5, 1; j .Lbbc_root_mode
.Lbbc_root_modify:
  li t5, 0
.Lbbc_root_mode:
  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1
  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)
  la t2, baap_storage_value_cursor; ld t3, 0(t2); sd t3, 16(t1); la t4, srss_rlpval_len; ld t4, 0(t4); sd t4, 24(t1); sd t5, 32(t1)
  add t3, t3, t4; addi t3, t3, 7; andi t3, t3, -8; sd t3, 0(t2)
  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)
  j .Lbbc_apply_storage
.Lbbc_root_zero:
  # EIP-4788 writes zero to the root slot as a storage deletion. If the
  # storage trie is empty or the key is absent, deleting is a no-op.
  la t0, baap_storage_empty_flag; ld t0, 0(t0); bnez t0, .Lbbc_apply_storage
  la a0, swd_4788_root_slot; li a1, 32; la a2, srss_key; jal ra, zkvm_keccak256
  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a2, t2, t1
  la a0, srss_key; li a1, 32; jal ra, bytes_to_nibbles
  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)
  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 6; la t2, baap_storage_paths; add a3, t2, t1
  li a4, 64; la a5, baap_walk_val; la a6, baap_walk_val_len; jal ra, mpt_walk
  beqz a0, .Lbbc_root_delete_desc
  li t0, 1; beq a0, t0, .Lbbc_apply_storage
  j .Lbbc_fail
.Lbbc_root_delete_desc:
  la t0, baap_sc_out_count; ld t0, 0(t0); slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2; la t2, baap_storage_desc; add t1, t2, t1
  slli t2, t0, 6; la t3, baap_storage_paths; add t2, t3, t2; sd t2, 0(t1); li t2, 64; sd t2, 8(t1)
  sd zero, 16(t1); sd zero, 24(t1); li t5, 2; sd t5, 32(t1)
  addi t0, t0, 1; la t1, baap_sc_out_count; sd t0, 0(t1)
.Lbbc_apply_storage:
  la t0, baap_sc_out_count; ld a4, 0(t0); beqz a4, .Lbbc_fail
  la t0, baap_storage_empty_flag; ld t0, 0(t0); beqz t0, .Lbbc_apply_nonempty
  la a0, aps_empty_root; mv a1, zero; mv a2, zero; la a3, baap_storage_desc; j .Lbbc_apply_call
.Lbbc_apply_nonempty:
  la t0, baap_storage_root_ptr; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0); la a3, baap_storage_desc
.Lbbc_apply_call:
  la a5, aps_newsroot; jal ra, mpt_state_root_ins
  bnez a0, .Lbbc_fail
  la a0, bsr_acct; la t0, bsr_acct_len; ld a1, 0(t0); la a2, aps_newsroot
  slli t0, s0, 7; la t1, bsr_newaccts; add a3, t1, t0; la a4, bsr_tmplen
  jal ra, account_set_storage_root
  bnez a0, .Lbbc_fail
  slli t0, s0, 5; slli t4, s0, 3; add t0, t0, t4; la t1, bsr_changes; add t1, t1, t0
  la t2, bsr_pathp; ld t2, 0(t2); sd t2, 0(t1); li t3, 64; sd t3, 8(t1)
  slli t0, s0, 7; la t2, bsr_newaccts; add t2, t2, t0; sd t2, 16(t1)
  la t2, bsr_tmplen; ld t2, 0(t2); sd t2, 24(t1); sd zero, 32(t1)
  li a0, 0; j .Lbbc_ret
.Lbbc_fail:
  li a0, 1
.Lbbc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
