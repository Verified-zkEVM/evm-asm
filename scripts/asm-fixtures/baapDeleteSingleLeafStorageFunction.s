baap_delete_single_leaf_storage:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  sd s5, 48(sp)
  mv s0, a0                   # account
  mv s1, a1                   # account len
  mv s2, a2                   # slot key
  mv s3, a3                   # out account
  mv s4, a4                   # out len
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lbaapdsl_fail
  mv s5, a1                    # account list end
  mv a1, s5; jal ra, rlp_walk_next; bnez a1, .Lbaapdsl_fail
  mv a1, s5; jal ra, rlp_walk_next; bnez a1, .Lbaapdsl_fail
  mv a1, s5; jal ra, rlp_walk_next; bnez a1, .Lbaapdsl_fail
  li t2, 32; bne a2, t2, .Lbaapdsl_fail
  sub t1, a0, a2; la t0, baap_storage_root_ptr; sd t1, 0(t0)
  # Deleting from an empty storage trie is a no-op.
  mv t2, t1; la t3, aps_empty_root; li t4, 32
.Lbaapdsl_empty_cmp:
  beqz t4, .Lbaapdsl_copy_current
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lbaapdsl_nonempty
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lbaapdsl_empty_cmp
.Lbaapdsl_nonempty:
  mv a0, s2; li a1, 32; la a2, srss_key
  jal ra, zkvm_keccak256
  la a0, srss_key; li a1, 32; la a2, baap_storage_paths
  jal ra, bytes_to_nibbles
  la t0, aps_witness_ptr; ld a0, 0(t0); beqz a0, .Lbaapdsl_fail
  la t0, aps_witness_len; ld a1, 0(t0); la t0, baap_storage_root_ptr; ld a2, 0(t0)
  la a3, baap_item_off; la a4, baap_item_len
  jal ra, witness_lookup_by_hash
  bnez a0, .Lbaapdsl_fail
  la t0, aps_witness_ptr; ld t1, 0(t0); la t0, baap_item_off; ld t2, 0(t0); add a0, t1, t2
  la t0, baap_item_len; ld a1, 0(t0); la a2, baap_walk_val; la a3, baap_walk_val_len
  la a4, baap_code_item_ptr; la a5, baap_val_len
  jal ra, mpt_leaf_extract
  bnez a0, .Lbaapdsl_fail
  la t0, baap_walk_val_len; ld t0, 0(t0); li t1, 64; bne t0, t1, .Lbaapdsl_fail
  la t0, baap_walk_val; la t1, baap_storage_paths; li t2, 64
.Lbaapdsl_path_cmp:
  beqz t2, .Lbaapdsl_set_empty
  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbaapdsl_fail
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbaapdsl_path_cmp
.Lbaapdsl_set_empty:
  mv a0, s0; mv a1, s1; la a2, aps_empty_root; mv a3, s3; mv a4, s4
  jal ra, account_set_storage_root
  bnez a0, .Lbaapdsl_fail
  li a0, 0; j .Lbaapdsl_ret
.Lbaapdsl_copy_current:
  mv a0, s3; mv a1, s0; mv a2, s1
  jal ra, mset_memcpy
  sd s1, 0(s4)
  li a0, 0; j .Lbaapdsl_ret
.Lbaapdsl_fail:
  li a0, 1
.Lbaapdsl_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  ld s5, 48(sp)
  addi sp, sp, 64
  ret
