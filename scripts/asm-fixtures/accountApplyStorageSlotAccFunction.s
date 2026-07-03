account_apply_storage_slot_acc:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # account
  mv s1, a1                   # account len
  mv s2, a2                   # slot_key
  mv s3, a3                   # value
  mv s4, a4                   # value len
  mv s5, a5                   # out
  mv s6, a6                   # out len
  # field 2 = storageRoot -> aps_off / aps_len
  mv a0, s0; mv a1, s1; li a2, 2; la a3, aps_off; la a4, aps_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lapsa_parsefail
  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lapsa_conservative
  la t0, aps_off; ld t1, 0(t0); add t1, s0, t1   # storageRoot ptr
  la t2, aps_empty_root; li t3, 32
.Lapsa_cmp:
  beqz t3, .Lapsa_empty
  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lapsa_nonempty
  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lapsa_cmp
.Lapsa_empty:
  beqz s4, .Lapsa_copy_current
  mv a0, s2; mv a1, s3; mv a2, s4; la a3, aps_newsroot
  jal ra, storage_root_single_slot
  j .Lapsa_set_account
.Lapsa_nonempty:
  # Need caller-provided witness for the existing storage trie.
  la t0, aps_witness_ptr; ld t0, 0(t0); beqz t0, .Lapsa_conservative
  beqz s4, .Lapsa_delete_nonempty
  # RLP(value) is the leaf value stored in the storage trie.
  mv a0, s3; mv a1, s4; la a2, srss_rlpval; la a3, srss_rlpval_len
  jal ra, rlp_encode_bytes
  # Storage path = nibbles(keccak256(slot_key)).
  mv a0, s2; li a1, 32; la a2, srss_key
  jal ra, zkvm_keccak256
  la a0, srss_key; li a1, 32; la a2, aps_path
  jal ra, bytes_to_nibbles
  # Update the non-empty storage trie through mpt_set_acc.
  la t0, mset_db_count; sd zero, 0(t0)
  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)
  la t0, aps_off; ld t0, 0(t0); add a0, s0, t0
  la t0, aps_witness_ptr; ld a1, 0(t0)
  la t0, aps_witness_len; ld a2, 0(t0)
  la a3, aps_path; li a4, 64
  la a5, srss_rlpval; la t0, srss_rlpval_len; ld a6, 0(t0); la a7, aps_newsroot
  jal ra, mpt_set_acc
  beqz a0, .Lapsa_set_account
  # If the slot was absent, insert it into the existing storage trie.
  la t0, mset_db_count; sd zero, 0(t0)
  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)
  la t0, aps_off; ld t0, 0(t0); add a0, s0, t0
  la t0, aps_witness_ptr; ld a1, 0(t0)
  la t0, aps_witness_len; ld a2, 0(t0)
  la a3, aps_path; li a4, 64
  la a5, srss_rlpval; la t0, srss_rlpval_len; ld a6, 0(t0); la a7, aps_newsroot
  jal ra, mpt_insert_acc
  bnez a0, .Lapsa_conservative
.Lapsa_set_account:
  mv a0, s0; mv a1, s1; la a2, aps_newsroot; mv a3, s5; mv a4, s6
  jal ra, account_set_storage_root
  bnez a0, .Lapsa_parsefail
  li a0, 0
  j .Lapsa_ret
.Lapsa_delete_nonempty:
  mv a0, s2; li a1, 32; la a2, srss_key
  jal ra, zkvm_keccak256
  la a0, srss_key; li a1, 32; la a2, aps_path
  jal ra, bytes_to_nibbles
  la t0, mset_db_count; sd zero, 0(t0)
  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)
  la t0, aps_off; ld t0, 0(t0); add a0, s0, t0
  la t0, aps_witness_ptr; ld a1, 0(t0)
  la t0, aps_witness_len; ld a2, 0(t0)
  la a3, aps_path; li a4, 64; la a7, aps_newsroot
  jal ra, mpt_delete_acc
  beqz a0, .Lapsa_set_account
  j .Lapsa_conservative
.Lapsa_copy_current:
  mv a0, s5; mv a1, s0; mv a2, s1
  jal ra, mset_memcpy
  sd s1, 0(s6)
  li a0, 0
  j .Lapsa_ret
.Lapsa_conservative:
  li a0, 1
  j .Lapsa_ret
.Lapsa_parsefail:
  li a0, 2
.Lapsa_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
