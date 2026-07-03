account_apply_storage_slot:
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
  bnez a0, .Laps_parsefail
  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Laps_conservative
  # compare the 32 storageRoot bytes (account + aps_off) to EMPTY_TRIE_ROOT
  la t0, aps_off; ld t1, 0(t0); add t1, s0, t1   # storageRoot ptr
  la t2, aps_empty_root; li t3, 32
.Laps_cmp:
  beqz t3, .Laps_empty
  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Laps_conservative
  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Laps_cmp
.Laps_empty:
  # new_storage_root = storage_root_single_slot(slot_key, value, value_len)
  mv a0, s2; mv a1, s3; mv a2, s4; la a3, aps_newsroot
  jal ra, storage_root_single_slot
  # new account = account_set_storage_root(account, len, new_storage_root, out, out_len)
  mv a0, s0; mv a1, s1; la a2, aps_newsroot; mv a3, s5; mv a4, s6
  jal ra, account_set_storage_root
  bnez a0, .Laps_parsefail
  li a0, 0
  j .Laps_ret
.Laps_conservative:
  li a0, 1
  j .Laps_ret
.Laps_parsefail:
  li a0, 2
.Laps_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
