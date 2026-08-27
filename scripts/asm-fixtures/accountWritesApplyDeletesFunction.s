account_writes_apply_deletes:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  la t0, account_state_delete_count; ld s2, 0(t0); li t0, 8192; bgtu s2, t0, .Lawd_overflow
  li s1, 0
.Lawd_delete_loop:
  bgeu s1, s2, .Lawd_ok
  slli t0, s1, 5; la t1, account_state_delete; add s0, t1, t0; ld t0, 24(s0); beqz t0, .Lawd_delete_next
  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 16384; bgtu t1, t2, .Lawd_overflow; li s3, 0
.Lawd_tx_loop:
  bgeu s3, t1, .Lawd_miss
  slli t2, s3, 7; li t3, 3212312576; add t2, t3, t2; mv t3, t2; mv t4, s0; li t5, 20  # TX_ACCOUNT_WRITES_AREA
.Lawd_cmp:
  beqz t5, .Lawd_hit; lbu t6, 0(t3); lbu a0, 0(t4); bne t6, a0, .Lawd_next; addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lawd_cmp
.Lawd_next:
  addi s3, s3, 1; j .Lawd_tx_loop
.Lawd_hit:
  mv a5, s3; li a6, 0; jal ra, account_writes_undo_push; bnez a0, .Lawd_overflow
  slli t0, s3, 7; li t1, 3212312576; add t0, t1, t0; sd zero, 64(t0); sd zero, 80(t0); sd zero, 88(t0); sd zero, 96(t0); sd zero, 104(t0)  # TX_ACCOUNT_WRITES_AREA
  ld t1, 32(t0); ld t2, 40(t0); or t1, t1, t2; ld t2, 48(t0); or t1, t1, t2; ld t2, 56(t0); or t1, t1, t2; bnez t1, .Lawd_keep_present
  ld t1, 112(t0); andi t1, t1, 1; bnez t1, .Lawd_present_none
  sd zero, 40(sp); sd zero, 48(sp); sd zero, 56(sp); sd zero, 64(sp); sd zero, 72(sp)
  mv a0, s0; addi a1, sp, 40; la t1, sv_pre_rlp_ptr; ld a2, 0(t1); la t1, sv_pre_rlp_len; ld a3, 0(t1); la t1, bv_witness_state_ptr; ld a4, 0(t1); la t1, bv_witness_state_len; ld a5, 0(t1); jal ra, account_resolve_pre_state
  bnez a0, .Lawd_overflow
  ld t1, 48(sp); ld t2, 56(sp); or t1, t1, t2; ld t2, 64(sp); or t1, t1, t2; ld t2, 72(sp); or t1, t1, t2; beqz t1, .Lawd_present_none
  slli t0, s3, 7; li t2, 3212312576; add t0, t2, t0  # TX_ACCOUNT_WRITES_AREA
  ld t1, 48(sp); sd t1, 32(t0); ld t1, 56(sp); sd t1, 40(t0)
  ld t1, 64(sp); sd t1, 48(t0); ld t1, 72(sp); sd t1, 56(t0)
  j .Lawd_keep_present
.Lawd_present_none:
  slli t0, s3, 7; li t1, 3212312576; add t0, t1, t0  # TX_ACCOUNT_WRITES_AREA
  sd zero, 72(t0); li t1, 15; sd t1, 112(t0); sd zero, 120(t0); j .Lawd_delete_next
.Lawd_keep_present:
  li t1, 1; sd t1, 72(t0); li t1, 15; sd t1, 112(t0); sd zero, 120(t0); j .Lawd_delete_next
.Lawd_miss:
  sd zero, 40(sp); sd zero, 48(sp); sd zero, 56(sp); sd zero, 64(sp)
  mv a0, s0; addi a1, sp, 40; li a2, 0; li a3, 0; li a4, 0; li a5, 0; li a6, 15; li a7, 0; jal ra, account_write_record
  la t0, tx_account_writes_overflow; ld t0, 0(t0); bnez t0, .Lawd_overflow
.Lawd_delete_next:
  addi s1, s1, 1; j .Lawd_delete_loop
.Lawd_ok:
  li a0, 0; j .Lawd_ret
.Lawd_overflow:
  la t0, tx_account_writes_overflow; li t1, 1; sd t1, 0(t0); la t0, account_writes_overflow; sd t1, 0(t0); li a0, 1
.Lawd_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 80; ret
