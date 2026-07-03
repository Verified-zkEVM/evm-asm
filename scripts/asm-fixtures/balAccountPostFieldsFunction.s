bal_account_post_fields:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # account-change ptr
  mv s1, a1                   # account-change len
  mv s2, a2                   # balance out ptr
  mv s3, a3                   # balance len ptr
  mv s4, a4                   # nonce out ptr
  mv s5, a5                   # nonce len ptr
  li t0, -1; sd t0, 0(s3); sd t0, 0(s5)
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lbpf_fail
  sd a0, 56(sp); sd a1, 64(sp)
  # Skip address, storage_changes, storage_reads.
  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 56(sp)
  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 56(sp)
  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 56(sp)
  # balance_changes is field 3.
  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next
  bnez a1, .Lbpf_fail
  sd a0, 56(sp); sub t0, a0, a2; mv t1, a2
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init
  bnez a2, .Lbpf_fail
  beq a0, a1, .Lbpf_nonce
  sd a0, 72(sp); sd a1, 80(sp)
.Lbpf_bal_last_loop:
  ld t0, 72(sp); ld t1, 80(sp); beq t0, t1, .Lbpf_bal_have_last
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next
  bnez a1, .Lbpf_fail
  sd a0, 72(sp); sub t0, a0, a2; sd t0, 88(sp); sd a2, 96(sp)
  j .Lbpf_bal_last_loop
.Lbpf_bal_have_last:
  ld a0, 88(sp); ld a1, 96(sp); jal ra, rlp_walk_init
  bnez a2, .Lbpf_fail
  sd a0, 72(sp); sd a1, 80(sp)
  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 72(sp)
  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next
  bnez a1, .Lbpf_fail
  sub t0, a0, a2; mv t2, a2; li t3, 32; bgtu t2, t3, .Lbpf_fail
  sd t2, 0(s3)
  mv t4, s2
.Lbpf_bal_cp:
  beqz t2, .Lbpf_nonce
  lbu t5, 0(t0); sb t5, 0(t4)
  addi t0, t0, 1; addi t4, t4, 1; addi t2, t2, -1
  j .Lbpf_bal_cp
.Lbpf_nonce:
  # nonce_changes is field 4.
  ld a0, 56(sp); ld a1, 64(sp); jal ra, rlp_walk_next
  bnez a1, .Lbpf_fail
  sub t0, a0, a2; mv t1, a2
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init
  bnez a2, .Lbpf_fail
  beq a0, a1, .Lbpf_ok
  sd a0, 72(sp); sd a1, 80(sp)
.Lbpf_nonce_last_loop:
  ld t0, 72(sp); ld t1, 80(sp); beq t0, t1, .Lbpf_nonce_have_last
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next
  bnez a1, .Lbpf_fail
  sd a0, 72(sp); sub t0, a0, a2; sd t0, 88(sp); sd a2, 96(sp)
  j .Lbpf_nonce_last_loop
.Lbpf_nonce_have_last:
  ld a0, 88(sp); ld a1, 96(sp); jal ra, rlp_walk_init
  bnez a2, .Lbpf_fail
  sd a0, 72(sp); sd a1, 80(sp)
  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next; bnez a1, .Lbpf_fail; sd a0, 72(sp)
  ld a0, 72(sp); ld a1, 80(sp); jal ra, rlp_walk_next
  bnez a1, .Lbpf_fail
  sub t0, a0, a2; mv t2, a2; li t3, 32; bgtu t2, t3, .Lbpf_fail
  sd t2, 0(s5)
  mv t4, s4
.Lbpf_nonce_cp:
  beqz t2, .Lbpf_ok
  lbu t5, 0(t0); sb t5, 0(t4)
  addi t0, t0, 1; addi t4, t4, 1; addi t2, t2, -1
  j .Lbpf_nonce_cp
.Lbpf_ok:
  li a0, 0; j .Lbpf_ret
.Lbpf_fail:
  li a0, 1
.Lbpf_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 112
  ret
