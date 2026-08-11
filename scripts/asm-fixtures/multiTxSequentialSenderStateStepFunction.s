multi_tx_sequential_sender_state_step:
  addi sp, sp, -88
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6; mv s7, a7
  ld t0, 0(s1); li t1, 0
.Lmtxseq_scan:
  bgeu t1, t0, .Lmtxseq_append
  slli t2, t1, 6; add t2, s0, t2; li t3, 0
.Lmtxseq_cmp:
  li t4, 20; beq t3, t4, .Lmtxseq_found
  add t5, t2, t3; lbu t5, 0(t5); add t6, s3, t3; lbu t6, 0(t6); bne t5, t6, .Lmtxseq_next
  addi t3, t3, 1; j .Lmtxseq_cmp
.Lmtxseq_next:
  addi t1, t1, 1; j .Lmtxseq_scan
.Lmtxseq_found:
  sd zero, 80(sp)
  j .Lmtxseq_check
.Lmtxseq_append:
  bgeu t0, s2, .Lmtxseq_full
  li t4, 1; sd t4, 80(sp)
  slli t2, t0, 6; add t2, s0, t2; li t3, 0
.Lmtxseq_copy_addr:
  li t4, 20; beq t3, t4, .Lmtxseq_copy_balance
  add t5, s3, t3; lbu t5, 0(t5); add t6, t2, t3; sb t5, 0(t6); addi t3, t3, 1; j .Lmtxseq_copy_addr
.Lmtxseq_copy_balance:
  li t3, 0
.Lmtxseq_copy_balance_loop:
  li t4, 32; beq t3, t4, .Lmtxseq_check
  add t5, s4, t3; lbu t5, 0(t5); add t6, t2, t3; addi t6, t6, 32; sb t5, 0(t6); addi t3, t3, 1; j .Lmtxseq_copy_balance_loop
.Lmtxseq_check:
  sd t2, 72(sp)
  addi a0, t2, 32; mv a1, s5; mv a2, s7; jal ra, u256_lt_be
  ld t0, 0(s7); bnez t0, .Lmtxseq_upfront
  ld t2, 72(sp)
  addi a0, t2, 32; mv a1, s6; addi a2, t2, 32; jal ra, u256_sub_be
  beqz a0, .Lmtxseq_count
  li a0, 2; j .Lmtxseq_ret
.Lmtxseq_count:
  ld t0, 80(sp); beqz t0, .Lmtxseq_updated
  ld t0, 0(s1); addi t0, t0, 1; sd t0, 0(s1)
.Lmtxseq_updated:
  li a0, 0; j .Lmtxseq_ret
.Lmtxseq_upfront:
  li a0, 1; j .Lmtxseq_ret
.Lmtxseq_full:
  li a0, 3
.Lmtxseq_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 88
  ret
