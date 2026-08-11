multi_tx_running_sender_balance_step:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5
  ld t0, 0(s1)                 # count
  li t1, 0                     # k
.Lmtxrb_scan:
  bgeu t1, t0, .Lmtxrb_append
  slli t2, t1, 6; add t2, s0, t2
  li t3, 0
.Lmtxrb_cmp:
  li t4, 20; beq t3, t4, .Lmtxrb_found
  add t5, t2, t3; lbu t5, 0(t5); add t6, s3, t3; lbu t6, 0(t6); bne t5, t6, .Lmtxrb_next
  addi t3, t3, 1; j .Lmtxrb_cmp
.Lmtxrb_next:
  addi t1, t1, 1; j .Lmtxrb_scan
.Lmtxrb_found:
  addi a0, t2, 32; mv a1, s5; addi a2, t2, 32
  jal ra, u256_sub_be
  beqz a0, .Lmtxrb_ok
  li a0, 1; j .Lmtxrb_ret
.Lmtxrb_append:
  bgeu t0, s2, .Lmtxrb_full
  slli t2, t0, 6; add t2, s0, t2
  li t3, 0
.Lmtxrb_copy_addr:
  li t4, 20; beq t3, t4, .Lmtxrb_zero_addr_tail
  add t5, s3, t3; lbu t5, 0(t5); add t6, t2, t3; sb t5, 0(t6); addi t3, t3, 1; j .Lmtxrb_copy_addr
.Lmtxrb_zero_addr_tail:
  li t4, 32; beq t3, t4, .Lmtxrb_append_sub
  add t6, t2, t3; sb zero, 0(t6); addi t3, t3, 1; j .Lmtxrb_zero_addr_tail
.Lmtxrb_append_sub:
  mv a0, s4; mv a1, s5; addi a2, t2, 32
  jal ra, u256_sub_be
  beqz a0, .Lmtxrb_append_count
  li a0, 1; j .Lmtxrb_ret
.Lmtxrb_append_count:
  ld t0, 0(s1); addi t0, t0, 1; sd t0, 0(s1)
.Lmtxrb_ok:
  li a0, 0; j .Lmtxrb_ret
.Lmtxrb_full:
  li a0, 2
.Lmtxrb_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64
  ret
