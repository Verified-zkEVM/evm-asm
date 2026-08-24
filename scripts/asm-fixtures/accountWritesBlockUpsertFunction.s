account_writes_block_upsert:
  addi sp, sp, -64
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  la t0, account_writes_count; ld t1, 0(t0)
  li t3, 3176538112
  li t4, 0
.Lawb_scan:
  bgeu t4, t1, .Lawb_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; mv t3, a0
.Lawb_cmp:
  beqz t6, .Lawb_store; lbu t1, 0(t2); lbu a1, 0(t3); bne t1, a1, .Lawb_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawb_cmp
.Lawb_next:
  la t0, account_writes_count; ld t1, 0(t0); li t3, 3176538112; addi t4, t4, 1; j .Lawb_scan
.Lawb_append:
  li t2, 102400
  bgeu t1, t2, .Lawb_overflow
  slli t5, t1, 7; add t5, t3, t5; li t6, 20; mv t2, a0
.Lawb_copy_addr:
  beqz t6, .Lawb_zero; lbu t3, 0(t2); sb t3, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lawb_copy_addr
.Lawb_zero:
  addi t5, t5, -20; sw zero, 20(t5); sd zero, 24(t5); sd zero, 32(t5); sd zero, 40(t5); sd zero, 48(t5); sd zero, 56(t5); sd zero, 64(t5); sd zero, 72(t5); sd zero, 80(t5); sd zero, 88(t5); sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5); addi t1, t1, 1; sd t1, 0(t0)
.Lawb_store:
  ld t2, 112(a0); andi t3, t2, 1; beqz t3, .Lawb_no_balance; ld t3, 32(a0); sd t3, 32(t5); ld t3, 40(a0); sd t3, 40(t5); ld t3, 48(a0); sd t3, 48(t5); ld t3, 56(a0); sd t3, 56(t5)
.Lawb_no_balance:
  andi t3, t2, 2; beqz t3, .Lawb_no_nonce; ld t3, 64(a0); sd t3, 64(t5)
.Lawb_no_nonce:
  andi t3, t2, 4; beqz t3, .Lawb_no_code; ld t3, 80(a0); sd t3, 80(t5); ld t3, 88(a0); sd t3, 88(t5)
.Lawb_no_code:
  andi t3, t2, 8; beqz t3, .Lawb_no_state; ld t3, 72(a0); sd t3, 72(t5)
.Lawb_no_state:
  andi t3, t2, 16; beqz t3, .Lawb_no_flags; ld t3, 96(a0); sd t3, 96(t5)
.Lawb_no_flags:
  ld t3, 112(t5); or t2, t2, t3; sd t2, 112(t5)
  j .Lawb_done
.Lawb_overflow:
  la t0, account_writes_overflow; li t1, 1; sd t1, 0(t0)
.Lawb_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  addi sp, sp, 64
  ret
