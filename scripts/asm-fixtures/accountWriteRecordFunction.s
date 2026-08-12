account_write_record:
  addi sp, sp, -128
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp); sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp); sd ra, 56(sp)
  sd a0, 64(sp); sd a1, 72(sp); sd a2, 80(sp); sd a3, 88(sp); sd a4, 96(sp); sd a5, 104(sp); sd a6, 112(sp); sd a7, 120(sp)
  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xbf780000; li t4, 0
.Lawr_scan:
  bgeu t4, t1, .Lawr_append; slli t5, t4, 7; add t5, t3, t5; li t6, 20; mv t2, t5; ld t3, 64(sp)
.Lawr_cmp:
  beqz t6, .Lawr_hit; lbu a0, 0(t2); lbu a1, 0(t3); bne a0, a1, .Lawr_next; addi t2, t2, 1; addi t3, t3, 1; addi t6, t6, -1; j .Lawr_cmp
.Lawr_hit:
  mv a5, t4; li a6, 0; jal ra, account_writes_undo_push; bnez a0, .Lawr_overflow; j .Lawr_store
.Lawr_next:
  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xbf780000; addi t4, t4, 1; j .Lawr_scan
.Lawr_append:
  li t2, 16384; bgeu t1, t2, .Lawr_overflow; mv a5, t1; li a6, 1; jal ra, account_writes_undo_push; bnez a0, .Lawr_overflow
  la t0, tx_account_writes_count; ld t1, 0(t0); li t3, 0xbf780000; slli t5, t1, 7; add t5, t3, t5; ld t2, 64(sp); li t6, 20
.Lawr_copy_addr:
  beqz t6, .Lawr_zero; lbu t3, 0(t2); sb t3, 0(t5); addi t2, t2, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lawr_copy_addr
.Lawr_zero:
  addi t5, t5, -20; sw zero, 20(t5); sd zero, 24(t5); sd zero, 32(t5); sd zero, 40(t5); sd zero, 48(t5); sd zero, 56(t5); sd zero, 64(t5); sd zero, 72(t5); sd zero, 80(t5); sd zero, 88(t5); sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5); addi t1, t1, 1; sd t1, 0(t0)
.Lawr_store:
  ld t2, 112(sp); andi t3, t2, 1; beqz t3, .Lawr_no_balance; ld t3, 72(sp); ld t4, 0(t3); sd t4, 32(t5); ld t4, 8(t3); sd t4, 40(t5); ld t4, 16(t3); sd t4, 48(t5); ld t4, 24(t3); sd t4, 56(t5)
.Lawr_no_balance:
  andi t3, t2, 2; beqz t3, .Lawr_no_nonce; ld t3, 80(sp); ld t4, 64(t5); bltu t3, t4, .Lawr_no_nonce; sd t3, 64(t5)
.Lawr_no_nonce:
  andi t3, t2, 4; beqz t3, .Lawr_no_code; ld t3, 88(sp); sd t3, 80(t5); ld t3, 96(sp); sd t3, 88(t5)
.Lawr_no_code:
  andi t3, t2, 8; beqz t3, .Lawr_no_state; ld t3, 104(sp); sd t3, 72(t5)
.Lawr_no_state:
  andi t3, t2, 16; beqz t3, .Lawr_no_flags; ld t3, 120(sp); sd t3, 96(t5)
.Lawr_no_flags:
  ld t3, 112(t5); or t2, t2, t3; sd t2, 112(t5); j .Lawr_done
.Lawr_overflow:
  la t0, tx_account_writes_overflow; li t1, 1; sd t1, 0(t0); la t0, account_writes_overflow; sd t1, 0(t0)
.Lawr_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp); ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp); ld ra, 56(sp); addi sp, sp, 128
  ret
