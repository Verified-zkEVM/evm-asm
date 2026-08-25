account_writes_undo_push:
  addi sp, sp, -64
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp); sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  la t0, account_writes_undo_count; ld t1, 0(t0)
  li t2, 163840; bgeu t1, t2, .Lawu_fail
  li t2, 3189645312  # ACCOUNT_WRITES_UNDO_AREA
  slli t3, t1, 7; add t3, t2, t3
  sd a5, 0(t3)
  sd a6, 8(t3)
  bnez a6, .Lawu_appended
  li t2, 3212312576; slli t4, a5, 7; add t4, t2, t4  # TX_ACCOUNT_WRITES_AREA
  ld t2, 32(t4);  sd t2, 16(t3); ld t2, 40(t4);  sd t2, 24(t3); ld t2, 48(t4);  sd t2, 32(t3); ld t2, 56(t4);  sd t2, 40(t3)
  ld t2, 64(t4);  sd t2, 48(t3); ld t2, 72(t4);  sd t2, 56(t3); ld t2, 80(t4);  sd t2, 64(t3); ld t2, 88(t4);  sd t2, 72(t3)
  ld t2, 96(t4);  sd t2, 80(t3); ld t2, 104(t4); sd t2, 88(t3); ld t2, 112(t4); sd t2, 96(t3); ld t2, 120(t4); sd t2, 104(t3)
.Lawu_appended:
  addi t1, t1, 1; la t0, account_writes_undo_count; sd t1, 0(t0); li a0, 0; j .Lawu_done
.Lawu_fail:
  li a0, 1; la t3, tx_account_writes_overflow; sd a0, 0(t3); la t3, account_writes_overflow; sd a0, 0(t3)
.Lawu_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp); ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  addi sp, sp, 64
  ret
