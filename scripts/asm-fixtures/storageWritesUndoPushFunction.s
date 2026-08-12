storage_writes_undo_push:
  addi sp, sp, -64
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  la t0, storage_writes_undo_count; ld t1, 0(t0)
  li t2, 167652
  bgeu t1, t2, .Lswup_fail
  li t3, 3148533760
  slli t4, t1, 7; slli t5, t1, 5; add t4, t4, t5; add t4, t3, t4
  sd a3, 0(t4)
  sd a4, 8(t4)
  beqz a4, .Lswup_prevval
  li t5, 2; bne a4, t5, .Lswup_bump
  li t2, 0
.Lswup_row:
  li t5, 128; beq t2, t5, .Lswup_bump
  add t5, a5, t2; ld t6, 0(t5)
  add t5, t4, t2; sd t6, 32(t5)
  addi t2, t2, 8; j .Lswup_row
.Lswup_prevval:
  ld t5, 0(a5);  sd t5, 32(t4)
  ld t5, 8(a5);  sd t5, 40(t4)
  ld t5, 16(a5); sd t5, 48(t4)
  ld t5, 24(a5); sd t5, 56(t4)
.Lswup_bump:
  addi t1, t1, 1; sd t1, 0(t0); li a0, 0; j .Lswup_done
.Lswup_fail:
  li a0, 1; la t3, tx_storage_writes_overflow; sd a0, 0(t3); la t3, storage_writes_overflow; sd a0, 0(t3)
.Lswup_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  addi sp, sp, 64
  ret
