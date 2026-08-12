account_writes_restore_frame:
  addi sp, sp, -48
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp); sd t4, 32(sp); sd t5, 40(sp)
  la t0, account_writes_undo_count; ld t1, 0(t0)
.Lawf_loop:
  bgeu a0, t1, .Lawf_done
  addi t1, t1, -1
  li t2, 0xbe380000; slli t3, t1, 7; add t3, t2, t3
  ld t4, 0(t3)
  ld t5, 8(t3)
  beqz t5, .Lawf_overwrite
  la t2, tx_account_writes_count; sd t4, 0(t2)
  j .Lawf_loop
.Lawf_overwrite:
  li t2, 0xbf780000; slli t5, t4, 7; add t5, t2, t5
  ld t2, 16(t3); sd t2, 32(t5); ld t2, 24(t3); sd t2, 40(t5); ld t2, 32(t3); sd t2, 48(t5); ld t2, 40(t3); sd t2, 56(t5)
  ld t2, 48(t3); sd t2, 64(t5); ld t2, 56(t3); sd t2, 72(t5); ld t2, 64(t3); sd t2, 80(t5); ld t2, 72(t3); sd t2, 88(t5)
  ld t2, 80(t3); sd t2, 96(t5); ld t2, 88(t3); sd t2, 104(t5); ld t2, 96(t3); sd t2, 112(t5); ld t2, 104(t3); sd t2, 120(t5)
  j .Lawf_loop
.Lawf_done:
  la t0, account_writes_undo_count; sd t1, 0(t0)
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp); ld t4, 32(sp); ld t5, 40(sp)
  addi sp, sp, 48
  ret
