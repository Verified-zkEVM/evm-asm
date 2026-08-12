write_sets_restore_frame:
  addi sp, sp, -64
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  la t0, storage_writes_undo_count; ld t1, 0(t0)
  li t3, 3148533760
  li t6, 2731900608
.Lswrf_loop:
  bleu t1, a0, .Lswrf_done
  addi t1, t1, -1
  slli t4, t1, 7; slli t5, t1, 5; add t4, t4, t5; add t4, t3, t4
  ld t2, 8(t4)
  li t5, 2; beq t2, t5, .Lswrf_reappend
  bnez t2, .Lswrf_unappend
  ld t2, 0(t4); slli t5, t2, 7; add t5, t6, t5
  ld t2, 32(t4); sd t2, 64(t5)
  ld t2, 40(t4); sd t2, 72(t5)
  ld t2, 48(t4); sd t2, 80(t5)
  ld t2, 56(t4); sd t2, 88(t5)
  j .Lswrf_loop
.Lswrf_unappend:
  la t2, tx_storage_writes_count; ld t5, 0(t2)
  beqz t5, .Lswrf_loop
  addi t5, t5, -1; sd t5, 0(t2)
  j .Lswrf_loop
.Lswrf_reappend:
  la t2, tx_storage_writes_count; ld t5, 0(t2)
  slli t0, t5, 7; add t0, t6, t0
  sd t0, 56(sp)
  li t2, 0
.Lswrf_re_cp:
  li t5, 128; beq t2, t5, .Lswrf_re_cnt
  add t5, t4, t2; ld t5, 32(t5)
  ld t0, 56(sp); add t0, t0, t2; sd t5, 0(t0)
  addi t2, t2, 8; j .Lswrf_re_cp
.Lswrf_re_cnt:
  la t2, tx_storage_writes_count; ld t5, 0(t2)
  addi t5, t5, 1; sd t5, 0(t2)
  j .Lswrf_loop
.Lswrf_done:
  la t0, storage_writes_undo_count; sd a0, 0(t0)
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  addi sp, sp, 64
  ret
