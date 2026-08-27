read_sets_merge_one:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0
  mv s1, a2
  mv s2, a4
  mv s3, a5
  mv s4, a3
  mv s5, a6
  mv s6, a7
  ld s7, 0(a1)
  li t0, 0
.Lrsm_tx:
  bgeu t0, s7, .Lrsm_done
  mul t1, t0, s2; add t1, s0, t1
  ld t2, 0(s4)
  li t3, 0
.Lrsm_blk:
  bgeu t3, t2, .Lrsm_append
  mul t4, t3, s2; add t4, s1, t4
  li t5, 0
.Lrsm_cmp:
  bgeu t5, s3, .Lrsm_next_tx
  add t6, t1, t5; lbu t6, 0(t6)
  add a0, t4, t5; lbu a0, 0(a0)
  bne t6, a0, .Lrsm_next_blk
  addi t5, t5, 1; j .Lrsm_cmp
.Lrsm_next_blk:
  addi t3, t3, 1; j .Lrsm_blk
.Lrsm_append:
  bgeu t2, s5, .Lrsm_overflow
  mul t4, t2, s2; add t4, s1, t4
  li t5, 0
.Lrsm_zero:
  bgeu t5, s2, .Lrsm_copy_init
  add t6, t4, t5; sb zero, 0(t6)
  addi t5, t5, 1; j .Lrsm_zero
.Lrsm_copy_init:
  li t5, 0
.Lrsm_copy:
  bgeu t5, s2, .Lrsm_bump
  add t6, t1, t5; lbu t6, 0(t6)
  add a0, t4, t5; sb t6, 0(a0)
  addi t5, t5, 1; j .Lrsm_copy
.Lrsm_bump:
  addi t2, t2, 1; sd t2, 0(s4)
  j .Lrsm_next_tx
.Lrsm_overflow:
  li t5, 1; sd t5, 0(s6)
.Lrsm_next_tx:
  addi t0, t0, 1; j .Lrsm_tx
.Lrsm_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
