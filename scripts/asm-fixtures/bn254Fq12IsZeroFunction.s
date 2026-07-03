bnq_is_zero:
  li t0, 48
  li t1, 0
.Lbnq_isz_loop:
  beqz t0, .Lbnq_isz_done
  ld t2, 0(a0)
  or t1, t1, t2
  addi a0, a0, 8
  addi t0, t0, -1
  j .Lbnq_isz_loop
.Lbnq_isz_done:
  seqz a0, t1
  ret
