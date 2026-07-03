blq_is_zero:
  li t0, 72
  li t1, 0
.Lblq_isz_loop:
  beqz t0, .Lblq_isz_done
  ld t2, 0(a0)
  or t1, t1, t2
  addi a0, a0, 8
  addi t0, t0, -1
  j .Lblq_isz_loop
.Lblq_isz_done:
  seqz a0, t1
  ret
