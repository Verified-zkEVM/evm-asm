u256_is_zero:
  ld t0,  0(a0)
  ld t1,  8(a0)
  ld t2, 16(a0)
  ld t3, 24(a0)
  or t0, t0, t1
  or t0, t0, t2
  or t0, t0, t3
  seqz a0, t0
  ret
