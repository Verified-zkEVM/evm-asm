bnp_fp2_copy:
  ld t0,  0(a0); sd t0,  0(a1)
  ld t0,  8(a0); sd t0,  8(a1)
  ld t0, 16(a0); sd t0, 16(a1)
  ld t0, 24(a0); sd t0, 24(a1)
  ld t0, 32(a0); sd t0, 32(a1)
  ld t0, 40(a0); sd t0, 40(a1)
  ld t0, 48(a0); sd t0, 48(a1)
  ld t0, 56(a0); sd t0, 56(a1)
  ret
