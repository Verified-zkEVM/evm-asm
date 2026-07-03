secf_copy32:
  ld t0,  0(a0); sd t0,  0(a1)
  ld t0,  8(a0); sd t0,  8(a1)
  ld t0, 16(a0); sd t0, 16(a1)
  ld t0, 24(a0); sd t0, 24(a1)
  ret
