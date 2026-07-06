spw_u32le:
  lbu t0, 0(a0)
  lbu t1, 1(a0); slli t1, t1, 8;  or t0, t0, t1
  lbu t1, 2(a0); slli t1, t1, 16; or t0, t0, t1
  lbu t1, 3(a0); slli t1, t1, 24; or t0, t0, t1
  mv a0, t0
  ret
