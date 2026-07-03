u256_to_u64_be:
  # Check high 24 bytes (positions 0..24) are all zero.
  ld t0,  0(a0)
  ld t1,  8(a0)
  ld t2, 16(a0)
  or t0, t0, t1
  or t0, t0, t2
  # Assemble low u64 from BE bytes at positions 24..32.
  lbu t1, 24(a0); slli t1, t1, 56
  lbu t2, 25(a0); slli t2, t2, 48; or t1, t1, t2
  lbu t2, 26(a0); slli t2, t2, 40; or t1, t1, t2
  lbu t2, 27(a0); slli t2, t2, 32; or t1, t1, t2
  lbu t2, 28(a0); slli t2, t2, 24; or t1, t1, t2
  lbu t2, 29(a0); slli t2, t2, 16; or t1, t1, t2
  lbu t2, 30(a0); slli t2, t2,  8; or t1, t1, t2
  lbu t2, 31(a0);                  or t1, t1, t2
  sd t1, 0(a1)
  snez a0, t0                      # overflow = (high bits != 0)
  ret
