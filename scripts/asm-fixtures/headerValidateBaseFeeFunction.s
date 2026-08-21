header_validate_base_fee:
  addi x2, x2, -48
  sd x1, 0(x2)
  sd x8, 8(x2)
  mv x8, x10
  mv x14, x11
  mv x15, x12
  mv x10, x13
  li x11, 32
  addi x12, x2, 16
  jal x1, swr_rev_le_be
  mv x10, x14
  mv x11, x15
  la x13, hvbf_expected
  jal x1, eip1559_calc_base_fee_per_gas
  bne x10, x0, .+56
  mv x10, x8
  li x11, 32
  addi x12, x2, 16
  jal x1, swr_rev_le_be
  mv x10, x12
  la x11, hvbf_expected
  jal x1, u256_eq
  beq x10, x0, .+12
  li x10, 0
  jal x0, .+16
  li x10, 1
  jal x0, .+8
  li x10, 2
  ld x1, 0(x2)
  ld x8, 8(x2)
  addi x2, x2, 48
  jalr x0, 0(x1)
