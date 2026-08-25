account_at_address:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  mv x8, x15
  la x15, aa_value_scratch
  la x16, aa_value_len
  jal x1, mpt_lookup_by_key
  mv x9, x10
  beq x10, x0, .+80
  sd x0, 0(x8)
  sd x0, 8(x8)
  sd x0, 16(x8)
  sd x0, 24(x8)
  sd x0, 32(x8)
  sd x0, 40(x8)
  sd x0, 48(x8)
  sd x0, 56(x8)
  sd x0, 64(x8)
  sd x0, 72(x8)
  sd x0, 80(x8)
  sd x0, 88(x8)
  sd x0, 96(x8)
  li x5, 3
  bne x9, x5, .+12
  li x10, 4
  jal x0, .+120
  mv x10, x9
  jal x0, .+112
  la x10, aa_value_scratch
  la x5, aa_value_len
  ld x11, 0(x5)
  mv x12, x8
  addi x13, x8, 8
  addi x14, x8, 40
  addi x15, x8, 72
  jal x1, account_decode
  beq x10, x0, .+64
  sd x0, 0(x8)
  sd x0, 8(x8)
  sd x0, 16(x8)
  sd x0, 24(x8)
  sd x0, 32(x8)
  sd x0, 40(x8)
  sd x0, 48(x8)
  sd x0, 56(x8)
  sd x0, 64(x8)
  sd x0, 72(x8)
  sd x0, 80(x8)
  sd x0, 88(x8)
  sd x0, 96(x8)
  li x10, 3
  jal x0, .+8
  li x10, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
