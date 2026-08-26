header_validate_excess_blob_gas:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  add x20, x18, x9
  bltu x20, x18, .+196
  lui x5, 0x1c0
  bltu x20, x5, .+172
  lui x5, 0x7b958
  addiw x5, x5, -829
  bgeu x18, x5, .+148
  mv x10, x18
  la x11, hvebg_threshold
  jal x1, amsterdam_blob_gas_price_u256
  bne x10, x0, .+156
  la x10, hvebg_threshold
  li x11, 16
  la x12, hvebg_threshold
  jal x1, u256_mul_u64_be
  bne x10, x0, .+100
  la x10, hvebg_threshold
  mv x11, x19
  la x12, u256m_acc
  jal x1, u256_lt_be
  la x5, u256m_acc
  ld x5, 0(x5)
  beq x5, x0, .+60
  lui x5, 0x1249
  addiw x5, x5, 585
  slli x5, x5, 12
  addi x5, x5, 585
  slli x5, x5, 12
  addi x5, x5, 585
  slli x5, x5, 13
  addi x5, x5, 1170
  bltu x5, x9, .+52
  li x5, 3
  divu x6, x9, x5
  add x21, x18, x6
  bltu x21, x18, .+36
  jal x0, .+20
  lui x5, 0x1c0
  sub x21, x20, x5
  jal x0, .+8
  li x21, 0
  bne x8, x21, .+20
  li x10, 0
  jal x0, .+16
  li x10, 1
  jal x0, .+8
  li x10, 2
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
