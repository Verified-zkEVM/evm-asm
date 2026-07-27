intrinsic_gas_amsterdam_counts:
  li x5, 0
  li x6, 0
  mv x7, x10
  mv x28, x11
  beq x28, x0, .+36
  lbu x29, 0(x7)
  bne x29, x0, .+12
  addi x5, x5, 1
  jal x0, .+8
  addi x6, x6, 1
  addi x7, x7, 1
  addi x28, x28, -1
  jal x0, .-32
  slli x30, x6, 2
  add x30, x30, x5
  slli x31, x30, 2
  lui x29, 0x3
  addiw x29, x29, -288
  add x31, x31, x29
  li x28, 0
  beq x12, x0, .+52
  lui x29, 0x3
  addiw x29, x29, -1288
  add x28, x28, x29
  addi x29, x11, 31
  srli x29, x29, 5
  slli x29, x29, 1
  add x31, x31, x29
  ld x29, 0(x2)
  beq x29, x0, .+56
  li x29, 1756
  add x28, x28, x29
  jal x0, .+44
  ld x29, 8(x2)
  bne x29, x0, .+36
  lui x29, 0x1
  addiw x29, x29, -1096
  add x28, x28, x29
  ld x29, 0(x2)
  beq x29, x0, .+16
  lui x29, 0x1
  addiw x29, x29, 1904
  add x28, x28, x29
  add x31, x31, x28
  lui x29, 0x1
  addiw x29, x29, -1096
  mul x29, x13, x29
  add x31, x31, x29
  lui x29, 0x1
  addiw x29, x29, -1096
  mul x29, x14, x29
  add x31, x31, x29
  li x29, 80
  mul x7, x13, x29
  li x29, 128
  mul x29, x14, x29
  add x7, x7, x29
  slli x29, x7, 4
  add x31, x31, x29
  lui x29, 0x2
  addiw x29, x29, -376
  mul x29, x15, x29
  add x31, x31, x29
  sd x31, 0(x16)
  slli x30, x11, 2
  add x30, x30, x7
  slli x30, x30, 4
  lui x29, 0x3
  addiw x29, x29, -288
  add x30, x30, x29
  add x30, x30, x28
  sd x30, 0(x17)
  li x10, 0
  jalr x0, 0(x1)
