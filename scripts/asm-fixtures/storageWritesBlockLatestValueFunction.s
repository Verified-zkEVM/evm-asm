storage_writes_block_latest_value:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  bltu x14, x13, .+276
  mv x8, x15
  mv x9, x16
  mv x18, x17
  sd x0, 0(x9)
  sd x0, 8(x9)
  sd x0, 16(x9)
  sd x0, 24(x9)
  li x5, 0
  li x6, 20
  beq x5, x6, .+28
  add x7, x10, x5
  lbu x28, 0(x7)
  add x7, x9, x5
  sb x28, 0(x7)
  addi x5, x5, 1
  jal x0, .-28
  addi x5, x11, 31
  mv x6, x18
  li x7, 32
  beq x7, x0, .+28
  lbu x28, 0(x5)
  sb x28, 0(x6)
  addi x5, x5, -1
  addi x6, x6, 1
  addi x7, x7, -1
  jal x0, .-24
  li x5, 0
  beq x5, x13, .+156
  slli x6, x5, 7
  add x7, x12, x6
  ld x28, 0(x7)
  ld x29, 0(x9)
  bne x28, x29, .+128
  ld x28, 8(x7)
  ld x29, 8(x9)
  bne x28, x29, .+116
  ld x28, 16(x7)
  ld x29, 16(x9)
  bne x28, x29, .+104
  ld x28, 24(x7)
  ld x29, 24(x9)
  bne x28, x29, .+92
  ld x28, 32(x7)
  ld x29, 0(x18)
  bne x28, x29, .+80
  ld x28, 40(x7)
  ld x29, 8(x18)
  bne x28, x29, .+68
  ld x28, 48(x7)
  ld x29, 16(x18)
  bne x28, x29, .+56
  ld x28, 56(x7)
  ld x29, 24(x18)
  bne x28, x29, .+44
  ld x28, 64(x7)
  sd x28, 0(x8)
  ld x28, 72(x7)
  sd x28, 8(x8)
  ld x28, 80(x7)
  sd x28, 16(x8)
  ld x28, 88(x7)
  sd x28, 24(x8)
  li x10, 1
  jal x0, .+28
  addi x5, x5, 1
  jal x0, .-152
  li x10, 0
  jal x0, .+12
  li x10, 2
  jal x0, .+4
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
