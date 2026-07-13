rlp_list_nth_item:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  mv x8, x10
  mv x9, x12
  mv x18, x13
  mv x19, x14
  jal x1, .+104
  bne x12, x0, .+60
  mv x20, x11
  li x21, 0
  mv x11, x20
  jal x1, .+296
  bne x11, x0, .+40
  beq x21, x9, .+12
  addi x21, x21, 1
  jal x0, .-20
  sub x5, x10, x12
  sub x5, x5, x8
  sd x5, 0(x18)
  sd x12, 0(x19)
  li x10, 0
  jal x0, .+8
  li x10, 1
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
  beq x11, x0, .+156
  add x11, x10, x11
  lbu x5, 0(x10)
  li x6, 192
  bltu x5, x6, .+148
  li x6, 248
  bltu x5, x6, .+100
  li x6, 247
  sub x7, x5, x6
  addi x28, x7, 1
  add x29, x10, x28
  bltu x11, x29, .+136
  addi x6, x10, 1
  lbu x30, 0(x6)
  beq x30, x0, .+132
  li x31, 0
  mv x30, x7
  beq x30, x0, .+28
  slli x31, x31, 8
  lbu x28, 0(x6)
  or x31, x31, x28
  addi x6, x6, 1
  addi x30, x30, -1
  jal x0, .-24
  li x6, 56
  bltu x31, x6, .+96
  add x6, x29, x31
  bne x6, x11, .+96
  mv x10, x29
  li x12, 0
  jalr x0, 0(x1)
  li x6, 192
  sub x7, x5, x6
  addi x28, x7, 1
  add x29, x10, x28
  bne x29, x11, .+32
  addi x10, x10, 1
  li x12, 0
  jalr x0, 0(x1)
  li x12, 2
  jalr x0, 0(x1)
  li x12, 1
  jalr x0, 0(x1)
  li x12, 3
  jalr x0, 0(x1)
  li x12, 4
  jalr x0, 0(x1)
  li x12, 5
  jalr x0, 0(x1)
  li x12, 6
  jalr x0, 0(x1)
  li x12, 7
  jalr x0, 0(x1)
  bgeu x10, x11, .+352
  lbu x5, 0(x10)
  li x6, 128
  bltu x5, x6, .+288
  li x6, 184
  bltu x5, x6, .+228
  li x6, 192
  bltu x5, x6, .+120
  li x6, 248
  bltu x5, x6, .+280
  li x6, 247
  sub x7, x5, x6
  addi x6, x7, 1
  add x29, x10, x6
  bltu x11, x29, .+308
  addi x30, x10, 1
  lbu x31, 0(x30)
  beq x31, x0, .+320
  li x28, 0
  mv x6, x7
  beq x6, x0, .+28
  slli x28, x28, 8
  lbu x31, 0(x30)
  or x28, x28, x31
  addi x30, x30, 1
  addi x6, x6, -1
  jal x0, .-24
  li x6, 56
  bltu x28, x6, .+264
  add x31, x7, x28
  addi x31, x31, 1
  sub x6, x11, x29
  bltu x6, x28, .+236
  add x10, x31, x10
  mv x12, x31
  li x11, 0
  jalr x0, 0(x1)
  li x6, 183
  sub x7, x5, x6
  addi x6, x7, 1
  add x29, x10, x6
  bltu x11, x29, .+200
  addi x30, x10, 1
  lbu x31, 0(x30)
  beq x31, x0, .+212
  li x28, 0
  mv x6, x7
  beq x6, x0, .+28
  slli x28, x28, 8
  lbu x31, 0(x30)
  or x28, x28, x31
  addi x30, x30, 1
  addi x6, x6, -1
  jal x0, .-24
  li x6, 56
  bltu x28, x6, .+156
  sub x6, x11, x29
  bltu x6, x28, .+136
  add x10, x29, x28
  mv x12, x28
  li x11, 0
  jalr x0, 0(x1)
  li x6, 128
  sub x12, x5, x6
  addi x7, x10, 1
  sub x28, x11, x10
  bgeu x12, x28, .+100
  li x6, 1
  bne x12, x6, .+16
  lbu x6, 0(x7)
  li x29, 128
  bltu x6, x29, .+116
  add x10, x7, x12
  li x11, 0
  jalr x0, 0(x1)
  addi x10, x10, 1
  li x12, 1
  li x11, 0
  jalr x0, 0(x1)
  li x6, 192
  sub x31, x5, x6
  addi x31, x31, 1
  sub x6, x11, x10
  bltu x6, x31, .+32
  add x10, x31, x10
  mv x12, x31
  li x11, 0
  jalr x0, 0(x1)
  li x11, 2
  li x12, 0
  jalr x0, 0(x1)
  li x11, 3
  li x12, 0
  jalr x0, 0(x1)
  li x11, 4
  li x12, 0
  jalr x0, 0(x1)
  li x11, 5
  li x12, 0
  jalr x0, 0(x1)
  li x11, 6
  li x12, 0
  jalr x0, 0(x1)
