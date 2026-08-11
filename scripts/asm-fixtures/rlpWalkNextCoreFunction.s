rlp_walk_next_core:
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