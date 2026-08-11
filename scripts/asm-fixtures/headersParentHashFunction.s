headers_parent_hash:
  lbu x5, 0(x10)
  li x6, 192
  bltu x5, x6, .+120
  li x6, 248
  bltu x5, x6, .+36
  li x6, 247
  sub x7, x5, x6
  li x28, 2
  bltu x28, x7, .+96
  addi x7, x7, 1
  add x10, x10, x7
  sub x11, x11, x7
  jal x0, .+12
  addi x10, x10, 1
  addi x11, x11, -1
  li x5, 33
  bltu x11, x5, .+64
  lbu x6, 0(x10)
  li x7, 160
  bne x6, x7, .+52
  li x5, 0
  li x6, 32
  beq x5, x6, .+32
  addi x7, x10, 1
  add x7, x7, x5
  lbu x28, 0(x7)
  add x7, x12, x5
  sb x28, 0(x7)
  addi x5, x5, 1
  jal x0, .-32
  li x10, 0
  jalr x0, 0(x1)
  li x10, 1
  jalr x0, 0(x1)
