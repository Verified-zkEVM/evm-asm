rlp_item_size:
  lbu x5, 0(x10)
  li x6, 128
  bgeu x5, x6, .+12
  li x10, 1
  jalr x0, 0(x1)
  li x6, 184
  bgeu x5, x6, .+16
  addi x10, x5, -128
  addi x10, x10, 1
  jalr x0, 0(x1)
  li x6, 192
  bgeu x5, x6, .+16
  li x6, 183
  sub x7, x5, x6
  jal x0, .+32
  li x6, 248
  bgeu x5, x6, .+16
  addi x10, x5, -192
  addi x10, x10, 1
  jalr x0, 0(x1)
  li x6, 247
  sub x7, x5, x6
  li x28, 0
  addi x29, x10, 1
  mv x30, x7
  beq x30, x0, .+28
  slli x28, x28, 8
  lbu x31, 0(x29)
  or x28, x28, x31
  addi x29, x29, 1
  addi x30, x30, -1
  jal x0, .-24
  addi x10, x7, 1
  add x10, x10, x28
  jalr x0, 0(x1)
