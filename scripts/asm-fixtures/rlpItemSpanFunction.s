rlp_item_span:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  mv x8, x10
  add x9, x10, x11
  mv x18, x12
  mv x19, x13
  mv x20, x14
  bgeu x8, x9, .+128
  lbu x5, 0(x8)
  li x6, 192
  bltu x5, x6, .+116
  li x6, 248
  bltu x5, x6, .+40
  li x6, 247
  sub x7, x5, x6
  addi x7, x7, 1
  add x21, x8, x7
  bgeu x21, x9, .+88
  addi x7, x8, 1
  lbu x7, 0(x7)
  beq x7, x0, .+76
  jal x0, .+8
  addi x21, x8, 1
  li x22, 0
  beq x22, x18, .+28
  bgeu x21, x9, .+56
  mv x10, x21
  jal ra, rlp_item_size
  add x21, x21, x10
  addi x22, x22, 1
  jal x0, .-24
  bgeu x21, x9, .+32
  mv x10, x21
  jal ra, rlp_item_size
  sub x6, x21, x8
  sd x6, 0(x19)
  sd x10, 0(x20)
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
  ld x22, 56(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
