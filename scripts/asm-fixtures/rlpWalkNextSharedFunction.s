rlp_walk_next_shared:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x10, 8(x2)
  sd x11, 16(x2)
  jal x1, rlp_walk_next_core
  sd x10, 24(x2)
  sd x11, 32(x2)
  sd x12, 40(x2)
  bne x11, x0, .+152
  li x5, 2
  bltu x8, x5, .+128
  addi x8, x8, -2
  ld x5, 8(x2)
  lbu x6, 0(x5)
  li x7, 192
  bltu x6, x7, .+124
  li x7, 1024
  bgeu x9, x7, .+100
  addi x9, x9, 1
  ld x11, 24(x2)
  li x7, 248
  bltu x6, x7, .+64
  li x7, 247
  sub x28, x6, x7
  mv x13, x28
  addi x29, x5, 1
  li x30, 0
  beq x28, x0, .+28
  slli x30, x30, 8
  lbu x31, 0(x29)
  or x30, x30, x31
  addi x29, x29, 1
  addi x28, x28, -1
  jal x0, .-24
  add x12, x5, x13
  addi x12, x12, 1
  jal x0, .+8
  addi x12, x5, 1
  mv x10, x12
  jal x1, rlp_validate_payload
  addi x9, x9, -1
  beq x10, x0, .+20
  ld x10, 8(x2)
  li x11, 7
  li x12, 0
  jal x0, .+16
  ld x10, 24(x2)
  ld x11, 32(x2)
  ld x12, 40(x2)
  ld x1, 0(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
