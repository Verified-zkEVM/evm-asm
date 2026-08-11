address_compute_create:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  la x5, ac_buffer
  li x6, 148
  sb x6, 1(x5)
  li x6, 0
  li x7, 20
  beq x6, x7, .+32
  add x28, x8, x6
  lbu x29, 0(x28)
  addi x28, x5, 2
  add x28, x28, x6
  sb x29, 0(x28)
  addi x6, x6, 1
  jal x0, .-32
  beq x9, x0, .+24
  li x6, 128
  bgeu x9, x6, .+32
  sb x9, 22(x5)
  li x7, 1
  jal x0, .+172
  li x6, 128
  sb x6, 22(x5)
  li x7, 1
  jal x0, .+156
  la x28, ac_nonce_be
  srli x29, x9, 56
  sb x29, 0(x28)
  srli x29, x9, 48
  sb x29, 1(x28)
  srli x29, x9, 40
  sb x29, 2(x28)
  srli x29, x9, 32
  sb x29, 3(x28)
  srli x29, x9, 24
  sb x29, 4(x28)
  srli x29, x9, 16
  sb x29, 5(x28)
  srli x29, x9, 8
  sb x29, 6(x28)
  sb x9, 7(x28)
  li x29, 0
  add x30, x28, x29
  lbu x31, 0(x30)
  bne x31, x0, .+12
  addi x29, x29, 1
  jal x0, .-16
  li x30, 8
  sub x7, x30, x29
  addi x30, x7, 128
  sb x30, 22(x5)
  addi x31, x5, 23
  add x30, x28, x29
  mv x6, x7
  beq x6, x0, .+28
  lbu x29, 0(x30)
  sb x29, 0(x31)
  addi x30, x30, 1
  addi x31, x31, 1
  addi x6, x6, -1
  jal x0, .-24
  addi x7, x7, 1
  addi x6, x7, 21
  addi x28, x6, 192
  sb x28, 0(x5)
  addi x11, x7, 22
  mv x10, x5
  la x12, ac_digest
  jal x1, zkvm_keccak256
  la x5, ac_digest
  li x6, 0
  li x7, 20
  beq x6, x7, .+32
  addi x28, x5, 12
  add x28, x28, x6
  lbu x29, 0(x28)
  add x28, x18, x6
  sb x29, 0(x28)
  addi x6, x6, 1
  jal x0, .-32
  li x10, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
