address_compute_create2:
  addi x2, x2, -48
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  mv x8, x10
  mv x9, x11
  mv x20, x14
  mv x10, x12
  mv x11, x13
  la x12, ac2_inner_digest
  jal x1, zkvm_keccak256
  la x18, ac2_preimage
  li x5, 255
  sb x5, 0(x18)
  li x5, 0
  li x6, 20
  beq x5, x6, .+32
  add x7, x8, x5
  lbu x28, 0(x7)
  addi x7, x18, 1
  add x7, x7, x5
  sb x28, 0(x7)
  addi x5, x5, 1
  jal x0, .-32
  li x5, 0
  li x6, 32
  beq x5, x6, .+32
  add x7, x9, x5
  lbu x28, 0(x7)
  addi x7, x18, 21
  add x7, x7, x5
  sb x28, 0(x7)
  addi x5, x5, 1
  jal x0, .-32
  la x6, ac2_inner_digest
  li x5, 0
  li x28, 32
  beq x5, x28, .+32
  add x7, x6, x5
  lbu x28, 0(x7)
  addi x7, x18, 53
  add x7, x7, x5
  sb x28, 0(x7)
  addi x5, x5, 1
  jal x0, .-32
  mv x10, x18
  li x11, 85
  la x12, ac2_outer_digest
  jal x1, zkvm_keccak256
  la x5, ac2_outer_digest
  li x6, 0
  li x7, 20
  beq x6, x7, .+32
  addi x28, x5, 12
  add x28, x28, x6
  lbu x29, 0(x28)
  add x28, x20, x6
  sb x29, 0(x28)
  addi x6, x6, 1
  jal x0, .-32
  li x10, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  addi x2, x2, 48
  jalr x0, 0(x1)
