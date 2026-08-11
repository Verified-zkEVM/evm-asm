address_from_pubkey:
  addi x2, x2, -16
  sd x1, 0(x2)
  sd x8, 8(x2)
  mv x8, x11
  li x11, 64
  la x12, afp_digest
  jal x1, zkvm_keccak256
  la x5, afp_digest
  li x6, 0
  li x7, 20
  beq x6, x7, .+32
  addi x28, x5, 12
  add x28, x28, x6
  lbu x29, 0(x28)
  add x28, x8, x6
  sb x29, 0(x28)
  addi x6, x6, 1
  jal x0, .-32
  li x10, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  addi x2, x2, 16
  jalr x0, 0(x1)
