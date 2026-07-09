p256_is_zero_n:
  mv x5, x10
  mv x6, x11
  beq x6, x0, .+24
  lbu x7, 0(x5)
  bne x7, x0, .+16
  addi x5, x5, 1
  addi x6, x6, -1
  jal x0, .-20
  li x10, 1
  beq x6, x0, .+8
  li x10, 0
  jalr x0, 0(x1)
