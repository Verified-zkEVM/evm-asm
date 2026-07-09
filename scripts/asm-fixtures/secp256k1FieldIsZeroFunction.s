secf_is_zero32:
  li x5, 32
  mv x6, x10
  beq x5, x0, .+24
  lbu x7, 0(x6)
  bne x7, x0, .+16
  addi x6, x6, 1
  addi x5, x5, -1
  jal x0, .-20
  li x10, 1
  beq x5, x0, .+8
  li x10, 0
  jalr x0, 0(x1)
