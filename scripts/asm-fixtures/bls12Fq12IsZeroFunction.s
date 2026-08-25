blq_is_zero:
  li x5, 72
  li x6, 0
  beq x5, x0, .+24
  ld x7, 0(x10)
  or x6, x6, x7
  addi x10, x10, 8
  addi x5, x5, -1
  jal x0, .-20
  sltiu x10, x6, 1
  jalr x0, 0(x1)
