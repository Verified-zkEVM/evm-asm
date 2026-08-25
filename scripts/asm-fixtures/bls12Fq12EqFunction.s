blq_eq:
  li x5, 72
  beq x5, x0, .+32
  ld x6, 0(x10)
  ld x7, 0(x11)
  bne x6, x7, .+28
  addi x10, x10, 8
  addi x11, x11, 8
  addi x5, x5, -1
  jal x0, .-28
  li x10, 1
  jalr x0, 0(x1)
  li x10, 0
  jalr x0, 0(x1)
