blq_copy:
  li x7, 72
  ld x28, 0(x10)
  sd x28, 0(x11)
  addi x10, x10, 8
  addi x11, x11, 8
  addi x7, x7, -1
  bne x7, x0, .-20
  jalr x0, 0(x1)
