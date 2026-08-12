wcidx_cmp32:
  li x5, 32
  beq x5, x0, .+44
  lbu x6, 0(x10)
  lbu x7, 0(x11)
  bltu x6, x7, .+24
  bltu x7, x6, .+36
  addi x10, x10, 1
  addi x11, x11, 1
  addi x5, x5, -1
  jal x0, .-32
  li x10, 0
  jalr x0, 0(x1)
  li x10, 1
  jalr x0, 0(x1)
  li x10, 2
  jalr x0, 0(x1)
