wcidx_swap_records:
  beq x10, x11, .+44
  li x31, 6
  beq x31, x0, .+36
  ld x5, 0(x10)
  ld x6, 0(x11)
  sd x6, 0(x10)
  sd x5, 0(x11)
  addi x10, x10, 8
  addi x11, x11, 8
  addi x31, x31, -1
  jal x0, .-32
  jalr x0, 0(x1)
