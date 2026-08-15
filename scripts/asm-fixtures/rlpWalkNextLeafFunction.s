rlp_walk_next_leaf:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x10, 8(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+32
  sub x5, x10, x12
  ld x6, 8(x2)
  bne x5, x6, .+20
  lbu x7, 0(x5)
  li x28, 192
  bltu x7, x28, .+8
  li x11, 8
  ld x1, 0(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
