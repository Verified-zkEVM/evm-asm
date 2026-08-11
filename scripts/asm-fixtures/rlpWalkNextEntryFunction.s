rlp_walk_next:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sub x5, x11, x10
  slli x8, x5, 1
  li x9, 0
  jal x1, rlp_walk_next_shared
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x1, 0(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
