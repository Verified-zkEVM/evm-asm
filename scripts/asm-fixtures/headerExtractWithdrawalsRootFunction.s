header_extract_withdrawals_root:
  addi x2, x2, -48
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x10, x8
  mv x11, x9
  jal x1, rlp_walk_init
  bne x12, x0, .+452
  sd x10, 32(x2)
  sd x11, 40(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+428
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+408
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+388
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+368
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+348
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+328
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+308
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+288
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+268
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+248
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+228
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+208
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+188
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+168
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+148
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+128
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+108
  sub x6, x10, x12
  sub x6, x6, x8
  la x5, hewr_offset
  sd x6, 0(x5)
  la x5, hewr_length
  sd x12, 0(x5)
  jal x0, .+4
  la x5, hewr_length
  ld x6, 0(x5)
  li x7, 32
  bne x6, x7, .+60
  la x5, hewr_offset
  ld x28, 0(x5)
  add x28, x8, x28
  lbu x29, 0(x28)
  sb x29, 0(x18)
  addi x28, x28, 1
  addi x18, x18, 1
  addi x6, x6, -1
  bne x6, x0, .-20
  li x10, 0
  jal x0, .+16
.Lhewr_st1:
  li x10, 1
  jal x0, .+8
  li x10, 2
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  addi x2, x2, 48
  jalr x0, 0(x1)