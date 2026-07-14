header_extract_receipts_root:
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
  bne x12, x0, .+240
  sd x10, 32(x2)
  sd x11, 40(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+216
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+196
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+176
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+156
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+136
  sd x10, 32(x2)
  ld x10, 32(x2)
  ld x11, 40(x2)
  jal x1, rlp_walk_next
  bne x11, x0, .+116
  sub x6, x10, x12
  sub x6, x6, x8
  la x5, herr_offset
  sd x6, 0(x5)
  la x5, herr_length
  sd x12, 0(x5)
  jal x0, .+4
  la x5, herr_length
  ld x6, 0(x5)
  li x7, 32
  bne x6, x7, .+68
  la x5, herr_offset
  ld x28, 0(x5)
  add x28, x8, x28
  ld x29, 0(x28)
  sd x29, 0(x18)
  ld x29, 8(x28)
  sd x29, 8(x18)
  ld x29, 16(x28)
  sd x29, 16(x18)
  ld x29, 24(x28)
  sd x29, 24(x18)
  li x10, 0
  jal x0, .+16
  li x10, 1
  jal x0, .+8
  li x10, 2
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  addi x2, x2, 48
  jalr x0, 0(x1)
