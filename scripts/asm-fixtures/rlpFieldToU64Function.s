rlp_field_to_u64:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  mv x8, x10
  mv x9, x13
  sd x0, 0(x9)
  la x13, rfu_offset
  la x14, rfu_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+68
  la x5, rfu_offset
  ld x10, 0(x5)
  add x10, x8, x10
  la x5, rfu_length
  ld x11, 0(x5)
  jal x1, rlp_content_to_u64
  bne x11, x0, .+16
  sd x10, 0(x9)
  li x10, 0
  jal x0, .+32
  li x5, 2
  beq x11, x5, .+20
  li x10, 1
  jal x0, .+16
.Lrfu_st1b:
  li x10, 1
  jal x0, .+8
  li x10, 2
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
