header_extended_decode_arity_check:
  addi x2, x2, -96
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  mv x8, x10
  mv x9, x11
  mv x11, x9
  mv x10, x8
  addi x12, x2, 64
  jal x1, rlp_list_count_items
  bne x10, x0, .+380
  ld x20, 64(x2)
  mv x10, x8
  mv x11, x9
  jal x1, rlp_walk_init
  bne x12, x0, .+360
  mv x18, x10
  mv x19, x11
  li x5, 21
  beq x20, x5, .+12
  li x5, 23
  bne x20, x5, .+336
  li x21, 0
  beq x21, x20, .+320
  mv x10, x18
  mv x11, x19
  jal x1, rlp_walk_next_leaf
  bne x11, x0, .+312
  sub x22, x10, x12
  mv x18, x10
  li x5, 0
  beq x21, x5, .+176
  li x5, 1
  beq x21, x5, .+168
  li x5, 3
  beq x21, x5, .+160
  li x5, 4
  beq x21, x5, .+152
  li x5, 5
  beq x21, x5, .+144
  li x5, 13
  beq x21, x5, .+136
  li x5, 16
  beq x21, x5, .+128
  li x5, 19
  beq x21, x5, .+120
  li x5, 20
  beq x21, x5, .+112
  li x5, 21
  beq x21, x5, .+104
  li x5, 2
  beq x21, x5, .+108
  li x5, 6
  beq x21, x5, .+112
  li x5, 14
  beq x21, x5, .+116
  li x5, 11
  beq x21, x5, .+136
  li x5, 17
  beq x21, x5, .+128
  li x5, 18
  beq x21, x5, .+120
  li x5, 22
  beq x21, x5, .+112
  li x5, 7
  beq x21, x5, .+104
  li x5, 8
  beq x21, x5, .+96
  li x5, 9
  beq x21, x5, .+88
  li x5, 10
  beq x21, x5, .+80
  li x5, 15
  beq x21, x5, .+92
  jal x0, .+108
  li x5, 32
  bne x12, x5, .+116
  jal x0, .+96
  li x5, 20
  bne x12, x5, .+104
  jal x0, .+84
  li x5, 256
  bne x12, x5, .+92
  jal x0, .+72
  li x5, 8
  bne x12, x5, .+80
  jal x0, .+60
  beq x12, x0, .+56
  lbu x5, 0(x22)
  beq x5, x0, .+64
  jal x0, .+44
  mv x10, x22
  mv x11, x12
  jal x1, rlp_content_to_u64_strict
  bne x11, x0, .+44
  jal x0, .+24
  mv x10, x22
  mv x11, x12
  addi x12, x2, 64
  jal x1, rlp_content_to_u256_be_strict
  bne x10, x0, .+20
  addi x21, x21, 1
  jal x0, .-316
  li x10, 0
  jal x0, .+8
  li x10, 1
  ld x22, 56(x2)
  ld x21, 48(x2)
  ld x20, 40(x2)
  ld x19, 32(x2)
  ld x18, 24(x2)
  ld x9, 16(x2)
  ld x8, 8(x2)
  ld x1, 0(x2)
  addi x2, x2, 96
  jalr x0, 0(x1)
