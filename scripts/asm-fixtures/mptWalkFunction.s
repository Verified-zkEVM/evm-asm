mpt_walk:
  addi x2, x2, -80
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  sd x23, 64(x2)
  sd x24, 72(x2)
  mv x8, x11
  mv x9, x12
  mv x18, x13
  mv x19, x14
  mv x20, x15
  mv x21, x16
  la x5, mw_lookup_hash
  ld x6, 0(x10)
  sd x6, 0(x5)
  ld x6, 8(x10)
  sd x6, 8(x5)
  ld x6, 16(x10)
  sd x6, 16(x5)
  ld x6, 24(x10)
  sd x6, 24(x5)
  mv x10, x8
  mv x11, x9
  la x12, mw_lookup_hash
  la x13, mw_lookup_offset
  la x14, mw_lookup_length
  jal x1, witness_lookup_by_hash
  bne x10, x0, .+1044
  la x5, mw_lookup_offset
  ld x6, 0(x5)
  add x23, x8, x6
  la x5, mw_lookup_length
  ld x24, 0(x5)
  li x22, 0
  mv x10, x23
  mv x11, x24
  jal x1, mpt_node_kind
  beq x10, x0, .+24
  li x5, 1
  beq x10, x5, .+300
  li x5, 2
  beq x10, x5, .+672
  jal x0, .+988
  beq x22, x19, .+228
  add x5, x18, x22
  lbu x6, 0(x5)
  mv x10, x23
  mv x11, x24
  mv x12, x6
  la x13, mw_child_offset
  la x14, mw_child_length
  jal x1, rlp_list_nth_item
  addi x22, x22, 1
  bne x10, x0, .+936
  la x5, mw_child_length
  ld x6, 0(x5)
  beq x6, x0, .+908
  li x7, 32
  beq x6, x7, .+28
  la x5, mw_child_offset
  ld x7, 0(x5)
  add x23, x23, x7
  mv x24, x6
  jal x0, .-132
  la x5, mw_child_offset
  ld x6, 0(x5)
  add x7, x23, x6
  la x28, mw_lookup_hash
  ld x29, 0(x7)
  sd x29, 0(x28)
  ld x29, 8(x7)
  sd x29, 8(x28)
  ld x29, 16(x7)
  sd x29, 16(x28)
  ld x29, 24(x7)
  sd x29, 24(x28)
  mv x10, x8
  mv x11, x9
  la x12, mw_lookup_hash
  la x13, mw_lookup_offset
  la x14, mw_lookup_length
  jal x1, witness_lookup_by_hash
  bne x10, x0, .+792
  la x5, mw_lookup_offset
  ld x6, 0(x5)
  add x23, x8, x6
  la x5, mw_lookup_length
  ld x24, 0(x5)
  jal x0, .-260
  mv x10, x23
  mv x11, x24
  li x12, 16
  la x13, mw_value_offset
  la x14, mw_value_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+724
  la x5, mw_value_length
  ld x6, 0(x5)
  beq x6, x0, .+696
  jal x0, .+604
  mv x10, x23
  mv x11, x24
  li x12, 0
  la x13, mw_path_offset
  la x14, mw_path_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+668
  la x5, mw_path_offset
  ld x6, 0(x5)
  add x10, x23, x6
  la x5, mw_path_length
  ld x11, 0(x5)
  la x12, mw_nibble_buf
  la x13, mw_nibble_count
  la x14, mw_is_leaf
  jal x1, hp_decode_nibbles
  bne x10, x0, .+608
  la x5, mw_is_leaf
  ld x6, 0(x5)
  bne x6, x0, .+592
  la x5, mw_nibble_count
  ld x6, 0(x5)
  add x7, x22, x6
  bltu x19, x7, .+560
  la x7, mw_nibble_buf
  add x28, x18, x22
  mv x29, x6
  beq x29, x0, .+32
  lbu x30, 0(x7)
  lbu x31, 0(x28)
  bne x30, x31, .+528
  addi x7, x7, 1
  addi x28, x28, 1
  addi x29, x29, -1
  jal x0, .-28
  add x22, x22, x6
  mv x10, x23
  mv x11, x24
  li x12, 1
  la x13, mw_child_offset
  la x14, mw_child_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+484
  la x5, mw_child_length
  ld x6, 0(x5)
  la x5, mw_child_offset
  ld x7, 0(x5)
  add x28, x23, x7
  li x29, 32
  beq x6, x29, .+16
  mv x23, x28
  mv x24, x6
  jal x0, .-584
  la x29, mw_lookup_hash
  ld x30, 0(x28)
  sd x30, 0(x29)
  ld x30, 8(x28)
  sd x30, 8(x29)
  ld x30, 16(x28)
  sd x30, 16(x29)
  ld x30, 24(x28)
  sd x30, 24(x29)
  mv x10, x8
  mv x11, x9
  la x12, mw_lookup_hash
  la x13, mw_lookup_offset
  la x14, mw_lookup_length
  jal x1, witness_lookup_by_hash
  bne x10, x0, .+356
  la x5, mw_lookup_offset
  ld x6, 0(x5)
  add x23, x8, x6
  la x5, mw_lookup_length
  ld x24, 0(x5)
  jal x0, .-696
  mv x10, x23
  mv x11, x24
  li x12, 0
  la x13, mw_path_offset
  la x14, mw_path_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+288
  la x5, mw_path_offset
  ld x6, 0(x5)
  add x10, x23, x6
  la x5, mw_path_length
  ld x11, 0(x5)
  la x12, mw_nibble_buf
  la x13, mw_nibble_count
  la x14, mw_is_leaf
  jal x1, hp_decode_nibbles
  bne x10, x0, .+228
  la x5, mw_is_leaf
  ld x6, 0(x5)
  li x7, 1
  bne x6, x7, .+208
  la x5, mw_nibble_count
  ld x6, 0(x5)
  sub x7, x19, x22
  bne x6, x7, .+176
  la x7, mw_nibble_buf
  add x28, x18, x22
  mv x29, x6
  beq x29, x0, .+32
  lbu x30, 0(x7)
  lbu x31, 0(x28)
  bne x30, x31, .+144
  addi x7, x7, 1
  addi x28, x28, 1
  addi x29, x29, -1
  jal x0, .-28
  mv x10, x23
  mv x11, x24
  li x12, 1
  la x13, mw_value_offset
  la x14, mw_value_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+104
  la x5, mw_value_length
  ld x6, 0(x5)
  sd x6, 0(x21)
  la x5, mw_value_offset
  ld x7, 0(x5)
  add x7, x23, x7
  mv x28, x20
  li x29, 256
  bltu x29, x6, .+8
  jal x0, .+8
  mv x6, x29
  beq x6, x0, .+28
  lbu x5, 0(x7)
  sb x5, 0(x28)
  addi x7, x7, 1
  addi x28, x28, 1
  addi x6, x6, -1
  jal x0, .-24
  li x10, 0
  jal x0, .+24
  li x10, 1
  sd x0, 0(x21)
  jal x0, .+60
  li x10, 2
  sd x0, 0(x21)
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  ld x22, 56(x2)
  ld x23, 64(x2)
  ld x24, 72(x2)
  addi x2, x2, 80
  jalr x0, 0(x1)
  la x5, mpt_walk
  addi x5, x5, 144
  beq x1, x5, .+24
  addi x5, x5, 264
  beq x1, x5, .+36
  addi x5, x5, 436
  beq x1, x5, .+28
  jal x0, .-80
  li x6, 1
  la x28, mw_lookup_hash
  sd x6, 48(x28)
  jal x0, .-100
  li x6, 2
  la x28, mw_lookup_hash
  sd x6, 48(x28)
  jal x0, .-120
