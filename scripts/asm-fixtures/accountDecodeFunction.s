account_decode:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  mv x20, x14
  mv x21, x15
  mv x10, x8
  mv x11, x9
  li x12, 0
  la x13, ad_offset
  la x14, ad_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+464
  la x5, ad_length
  ld x6, 0(x5)
  la x5, ad_offset
  ld x28, 0(x5)
  add x28, x8, x28
  beq x6, x0, .+24
  lbu x29, 0(x28)
  bne x29, x0, .+16
  addi x28, x28, 1
  addi x6, x6, -1
  jal x0, .-20
  li x7, 8
  bltu x7, x6, .+404
  li x7, 0
  beq x6, x0, .+28
  slli x7, x7, 8
  lbu x29, 0(x28)
  or x7, x7, x29
  addi x28, x28, 1
  addi x6, x6, -1
  jal x0, .-24
  sd x7, 0(x18)
  mv x10, x8
  mv x11, x9
  li x12, 1
  la x13, ad_offset
  la x14, ad_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+332
  la x5, ad_length
  ld x6, 0(x5)
  la x5, ad_offset
  ld x28, 0(x5)
  add x28, x8, x28
  beq x6, x0, .+24
  lbu x29, 0(x28)
  bne x29, x0, .+16
  addi x28, x28, 1
  addi x6, x6, -1
  jal x0, .-20
  li x7, 32
  bltu x7, x6, .+272
  sd x0, 0(x19)
  sd x0, 8(x19)
  sd x0, 16(x19)
  sd x0, 24(x19)
  sub x7, x7, x6
  add x29, x19, x7
  beq x6, x0, .+28
  lbu x30, 0(x28)
  sb x30, 0(x29)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x6, x6, -1
  jal x0, .-24
  mv x10, x8
  mv x11, x9
  li x12, 2
  la x13, ad_offset
  la x14, ad_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+184
  la x5, ad_length
  ld x6, 0(x5)
  li x7, 32
  bne x6, x7, .+204
  la x5, ad_offset
  ld x28, 0(x5)
  add x28, x8, x28
  lbu x29, 0(x28)
  sb x29, 0(x20)
  addi x28, x28, 1
  addi x20, x20, 1
  addi x6, x6, -1
  bne x6, x0, .-20
  nop
  nop
  mv x10, x8
  mv x11, x9
  li x12, 3
  la x13, ad_offset
  la x14, ad_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+80
  la x5, ad_length
  ld x6, 0(x5)
  li x7, 32
  bne x6, x7, .+152
  la x5, ad_offset
  ld x28, 0(x5)
  add x28, x8, x28
  lbu x29, 0(x28)
  sb x29, 0(x21)
  addi x28, x28, 1
  addi x21, x21, 1
  addi x6, x6, -1
  bne x6, x0, .-20
  nop
  nop
  li x10, 0
  jal x0, .+8
  li x10, 1
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
  beq x6, x0, .+8
  jal x0, .-44
  la x5, iw_empty_trie_root
  ld x7, 0(x5)
  sd x7, 0(x20)
  ld x7, 8(x5)
  sd x7, 8(x20)
  ld x7, 16(x5)
  sd x7, 16(x20)
  ld x7, 24(x5)
  sd x7, 24(x20)
  jal x0, .-200
  beq x6, x0, .+8
  jal x0, .-96
  la x5, aie_empty_code_hash
  ld x7, 0(x5)
  sd x7, 0(x21)
  ld x7, 8(x5)
  sd x7, 8(x21)
  ld x7, 16(x5)
  sd x7, 16(x21)
  ld x7, 24(x5)
  sd x7, 24(x21)
  jal x0, .-148
