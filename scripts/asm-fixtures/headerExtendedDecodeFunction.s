header_extended_decode:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  mv x8, x10
  mv x18, x12
  jal x1, rlp_walk_init
  bne x12, x0, .+628
  mv x9, x11
  mv x19, x10
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+600
  li x5, 32
  bne x12, x5, .+592
  sub x28, x10, x12
  mv x29, x18
  li x5, 32
  lbu x6, 0(x28)
  sb x6, 0(x29)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x5, x5, -1
  bne x5, x0, .-20
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+536
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+516
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+496
  li x5, 32
  bne x12, x5, .+488
  sub x28, x10, x12
  addi x29, x18, 32
  li x5, 32
  lbu x6, 0(x28)
  sb x6, 0(x29)
  addi x28, x28, 1
  addi x29, x29, 1
  addi x5, x5, -1
  bne x5, x0, .-20
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+432
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+412
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+392
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+372
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+352
  sub x10, x10, x12
  mv x11, x12
  jal x1, rlp_content_to_u64_strict
  bne x11, x0, .+336
  sd x10, 64(x18)
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+312
  sub x10, x10, x12
  mv x11, x12
  jal x1, rlp_content_to_u64_strict
  bne x11, x0, .+296
  sd x10, 80(x18)
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+272
  sub x10, x10, x12
  mv x11, x12
  jal x1, rlp_content_to_u64_strict
  bne x11, x0, .+256
  sd x10, 88(x18)
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+232
  sub x10, x10, x12
  mv x11, x12
  jal x1, rlp_content_to_u64_strict
  bne x11, x0, .+216
  sd x10, 72(x18)
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+192
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+172
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+152
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+132
  sub x10, x10, x12
  mv x11, x12
  addi x12, x18, 96
  jal x1, rlp_content_to_u256_be_strict
  bne x10, x0, .+112
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+92
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+72
  sub x10, x10, x12
  mv x11, x12
  jal x1, rlp_content_to_u64_strict
  bne x11, x0, .+56
  sd x10, 128(x18)
  mv x10, x19
  mv x11, x9
  jal x1, rlp_walk_next
  mv x19, x10
  bne x11, x0, .+32
  sub x10, x10, x12
  mv x11, x12
  jal x1, rlp_content_to_u64_strict
  bne x11, x0, .+16
  sd x10, 136(x18)
  li x10, 0
  jal x0, .+8
  li x10, 1
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
