chain_validate_post_merge_full:
  addi x2, x2, -56
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
  li x5, 1
  sd x5, 0(x19)
  sd x0, 0(x20)
  li x21, 0
  beq x21, x8, .+488
  la x5, cvpmf_iter_ptr
  sd x18, 0(x5)
  la x5, cvpmf_iter_i
  sd x21, 0(x5)
  slli x28, x21, 3
  add x28, x9, x28
  ld x11, 0(x28)
  mv x10, x18
  li x12, 7
  la x13, cvpmf_field
  jal x1, rlp_field_to_u64_strict
  bne x10, x0, .+408
  la x5, cvpmf_field
  ld x6, 0(x5)
  bne x6, x0, .+288
  la x5, cvpmf_iter_ptr
  ld x18, 0(x5)
  la x5, cvpmf_iter_i
  ld x21, 0(x5)
  slli x28, x21, 3
  add x28, x9, x28
  ld x11, 0(x28)
  mv x10, x18
  li x12, 14
  la x13, cvpmf_field
  jal x1, rlp_field_to_u64_strict
  bne x10, x0, .+332
  la x5, cvpmf_field
  ld x6, 0(x5)
  bne x6, x0, .+236
  la x5, cvpmf_iter_ptr
  ld x18, 0(x5)
  la x5, cvpmf_iter_i
  ld x21, 0(x5)
  slli x28, x21, 3
  add x28, x9, x28
  ld x11, 0(x28)
  mv x10, x18
  li x12, 1
  la x13, cvpmf_offset
  la x14, cvpmf_length
  jal x1, rlp_list_nth_item
  bne x10, x0, .+248
  la x5, cvpmf_length
  ld x6, 0(x5)
  li x7, 32
  bne x6, x7, .+196
  la x5, cvpmf_iter_ptr
  ld x18, 0(x5)
  la x5, cvpmf_iter_i
  ld x21, 0(x5)
  la x5, cvpmf_offset
  ld x6, 0(x5)
  add x7, x18, x6
  la x28, cvpmf_empty_hash
  ld x29, 0(x7)
  ld x30, 0(x28)
  bne x29, x30, .+112
  ld x29, 8(x7)
  ld x30, 8(x28)
  bne x29, x30, .+100
  ld x29, 16(x7)
  ld x30, 16(x28)
  bne x29, x30, .+88
  ld x29, 24(x7)
  ld x30, 24(x28)
  bne x29, x30, .+76
  slli x28, x21, 3
  add x28, x9, x28
  ld x29, 0(x28)
  add x18, x18, x29
  addi x21, x21, 1
  jal x0, .-360
  slli x7, x21, 2
  ori x7, x7, 1
  sd x0, 0(x19)
  sd x7, 0(x20)
  li x10, 0
  jal x0, .+108
  slli x7, x21, 2
  ori x7, x7, 2
  sd x0, 0(x19)
  sd x7, 0(x20)
  li x10, 0
  jal x0, .+84
  slli x7, x21, 2
  ori x7, x7, 3
  sd x0, 0(x19)
  sd x7, 0(x20)
  li x10, 0
  jal x0, .+60
  la x5, cvpmf_iter_i
  ld x6, 0(x5)
  slli x7, x6, 2
  ori x7, x7, 3
  sd x7, 0(x20)
  li x10, 3
  jal x0, .+28
  la x5, cvpmf_iter_i
  ld x6, 0(x5)
  sd x6, 0(x20)
  jal x0, .+8
  li x10, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  addi x2, x2, 56
  jalr x0, 0(x1)
