bal_account_code_at_or_before:
  addi x2, x2, -160
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
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  sd x0, 56(x18)
  sd x0, 64(x18)
  sd x0, 72(x18)
  sd x0, 152(x2)
  mv x10, x8
  mv x11, x9
  li x12, 5
  addi x13, x2, 80
  addi x14, x2, 88
  jal x1, rlp_list_nth_item
  bne x10, x0, .+212
  ld x5, 80(x2)
  add x20, x8, x5
  ld x21, 88(x2)
  mv x10, x20
  mv x11, x21
  addi x12, x2, 96
  jal x1, rlp_list_count_items
  bne x10, x0, .+180
  li x22, 0
  li x23, 0
  ld x5, 96(x2)
  beq x22, x5, .+156
  mv x10, x20
  mv x11, x21
  mv x12, x22
  addi x13, x2, 104
  addi x14, x2, 112
  jal x1, rlp_list_nth_item
  bne x10, x0, .+136
  ld x5, 104(x2)
  add x24, x20, x5
  ld x6, 112(x2)
  mv x10, x24
  mv x11, x6
  li x12, 0
  addi x13, x2, 120
  jal x1, rlp_field_to_u64_strict
  bne x10, x0, .+100
  ld x5, 120(x2)
  bltu x19, x5, .+76
  bltu x5, x23, .+72
  sd x5, 152(x2)
  mv x10, x24
  ld x11, 112(x2)
  li x12, 1
  addi x13, x2, 128
  addi x14, x2, 136
  jal x1, rlp_list_nth_item
  bne x10, x0, .+56
  ld x6, 128(x2)
  add x6, x24, x6
  sub x6, x6, x8
  sd x6, 64(x18)
  ld x6, 136(x2)
  sd x6, 72(x18)
  li x6, 1
  sd x6, 56(x18)
  ld x23, 152(x2)
  addi x22, x22, 1
  jal x0, .-156
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
  ld x22, 56(x2)
  ld x23, 64(x2)
  ld x24, 72(x2)
  addi x2, x2, 160
  jalr x0, 0(x1)
