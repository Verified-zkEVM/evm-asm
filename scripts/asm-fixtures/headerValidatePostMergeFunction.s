header_validate_post_merge:
  addi x2, x2, -48
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  mv x8, x10
  mv x9, x11
  li x20, 0
  jal x1, rlp_walk_init
  bne x12, x0, .+584
  mv x18, x10
  mv x19, x11
  mv x10, x18
  mv x11, x19
  jal x1, rlp_walk_next
  bne x11, x0, .+560
  li x5, 1
  bne x20, x5, .+12
  mv x8, x10
  mv x9, x12
  li x5, 7
  bne x20, x5, .+8
  bne x12, x0, .+508
  mv x18, x10
  addi x20, x20, 1
  li x5, 15
  bne x20, x5, .-56
  li x5, 8
  bne x12, x5, .+492
  sub x6, x10, x12
  lbu x7, 0(x6)
  bne x7, x0, .+480
  lbu x7, 1(x6)
  bne x7, x0, .+472
  lbu x7, 2(x6)
  bne x7, x0, .+464
  lbu x7, 3(x6)
  bne x7, x0, .+456
  lbu x7, 4(x6)
  bne x7, x0, .+448
  lbu x7, 5(x6)
  bne x7, x0, .+440
  lbu x7, 6(x6)
  bne x7, x0, .+432
  lbu x7, 7(x6)
  bne x7, x0, .+424
  li x5, 32
  bne x9, x5, .+424
  sub x6, x8, x9
  la x5, empty_ommers_hash
  lbu x7, 0(x6)
  lbu x28, 0(x5)
  bne x7, x28, .+400
  lbu x7, 1(x6)
  lbu x28, 1(x5)
  bne x7, x28, .+388
  lbu x7, 2(x6)
  lbu x28, 2(x5)
  bne x7, x28, .+376
  lbu x7, 3(x6)
  lbu x28, 3(x5)
  bne x7, x28, .+364
  lbu x7, 4(x6)
  lbu x28, 4(x5)
  bne x7, x28, .+352
  lbu x7, 5(x6)
  lbu x28, 5(x5)
  bne x7, x28, .+340
  lbu x7, 6(x6)
  lbu x28, 6(x5)
  bne x7, x28, .+328
  lbu x7, 7(x6)
  lbu x28, 7(x5)
  bne x7, x28, .+316
  lbu x7, 8(x6)
  lbu x28, 8(x5)
  bne x7, x28, .+304
  lbu x7, 9(x6)
  lbu x28, 9(x5)
  bne x7, x28, .+292
  lbu x7, 10(x6)
  lbu x28, 10(x5)
  bne x7, x28, .+280
  lbu x7, 11(x6)
  lbu x28, 11(x5)
  bne x7, x28, .+268
  lbu x7, 12(x6)
  lbu x28, 12(x5)
  bne x7, x28, .+256
  lbu x7, 13(x6)
  lbu x28, 13(x5)
  bne x7, x28, .+244
  lbu x7, 14(x6)
  lbu x28, 14(x5)
  bne x7, x28, .+232
  lbu x7, 15(x6)
  lbu x28, 15(x5)
  bne x7, x28, .+220
  lbu x7, 16(x6)
  lbu x28, 16(x5)
  bne x7, x28, .+208
  lbu x7, 17(x6)
  lbu x28, 17(x5)
  bne x7, x28, .+196
  lbu x7, 18(x6)
  lbu x28, 18(x5)
  bne x7, x28, .+184
  lbu x7, 19(x6)
  lbu x28, 19(x5)
  bne x7, x28, .+172
  lbu x7, 20(x6)
  lbu x28, 20(x5)
  bne x7, x28, .+160
  lbu x7, 21(x6)
  lbu x28, 21(x5)
  bne x7, x28, .+148
  lbu x7, 22(x6)
  lbu x28, 22(x5)
  bne x7, x28, .+136
  lbu x7, 23(x6)
  lbu x28, 23(x5)
  bne x7, x28, .+124
  lbu x7, 24(x6)
  lbu x28, 24(x5)
  bne x7, x28, .+112
  lbu x7, 25(x6)
  lbu x28, 25(x5)
  bne x7, x28, .+100
  lbu x7, 26(x6)
  lbu x28, 26(x5)
  bne x7, x28, .+88
  lbu x7, 27(x6)
  lbu x28, 27(x5)
  bne x7, x28, .+76
  lbu x7, 28(x6)
  lbu x28, 28(x5)
  bne x7, x28, .+64
  lbu x7, 29(x6)
  lbu x28, 29(x5)
  bne x7, x28, .+52
  lbu x7, 30(x6)
  lbu x28, 30(x5)
  bne x7, x28, .+40
  lbu x7, 31(x6)
  lbu x28, 31(x5)
  bne x7, x28, .+28
  li x10, 0
  jal x0, .+32
  li x10, 1
  jal x0, .+24
  li x10, 2
  jal x0, .+16
  li x10, 3
  jal x0, .+8
  li x10, 4
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  addi x2, x2, 48
  jalr x0, 0(x1)
