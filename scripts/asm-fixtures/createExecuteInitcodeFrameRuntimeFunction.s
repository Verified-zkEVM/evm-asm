create_execute_initcode_frame:
  la x5, create_child_status
  li x6, 4
  sd x6, 0(x5)
  la x5, create_child_return_len
  sd x0, 0(x5)
  la x5, create_child_code_len
  sd x0, 0(x5)
  la x5, create_child_returndata
  la x6, create_child_code
  li x7, 256
  sb x0, 0(x5)
  sb x0, 0(x6)
  addi x5, x5, 1
  addi x6, x6, 1
  addi x7, x7, -1
  bne x7, x0, .-20
  li x5, 0
  la x7, create_child_initcode
  la x28, create_child_stack
  li x29, 0
  li x30, 1024
  la x6, create_child_init_len
  ld x6, 0(x6)
  beq x30, x0, .+600
  addi x30, x30, -1
  bgeu x5, x6, .+532
  add x10, x7, x5
  lbu x31, 0(x10)
  addi x5, x5, 1
  beq x31, x0, .+516
  li x10, 243
  beq x31, x10, .+344
  li x10, 253
  beq x31, x10, .+360
  li x10, 254
  beq x31, x10, .+576
  li x10, 82
  beq x31, x10, .+144
  li x10, 83
  beq x31, x10, .+244
  li x10, 95
  beq x31, x10, .+24
  li x10, 96
  bltu x31, x10, .+544
  li x10, 128
  bgeu x31, x10, .+536
  jal x0, .+12
  li x11, 0
  jal x0, .+72
  addi x12, x31, -95
  add x13, x5, x12
  bltu x6, x13, .+512
  li x11, 0
  beq x12, x0, .+52
  add x13, x7, x5
  lbu x14, 0(x13)
  addi x5, x5, 1
  li x13, 8
  bltu x13, x12, .+20
  slli x11, x11, 8
  or x11, x11, x14
  addi x12, x12, -1
  jal x0, .-36
  bne x14, x0, .+464
  addi x12, x12, -1
  jal x0, .-48
  li x10, 16
  bgeu x29, x10, .+448
  slli x10, x29, 3
  add x10, x28, x10
  sd x11, 0(x10)
  addi x29, x29, 1
  jal x0, .-196
  li x10, 2
  bltu x29, x10, .+420
  addi x29, x29, -1
  slli x10, x29, 3
  add x10, x28, x10
  ld x11, 0(x10)
  addi x29, x29, -1
  slli x10, x29, 3
  add x10, x28, x10
  ld x12, 0(x10)
  li x10, 224
  bltu x10, x11, .+380
  la x13, create_child_returndata
  add x13, x13, x11
  li x14, 24
  sb x0, 0(x13)
  addi x13, x13, 1
  addi x14, x14, -1
  bne x14, x0, .-12
  li x14, 56
  srl x15, x12, x14
  sb x15, 0(x13)
  addi x13, x13, 1
  addi x14, x14, -8
  bge x14, x0, .-16
  jal x0, .-304
  li x10, 2
  bltu x29, x10, .+312
  addi x29, x29, -1
  slli x10, x29, 3
  add x10, x28, x10
  ld x11, 0(x10)
  addi x29, x29, -1
  slli x10, x29, 3
  add x10, x28, x10
  ld x12, 0(x10)
  li x10, 255
  bltu x10, x11, .+272
  la x13, create_child_returndata
  add x13, x13, x11
  sb x12, 0(x13)
  jal x0, .-372
  li x16, 2
  la x17, create_child_code_len
  la x15, create_child_code
  jal x0, .+28
  li x16, 3
  la x17, create_child_return_len
  la x15, create_child_returndata
  jal x0, .+4
  li x10, 2
  bltu x29, x10, .+196
  addi x29, x29, -1
  slli x10, x29, 3
  add x10, x28, x10
  ld x11, 0(x10)
  addi x29, x29, -1
  slli x10, x29, 3
  add x10, x28, x10
  ld x12, 0(x10)
  li x10, 256
  bltu x10, x12, .+156
  add x10, x11, x12
  bltu x10, x11, .+148
  li x13, 256
  bltu x13, x10, .+140
  sd x12, 0(x17)
  beq x12, x0, .+52
  la x13, create_child_returndata
  add x13, x13, x11
  mv x14, x12
  lbu x10, 0(x13)
  sb x10, 0(x15)
  addi x13, x13, 1
  addi x15, x15, 1
  addi x14, x14, -1
  bne x14, x0, .-20
  jal x0, .+8
  li x16, 2
  li x10, 2
  bne x16, x10, .+32
  la x11, create_child_returndata
  li x12, 256
  sb x0, 0(x11)
  addi x11, x11, 1
  addi x12, x12, -1
  bne x12, x0, .-12
  la x10, create_child_status
  sd x16, 0(x10)
  li x10, 0
  jalr x0, 0(x1)
  la x10, create_child_status
  li x11, 5
  sd x11, 0(x10)
  li x10, 5
  jalr x0, 0(x1)
  la x10, create_child_status
  li x11, 4
  sd x11, 0(x10)
  li x10, 4
  jalr x0, 0(x1)
