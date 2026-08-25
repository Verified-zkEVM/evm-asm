create2_descend:
  addi x2, x2, -48
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  mv x8, x12
  mv x9, x13
  mv x18, x20
  ld x5, 32(x8)
  la x6, create_init_offset
  sd x5, 0(x6)
  ld x5, 64(x8)
  la x6, create_init_size
  sd x5, 0(x6)
  la x6, create_sender_be
  ld x7, 0(x18)
  sd x7, 0(x6)
  ld x7, 8(x18)
  sd x7, 8(x6)
  ld x7, 16(x18)
  sd x7, 16(x6)
  ld x7, 24(x18)
  sd x7, 24(x6)
  addi x7, x8, 127
  la x6, create_salt_be
  li x5, 32
  beq x5, x0, .+28
  lbu x28, 0(x7)
  sb x28, 0(x6)
  addi x7, x7, -1
  addi x6, x6, 1
  addi x5, x5, -1
  jal x0, .-24
  la x10, create_sender_be
  la x11, create_salt_be
  la x5, create_init_offset
  ld x5, 0(x5)
  add x12, x9, x5
  la x5, create_init_size
  ld x13, 0(x5)
  la x14, create_address_be
  jal x1, address_compute_create2
  mv x10, x9
  mv x11, x8
  li x12, 1
  jal x1, create_stage_initcode_frame
  jal x1, create_execute_initcode_frame
  addi x29, x8, 96
  sd x0, 0(x29)
  sd x0, 8(x29)
  sd x0, 16(x29)
  sd x0, 24(x29)
  la x5, create_child_status
  ld x5, 0(x5)
  li x6, 2
  bne x5, x6, .+52
  la x7, create_address_be
  addi x7, x7, 19
  mv x6, x29
  li x5, 20
  beq x5, x0, .+28
  lbu x28, 0(x7)
  sb x28, 0(x6)
  addi x7, x7, -1
  addi x6, x6, 1
  addi x5, x5, -1
  jal x0, .-24
  addi x10, x8, 96
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  addi x2, x2, 48
  jalr x0, 0(x1)
