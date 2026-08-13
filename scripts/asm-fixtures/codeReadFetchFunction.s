code_read_fetch:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x10, 8(x2)
  sd x11, 16(x2)
  sd x12, 24(x2)
  sd x13, 32(x2)
  sd x14, 40(x2)
  sd x15, 48(x2)
  la x5, ecc_empty_code_hash
  li x6, 0
  li x7, 32
  beq x6, x7, .+88
  add x7, x5, x6
  lbu x7, 0(x7)
  add x28, x12, x6
  lbu x28, 0(x28)
  bne x7, x28, .+12
  addi x6, x6, 1
  jal x0, .-32
  la x10, exec_code_effect_log
  la x5, exec_code_effect_count
  ld x11, 0(x5)
  ld x12, 24(x2)
  jal x1, find_code_effect_by_hash
  mv x6, x10
  bne x6, x0, .+60
  ld x15, 48(x2)
  ld x12, 24(x2)
  mv x10, x15
  mv x11, x12
  jal x1, code_read_record
  ld x1, 0(x2)
  ld x10, 8(x2)
  ld x11, 16(x2)
  ld x12, 24(x2)
  ld x13, 32(x2)
  ld x14, 40(x2)
  ld x15, 48(x2)
  addi x2, x2, 64
  jal x0, witness_codes_lookup_by_hash
  ld x7, 40(x6)
  ld x28, 40(x2)
  sd x7, 0(x28)
  addi x7, x6, 48
  ld x28, 8(x2)
  sub x7, x7, x28
  ld x28, 32(x2)
  sd x7, 0(x28)
  ld x1, 0(x2)
  li x10, 0
  addi x2, x2, 64
  jalr x0, 0(x1)
