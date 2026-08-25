code_at_header_state_root:
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
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  mv x20, x14
  mv x21, x15
  mv x22, x16
  mv x10, x8
  mv x11, x9
  la x12, cahsr_state_root
  jal x1, header_extract_state_root
  beq x10, x0, .+12
  li x10, 4
  jal x0, .+112
  mv x10, x18
  li x11, 20
  la x12, cahsr_state_root
  mv x13, x19
  mv x14, x20
  la x15, cahsr_acct_struct
  jal x1, account_at_address
  beq x10, x0, .+20
  li x5, 4
  bne x10, x5, .+64
  li x10, 6
  jal x0, .+56
  mv x10, x21
  mv x11, x22
  la x12, cahsr_acct_struct
  addi x12, x12, 72
  la x13, cahsr_code_offset
  la x14, cahsr_code_length
  mv x15, x18
  jal x1, code_read_fetch
  beq x10, x0, .+8
  li x10, 5
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  ld x22, 56(x2)
  ld x23, 64(x2)
  addi x2, x2, 80
  jalr x0, 0(x1)
