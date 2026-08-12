eip7702_authority_asof:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x13, 32(x2)
  sd x14, 40(x2)
  sd x15, 48(x2)
  mv x8, x10
  li x18, 0
  addi x11, x2, 56
  addi x12, x2, 48
  mv x10, x8
  jal x1, account_writes_auth_current
  li x5, 1
  bne x10, x5, .+424
  ld x9, 56(x2)
  mv x10, x8
  addi x11, x2, 56
  jal x1, account_writes_latest_nonce_tx
  beq x10, x0, .+8
  ld x9, 56(x2)
  mv x10, x8
  addi x11, x2, 56
  addi x12, x2, 48
  jal x1, account_writes_auth_block
  beq x10, x0, .+88
  li x5, 2
  beq x10, x5, .+64
  beq x12, x0, .+60
  li x5, 23
  bne x12, x5, .+52
  lbu x5, 0(x11)
  li x6, 239
  bne x5, x6, .+40
  lbu x5, 1(x11)
  li x6, 1
  bne x5, x6, .+28
  lbu x5, 2(x11)
  bne x5, x0, .+20
  mv x11, x9
  li x12, 1
  li x10, 1
  jal x0, .+812
  .L77as_deleg_empty_target:
  mv x11, x9
  li x12, 0
  li x10, 1
  jal x0, .+796
  la x5, sv_pre_rlp_ptr
  ld x10, 0(x5)
  la x5, sv_pre_rlp_len
  ld x11, 0(x5)
  mv x12, x8
  la x5, bv_witness_state_ptr
  ld x13, 0(x5)
  la x5, bv_witness_state_len
  ld x14, 0(x5)
  la x5, svf_codes_ptr
  ld x15, 0(x5)
  la x5, svf_codes_len
  ld x16, 0(x5)
  jal x1, code_at_header_state_root
  beq x10, x0, .L77as_deleg_code_target
  li x5, 1
  beq x10, x5, .-104
  li x5, 5
  bne x10, x5, .L77as_header_reject_target
  la x5, cahsr_acct_struct
  la x6, chahsr_empty_code_hash
  ld x7, 72(x5)
  ld x10, 0(x6)
  bne x7, x10, .L77as_header_reject_target
  ld x7, 80(x5)
  ld x10, 8(x6)
  bne x7, x10, .L77as_header_reject_target
  ld x7, 88(x5)
  ld x10, 16(x6)
  bne x7, x10, .L77as_header_reject_target
  ld x7, 96(x5)
  ld x10, 24(x6)
  bne x7, x10, .L77as_header_reject_target
  jal x0, .L77as_deleg_empty_target
  .L77as_header_reject_target:
  mv x11, x9
  li x12, 0
  li x10, 2
  jal x0, .+616
  .L77as_deleg_code_target:
  la x5, cahsr_code_length
  ld x5, 0(x5)
  beq x5, x0, .-208
  li x6, 23
  bne x5, x6, .-216
  la x5, svf_codes_ptr
  ld x5, 0(x5)
  la x6, cahsr_code_offset
  ld x6, 0(x6)
  add x5, x5, x6
  lbu x6, 0(x5)
  li x7, 239
  bne x6, x7, .-256
  lbu x6, 1(x5)
  li x7, 1
  bne x6, x7, .-268
  lbu x6, 2(x5)
  bne x6, x0, .-276
  mv x11, x9
  li x12, 1
  li x10, 1
  jal x0, .+516
  li x5, 2
  beq x10, x5, .+496
  mv x10, x8
  addi x11, x2, 56
  li x12, 20
  jal x1, account_writes_latest_nonce_tx
  beq x10, x0, .+16
  ld x9, 56(x2)
  li x18, 1
  jal x0, .+32
  mv x10, x8
  addi x11, x2, 56
  li x12, 21
  jal x1, account_writes_latest_nonce_block
  beq x10, x0, .+12
  ld x9, 56(x2)
  li x18, 1
  la x5, sv_pre_rlp_ptr
  ld x10, 0(x5)
  la x5, sv_pre_rlp_len
  ld x11, 0(x5)
  mv x12, x8
  li x13, 20
  la x5, bv_witness_state_ptr
  ld x14, 0(x5)
  la x5, bv_witness_state_len
  ld x15, 0(x5)
  la x16, teer_pre_acct
  jal x1, account_at_header_state_root
  beq x10, x0, .+28
  li x5, 1
  beq x10, x5, .+356
  li x10, 2
  li x11, 0
  li x12, 0
  jal x0, .+352
  bne x18, x0, .+16
  la x5, teer_pre_acct
  ld x11, 0(x5)
  la x5, sv_pre_rlp_ptr
  ld x10, 0(x5)
  la x5, sv_pre_rlp_len
  ld x11, 0(x5)
  mv x12, x8
  la x5, bv_witness_state_ptr
  ld x13, 0(x5)
  la x5, bv_witness_state_len
  ld x14, 0(x5)
  la x5, svf_codes_ptr
  ld x15, 0(x5)
  la x5, svf_codes_len
  ld x16, 0(x5)
  jal x1, code_at_header_state_root
  beq x10, x0, .L77as_code_target
  li x5, 1
  beq x10, x5, .+200
  li x5, 5
  bne x10, x5, .L77as_code_reject_target
  la x5, cahsr_acct_struct
  la x6, chahsr_empty_code_hash
  ld x7, 72(x5)
  ld x10, 0(x6)
  bne x7, x10, .L77as_code_reject_target
  ld x7, 80(x5)
  ld x10, 8(x6)
  bne x7, x10, .L77as_code_reject_target
  ld x7, 88(x5)
  ld x10, 16(x6)
  bne x7, x10, .L77as_code_reject_target
  ld x7, 96(x5)
  ld x10, 24(x6)
  bne x7, x10, .L77as_code_reject_target
  jal x0, .L77as_live_empty_target
  .L77as_code_reject_target:
  li x10, 2
  li x11, 0
  li x12, 0
  jal x0, .+156
  .L77as_code_target:
  la x5, cahsr_code_length
  ld x5, 0(x5)
  beq x5, x0, .+96
  li x6, 23
  bne x5, x6, .+72
  la x5, svf_codes_ptr
  ld x5, 0(x5)
  la x6, cahsr_code_offset
  ld x6, 0(x6)
  add x5, x5, x6
  lbu x6, 0(x5)
  li x7, 239
  bne x6, x7, .+32
  lbu x6, 1(x5)
  li x7, 1
  bne x6, x7, .+20
  lbu x6, 2(x5)
  bne x6, x0, .+12
  li x12, 1
  jal x0, .+24
  li x10, 3
  li x11, 0
  li x12, 0
  jal x0, .+48
  .L77as_live_empty_target:
  li x12, 0
  bne x18, x0, .+16
  la x5, teer_pre_acct
  ld x9, 0(x5)
  mv x11, x9
  li x10, 1
  jal x0, .+16
  li x10, 0
  li x11, 0
  li x12, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x13, 32(x2)
  ld x14, 40(x2)
  ld x15, 48(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
