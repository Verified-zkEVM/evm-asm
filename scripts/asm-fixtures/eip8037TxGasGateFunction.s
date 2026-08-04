eip8037_tx_gas_gate:
  addi x2, x2, -112
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
  sd x25, 80(x2)
  sd x26, 88(x2)
  sd x27, 96(x2)
  mv x8, x10
  mv x19, x13
  li x20, 0
  la x5, bsg_min_block_gas
  sd x0, 0(x5)
  la x5, bsg_exact_state_ok
  sd x0, 0(x5)
  addi x10, x8, 504
  jal x1, bgv_u32le
  add x21, x8, x10
  addi x10, x8, 508
  jal x1, bgv_u32le
  sub x22, x10, x10
  add x5, x8, x10
  sub x22, x5, x21
  bltu x5, x21, .+2076
  beq x22, x0, .+2072
  mv x10, x21
  jal x1, bgv_u32le
  andi x5, x10, 3
  bne x5, x0, .+2056
  srli x23, x10, 2
  beq x23, x0, .+2048
  li x5, 16
  bltu x5, x23, .+2040
  mv x10, x21
  mv x11, x22
  mv x12, x23
  la x13, bvgr_tx_state_gas
  la x7, teer_records_ptr
  la x28, basr_records
  sd x28, 0(x7)
  la x7, bv_chain_id
  ld x16, 0(x7)
  li x10, 0
  bne x10, x0, .+20
  la x5, bsg_exact_state_ok
  li x6, 1
  sd x6, 0(x5)
  li x24, 0
  la x5, bsg_blob_gas_accum
  sd x0, 0(x5)
  beq x24, x23, .+1944
  slli x5, x24, 2
  add x6, x21, x5
  mv x10, x6
  jal x1, bgv_u32le
  mv x25, x10
  addi x5, x24, 1
  beq x5, x23, .+24
  slli x6, x5, 2
  add x6, x21, x6
  mv x10, x6
  jal x1, bgv_u32le
  jal x0, .+8
  mv x10, x22
  bltu x10, x25, .+1888
  sub x26, x10, x25
  add x25, x21, x25
  mv x10, x25
  mv x11, x26
  la x12, bsg_tx_type
  la x13, bsg_tx_inner
  jal x1, tx_type_dispatch
  bne x10, x0, .+1848
  la x5, bsg_tx_inner
  ld x7, 0(x5)
  bltu x26, x7, .+1832
  add x25, x25, x7
  sub x26, x26, x7
  la x5, bsg_tx_type
  ld x6, 0(x5)
  li x5, 1
  beq x6, x5, .+132
  li x5, 2
  beq x6, x5, .+224
  li x5, 3
  beq x6, x5, .+216
  li x5, 4
  beq x6, x5, .+308
  beq x6, x0, .+8
  jal x0, .+1772
  li x5, 2
  la x6, bsg_gas_field
  sd x5, 0(x6)
  li x5, 3
  la x6, bsg_to_field
  sd x5, 0(x6)
  li x5, 4
  la x6, bsg_value_field
  sd x5, 0(x6)
  li x5, 5
  la x6, bsg_data_field
  sd x5, 0(x6)
  li x5, -1
  la x6, bsg_access_field
  sd x5, 0(x6)
  la x6, bsg_auth_field
  sd x5, 0(x6)
  jal x0, .+300
  li x5, 3
  la x6, bsg_gas_field
  sd x5, 0(x6)
  li x5, 4
  la x6, bsg_to_field
  sd x5, 0(x6)
  li x5, 5
  la x6, bsg_value_field
  sd x5, 0(x6)
  li x5, 6
  la x6, bsg_data_field
  sd x5, 0(x6)
  li x5, 7
  la x6, bsg_access_field
  sd x5, 0(x6)
  li x5, -1
  la x6, bsg_auth_field
  sd x5, 0(x6)
  jal x0, .+200
  li x5, 4
  la x6, bsg_gas_field
  sd x5, 0(x6)
  li x5, 5
  la x6, bsg_to_field
  sd x5, 0(x6)
  li x5, 6
  la x6, bsg_value_field
  sd x5, 0(x6)
  li x5, 7
  la x6, bsg_data_field
  sd x5, 0(x6)
  li x5, 8
  la x6, bsg_access_field
  sd x5, 0(x6)
  li x5, -1
  la x6, bsg_auth_field
  sd x5, 0(x6)
  jal x0, .+100
  li x5, 4
  la x6, bsg_gas_field
  sd x5, 0(x6)
  li x5, 5
  la x6, bsg_to_field
  sd x5, 0(x6)
  li x5, 6
  la x6, bsg_value_field
  sd x5, 0(x6)
  li x5, 7
  la x6, bsg_data_field
  sd x5, 0(x6)
  li x5, 8
  la x6, bsg_access_field
  sd x5, 0(x6)
  li x5, 9
  la x6, bsg_auth_field
  sd x5, 0(x6)
  la x5, bsg_gas_field
  ld x12, 0(x5)
  mv x10, x25
  mv x11, x26
  la x13, bsg_tx_gas
  jal x1, rlp_field_to_u64
  bne x10, x0, .+1344
  la x5, bsg_tx_gas
  ld x6, 0(x5)
  la x5, bsg_value_field
  ld x12, 0(x5)
  mv x10, x25
  mv x11, x26
  la x13, bsg_value_off
  la x14, bsg_value_len
  jal x1, rlp_list_nth_item
  bne x10, x0, .+1288
  la x5, bsg_data_field
  ld x12, 0(x5)
  mv x10, x25
  mv x11, x26
  la x13, bsg_data_off
  la x14, bsg_data_len
  jal x1, rlp_list_nth_item
  bne x10, x0, .+1244
  la x5, bsg_data_off
  ld x6, 0(x5)
  add x6, x25, x6
  la x5, bsg_data_ptr
  sd x6, 0(x5)
  la x5, bsg_to_field
  ld x12, 0(x5)
  mv x10, x25
  mv x11, x26
  la x13, bsg_to_off
  la x14, bsg_to_len
  jal x1, rlp_list_nth_item
  bne x10, x0, .+1172
  la x5, bsg_to_len
  ld x6, 0(x5)
  bne x6, x0, .+24
  la x5, bsg_data_len
  ld x6, 0(x5)
  lui x7, 0x20
  bltu x7, x6, .+1128
  la x5, bsg_access_addrs
  sd x0, 0(x5)
  la x5, bsg_access_slots
  sd x0, 0(x5)
  la x5, bsg_auth_count
  sd x0, 0(x5)
  la x5, bsg_access_field
  ld x6, 0(x5)
  li x7, -1
  beq x6, x7, .+92
  mv x10, x25
  mv x11, x26
  mv x12, x6
  la x13, bsg_access_off
  la x14, bsg_access_len
  jal x1, rlp_list_nth_item
  bne x10, x0, .+1044
  la x5, bsg_access_off
  ld x6, 0(x5)
  add x10, x25, x6
  la x5, bsg_access_len
  ld x11, 0(x5)
  la x12, bsg_access_addrs
  la x13, bsg_access_slots
  jal x1, access_list_count
  bne x10, x0, .+992
  la x5, bsg_auth_field
  ld x6, 0(x5)
  li x7, -1
  beq x6, x7, .+84
  mv x10, x25
  mv x11, x26
  mv x12, x6
  la x13, bsg_auth_off
  la x14, bsg_auth_len
  jal x1, rlp_list_nth_item
  bne x10, x0, .+936
  la x5, bsg_auth_off
  ld x6, 0(x5)
  add x10, x25, x6
  la x5, bsg_auth_len
  ld x11, 0(x5)
  la x12, bsg_auth_count
  jal x1, rlp_list_count_items
  bne x10, x0, .+892
  la x5, bsg_tx_type
  ld x6, 0(x5)
  li x7, 3
  bne x6, x7, .+228
  mv x10, x25
  mv x11, x26
  la x12, tcbg_struct
  jal x1, tx_eip4844_decode
  bne x10, x0, .+840
  la x5, tcbg_struct
  lwu x6, 168(x5)
  lwu x7, 172(x5)
  add x10, x25, x6
  mv x11, x7
  la x12, bsg_blob_count
  jal x1, rlp_list_count_items
  bne x10, x0, .+800
  la x5, bsg_blob_count
  ld x6, 0(x5)
  beq x6, x0, .+784
  li x7, 6
  bltu x7, x6, .+776
  slli x6, x6, 17
  la x5, bsg_blob_gas_accum
  ld x7, 0(x5)
  add x7, x7, x6
  lui x28, 0x2a0
  bltu x28, x7, .+748
  la x5, bsg_blob_gas_accum
  sd x7, 0(x5)
  addi x10, x8, 520
  jal x1, bgv_u64le
  la x11, bsg_blob_price_be
  jal x1, amsterdam_blob_gas_price_u256
  bne x10, x0, .+712
  la x10, tcbg_blob_fee_be
  la x11, bsg_blob_price_be
  la x12, bsg_blob_lt_out
  jal x1, u256_lt_be
  la x5, bsg_blob_lt_out
  ld x5, 0(x5)
  bne x5, x0, .+668
  mv x10, x25
  mv x11, x26
  li x12, 6
  la x13, bsg_blob_count
  jal x1, tx_eip4844_validate_blob_hashes
  bne x10, x0, .+640
  la x5, bsg_tx_type
  ld x6, 0(x5)
  li x7, 4
  beq x6, x7, .+16
  li x7, 3
  beq x6, x7, .+24
  jal x0, .+36
  la x5, bsg_auth_count
  ld x7, 0(x5)
  beq x7, x0, .+592
  la x5, bsg_to_len
  ld x7, 0(x5)
  beq x7, x0, .+576
  li x31, 0
  la x5, bsg_to_len
  ld x6, 0(x5)
  li x7, 20
  bne x6, x7, .+112
  la x5, bv_public_keys_ptr
  ld x5, 0(x5)
  beq x5, x0, .+96
  slli x6, x24, 6
  add x6, x6, x24
  add x5, x5, x6
  addi x10, x5, 1
  la x11, bsg_sender_addr
  jal x1, address_from_pubkey
  la x5, bsg_sender_addr
  la x6, bsg_to_off
  ld x6, 0(x6)
  add x6, x25, x6
  li x7, 20
  beq x7, x0, .+32
  lbu x28, 0(x5)
  lbu x29, 0(x6)
  bne x28, x29, .+24
  addi x5, x5, 1
  addi x6, x6, 1
  addi x7, x7, -1
  jal x0, .-28
  li x31, 1
  li x30, 0
  la x5, bsg_value_len
  ld x6, 0(x5)
  beq x6, x0, .+8
  li x30, 1
  la x5, bsg_data_ptr
  ld x10, 0(x5)
  la x5, bsg_data_len
  ld x11, 0(x5)
  la x5, bsg_to_len
  ld x12, 0(x5)
  sltiu x12, x12, 1
  la x5, bsg_access_addrs
  ld x13, 0(x5)
  la x5, bsg_access_slots
  ld x14, 0(x5)
  la x5, bsg_auth_count
  ld x15, 0(x5)
  la x16, bsg_intrinsic_gas
  la x17, bsg_floor_gas
  addi x2, x2, -16
  sd x30, 0(x2)
  sd x31, 8(x2)
  jal x1, intrinsic_gas_amsterdam_counts
  addi x2, x2, 16
  bne x10, x0, .+312
  la x5, bsg_floor_gas
  ld x6, 0(x5)
  slli x7, x24, 3
  la x28, bv_mtx_calldata
  add x28, x28, x7
  ld x29, 0(x28)
  bgeu x29, x6, .+8
  sd x6, 0(x28)
  la x5, bsg_state_gas
  sd x0, 0(x5)
  la x5, bsg_intrinsic_gas
  ld x27, 0(x5)
  la x5, bsg_tx_gas
  ld x6, 0(x5)
  la x5, bsg_floor_gas
  ld x31, 0(x5)
  mv x5, x27
  bgeu x5, x31, .+8
  mv x5, x31
  lui x29, 0x1000
  bltu x29, x5, .+196
  mv x29, x27
  bgeu x29, x31, .+8
  mv x29, x31
  bltu x6, x29, .+180
  la x30, bsg_min_block_gas
  ld x7, 0(x30)
  bltu x19, x7, .+148
  sub x28, x19, x7
  mv x29, x6
  lui x31, 0x1000
  bgeu x31, x29, .+8
  mv x29, x31
  bltu x28, x29, .+124
  bltu x28, x5, .+120
  add x7, x7, x5
  sd x7, 0(x30)
  bltu x6, x27, .+132
  sub x7, x6, x27
  la x5, bsg_worst_state
  sd x7, 0(x5)
  mv x10, x24
  la x11, bsg_prior_state
  jal x1, eip8037_prior_state_used_exact
  bne x10, x0, .+56
  la x5, bsg_tx_gas
  ld x6, 0(x5)
  la x5, bsg_prior_state
  ld x28, 0(x5)
  bltu x19, x28, .+28
  sub x29, x19, x28
  bltu x29, x6, .+20
  addi x24, x24, 1
  jal x0, .-1916
  li x10, 1
  jal x0, .+24
  li x10, 2
  jal x0, .+16
  li x10, 3
  jal x0, .+8
  li x10, 0
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
  ld x25, 80(x2)
  ld x26, 88(x2)
  ld x27, 96(x2)
  addi x2, x2, 112
  jalr x0, 0(x1)
