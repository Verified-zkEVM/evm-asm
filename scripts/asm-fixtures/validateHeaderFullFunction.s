validate_header_full:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                   # this_rlp ptr
  mv s1, a1                   # this_rlp_len
  mv s2, a2                   # this_struct (144 B)
  mv s3, a3                   # parent_struct (144 B)
  # Step 1: post_merge check
  mv a0, s0; mv a1, s1
  jal ra, header_validate_post_merge
  beqz a0, .Lvhf_s2
  li t0, 100
  add a0, a0, t0
  j .Lvhf_ret
.Lvhf_s2:
  # Step 2: extra_data length check
  mv a0, s0; mv a1, s1
  jal ra, header_validate_extra_data_length
  beqz a0, .Lvhf_s3
  li t0, 200
  add a0, a0, t0
  j .Lvhf_ret
.Lvhf_s3:
  # Step 3: gas_used/number/timestamp
  mv a0, s2; mv a1, s3
  jal ra, validate_header_basic
  beqz a0, .Lvhf_s4
  li t0, 300
  add a0, a0, t0
  j .Lvhf_ret
.Lvhf_s4:
  # Step 4: check_gas_limit(this.gas_limit, parent.gas_limit)
  ld a0, 80(s2)
  ld a1, 80(s3)
  jal ra, check_gas_limit
  beqz a0, .Lvhf_s5
  li t0, 400
  add a0, a0, t0
  j .Lvhf_ret
.Lvhf_s5:
  # Step 5: base_fee continuity
  addi a0, s2, 96
  ld a1, 80(s3)
  ld a2, 88(s3)
  addi a3, s3, 96
  jal ra, header_validate_base_fee
  beqz a0, .Lvhf_s6
  li t0, 500
  add a0, a0, t0
  j .Lvhf_ret
.Lvhf_s6:
  # Step 6: Amsterdam excess_blob_gas recurrence
  ld a0, 136(s2)
  ld a1, 128(s3)
  ld a2, 136(s3)
  addi a3, s3, 96
  jal ra, header_validate_excess_blob_gas
  beqz a0, .Lvhf_ret
  li t0, 600
  add a0, a0, t0
.Lvhf_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 56
  ret
