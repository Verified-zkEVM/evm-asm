validate_header:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  sd s5, 48(sp)
  mv s0, a0                  # this_rlp
  mv s1, a1                  # this_len
  mv s2, a2                  # this_struct
  mv s3, a3                  # parent_struct
  mv s4, a4                  # parent_rlp
  mv s5, a5                  # parent_len
  ld t0, 64(s2)
  beqz t0, .Lvh_fail1
  ld a0, 136(s2)
  ld a1, 128(s3)
  ld a2, 136(s3)
  addi a3, s3, 96
  jal ra, header_validate_excess_blob_gas
  bnez a0, .Lvh_fail2
  ld t0, 88(s2)
  ld t1, 80(s2)
  bltu t1, t0, .Lvh_fail3
  ld a0, 80(s2)
  ld a1, 80(s3)
  jal ra, check_gas_limit
  bnez a0, .Lvh_fail4
  addi a0, s2, 96
  ld a1, 80(s3)
  ld a2, 88(s3)
  addi a3, s3, 96
  jal ra, header_validate_base_fee
  bnez a0, .Lvh_fail4
  ld t0, 72(s2)
  ld t1, 72(s3)
  bgeu t1, t0, .Lvh_fail5
  ld t0, 64(s2)
  ld t1, 64(s3)
  addi t1, t1, 1
  bne t0, t1, .Lvh_fail6
  mv a0, s0
  mv a1, s1
  jal ra, header_validate_extra_data_length
  bnez a0, .Lvh_fail7
  mv a0, s0
  mv a1, s1
  jal ra, header_validate_post_merge
  beqz a0, .Lvh_pm_ok
  li t0, 1
  beq a0, t0, .Lvh_fail10
  li t0, 2
  beq a0, t0, .Lvh_fail8
  li t0, 3
  beq a0, t0, .Lvh_fail9
  j .Lvh_fail12
.Lvh_pm_ok:
  mv a0, s0
  mv a1, s1
  mv a2, s4
  mv a3, s5
  jal ra, header_validate_parent_hash
  bnez a0, .Lvh_fail11
  li a0, 0
  j .Lvh_ret
.Lvh_fail1:
  li a0, 1
  j .Lvh_ret
.Lvh_fail2:
  li a0, 2
  j .Lvh_ret
.Lvh_fail3:
  li a0, 3
  j .Lvh_ret
.Lvh_fail4:
  li a0, 4
  j .Lvh_ret
.Lvh_fail5:
  li a0, 5
  j .Lvh_ret
.Lvh_fail6:
  li a0, 6
  j .Lvh_ret
.Lvh_fail7:
  li a0, 7
  j .Lvh_ret
.Lvh_fail8:
  li a0, 8
  j .Lvh_ret
.Lvh_fail9:
  li a0, 9
  j .Lvh_ret
.Lvh_fail10:
  li a0, 10
  j .Lvh_ret
.Lvh_fail11:
  li a0, 11
  j .Lvh_ret
.Lvh_fail12:
  li a0, 12
.Lvh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  ld s5, 48(sp)
  addi sp, sp, 56
  ret
