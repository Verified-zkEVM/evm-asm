blsg_point_dbl:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  addi a0, s0, 48
  li a1, 48
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg_dbl_finite
  mv a0, s1
  jal ra, blsg_zero96
  li a0, 1
  j .Lblsg_dbl_ret
.Lblsg_dbl_finite:
  mv a0, s0
  la a1, blsf_p1
  jal ra, blsg_be_to_le          # p1.x
  addi a0, s0, 48
  la a1, blsf_p1
  addi a1, a1, 48
  jal ra, blsg_be_to_le          # p1.y
  la a0, blsf_p1
  .4byte 0x80d52073              # csrs 0x80D, a0 -> Bls12_381CurveDbl
  la a0, blsf_p1
  mv a1, s1
  jal ra, blsg_le_to_be          # out.x
  la a0, blsf_p1
  addi a0, a0, 48
  addi a1, s1, 48
  jal ra, blsg_le_to_be          # out.y
  li a0, 0
.Lblsg_dbl_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
