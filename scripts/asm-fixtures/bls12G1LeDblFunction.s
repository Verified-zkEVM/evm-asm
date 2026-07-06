blsg_le_dbl:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  addi a0, s0, 48
  li a1, 48
  jal ra, blsg_is_zero_n
  beqz a0, .Lblsg_ldbl_finite
  mv a0, s1
  jal ra, blsg_zero96
  li a0, 1
  j .Lblsg_ldbl_ret
.Lblsg_ldbl_finite:
  mv a0, s0
  la a1, blsf_p1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blsf_p1
  .4byte 0x80d52073              # csrs 0x80D, a0 -> Bls12_381CurveDbl
  la a0, blsf_p1
  mv a1, s1
  li a2, 12
  jal ra, blsf_copy_quads
  li a0, 0
.Lblsg_ldbl_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
