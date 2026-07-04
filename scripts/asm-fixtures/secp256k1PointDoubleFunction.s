secp256k1_point_double:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  addi a0, s0, 32
  jal ra, secf_is_zero32
  beqz a0, .Lsecc_double_finite
  mv a0, s1
  jal ra, secf_zero32
  addi a0, s1, 32
  jal ra, secf_zero32
  li a0, 1
  j .Lsecc_double_ret
.Lsecc_double_finite:
  mv a0, s0
  la a1, secc_le_p1
  jal ra, secf_be_to_le         # p1.x
  addi a0, s0, 32
  la a1, secc_le_p1
  addi a1, a1, 32
  jal ra, secf_be_to_le         # p1.y
  la t0, secc_le_p1
  .4byte 0x8042a073             # csrs 0x804, t0 -> Secp256k1Dbl
  la a0, secc_le_p1
  mv a1, s1
  jal ra, secf_le_to_be         # out.x
  la a0, secc_le_p1
  addi a0, a0, 32
  addi a1, s1, 32
  jal ra, secf_le_to_be         # out.y
  li a0, 0
.Lsecc_double_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
