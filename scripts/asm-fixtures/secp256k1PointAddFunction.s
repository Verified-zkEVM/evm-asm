secp256k1_point_add:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  mv a0, s0
  jal ra, secf_is_zero32
  beqz a0, .Lsecc_add_check_q_inf
  addi a0, s0, 32
  jal ra, secf_is_zero32
  beqz a0, .Lsecc_add_check_q_inf
  mv a0, s1
  mv a1, s2
  jal ra, secp256k1_point_copy64
  li a0, 0
  j .Lsecc_add_ret
.Lsecc_add_check_q_inf:
  mv a0, s1
  jal ra, secf_is_zero32
  beqz a0, .Lsecc_add_regular
  addi a0, s1, 32
  jal ra, secf_is_zero32
  beqz a0, .Lsecc_add_regular
  mv a0, s0
  mv a1, s2
  jal ra, secp256k1_point_copy64
  li a0, 0
  j .Lsecc_add_ret
.Lsecc_add_regular:
  mv a0, s0
  mv a1, s1
  jal ra, secf_eq32
  beqz a0, .Lsecc_add_distinct_x
  addi a0, s0, 32
  addi a1, s1, 32
  jal ra, secf_eq32
  beqz a0, .Lsecc_add_inf
  mv a0, s0
  mv a1, s2
  jal ra, secp256k1_point_double
  j .Lsecc_add_ret
.Lsecc_add_distinct_x:
  mv a0, s0
  la a1, secc_le_p1
  jal ra, secf_be_to_le         # p1.x
  addi a0, s0, 32
  la a1, secc_le_p1
  addi a1, a1, 32
  jal ra, secf_be_to_le         # p1.y
  mv a0, s1
  la a1, secc_le_p2
  jal ra, secf_be_to_le         # p2.x
  addi a0, s1, 32
  la a1, secc_le_p2
  addi a1, a1, 32
  jal ra, secf_be_to_le         # p2.y
  la t0, secc_add_params
  .4byte 0x8032a073             # csrs 0x803, t0 -> Secp256k1Add
  la a0, secc_le_p1
  mv a1, s2
  jal ra, secf_le_to_be         # out.x
  la a0, secc_le_p1
  addi a0, a0, 32
  addi a1, s2, 32
  jal ra, secf_le_to_be         # out.y
  li a0, 0
  j .Lsecc_add_ret
.Lsecc_add_inf:
  mv a0, s2
  jal ra, secf_zero32
  addi a0, s2, 32
  jal ra, secf_zero32
  li a0, 1
.Lsecc_add_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
