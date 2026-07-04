secf_add_mod_p:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0
  mv s1, a1
  mv s2, a2
  la s3, secf_tmp0
  mv a0, s0
  mv a1, s1
  mv a2, s3
  jal ra, u256_add_be
  mv s4, a0
  beqz s4, .Lsecf_add_reduce
  mv a0, s3
  la a1, secp256k1_c_be
  mv a2, s3
  jal ra, u256_add_be
.Lsecf_add_reduce:
  mv a0, s3
  mv a1, s2
  jal ra, secf_reduce_once
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 48
  ret
