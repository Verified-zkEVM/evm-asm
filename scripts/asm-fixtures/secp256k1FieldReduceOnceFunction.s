secf_reduce_once:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  mv a0, s0
  la a1, secp256k1_p_be
  la a2, secf_cmp
  jal ra, u256_lt_be
  la t0, secf_cmp
  ld t1, 0(t0)
  bnez t1, .Lsecf_reduce_copy
  mv a0, s0
  la a1, secp256k1_p_be
  mv a2, s1
  jal ra, u256_sub_be
  li a0, 1
  j .Lsecf_reduce_done
.Lsecf_reduce_copy:
  mv a0, s0
  mv a1, s1
  jal ra, secf_copy32
  li a0, 0
.Lsecf_reduce_done:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  addi sp, sp, 32
  ret
