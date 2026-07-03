secf_pow_mod_n:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  sd s5, 48(sp)
  mv s0, a0
  mv s1, a1
  mv s2, a2
  la s4, secf_pow_result
  la s5, secf_pow_base
  la a0, secp256k1_one_be
  mv a1, s4
  jal ra, secf_copy32
  mv a0, s0
  mv a1, s5
  jal ra, secf_reduce_once_n
  li s3, 255
.Lsecf_pown_loop:
  mv a0, s4
  mv a2, s4
  jal ra, secf_square_mod_n
  mv a0, s1
  mv a1, s3
  jal ra, secf_get_bit_lsb
  beqz a0, .Lsecf_pown_after_mul
  mv a0, s4
  mv a1, s5
  mv a2, s4
  jal ra, secf_mul_mod_n
.Lsecf_pown_after_mul:
  beqz s3, .Lsecf_pown_done
  addi s3, s3, -1
  j .Lsecf_pown_loop
.Lsecf_pown_done:
  mv a0, s4
  mv a1, s2
  jal ra, secf_copy32
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  ld s5, 48(sp)
  addi sp, sp, 80
  ret
