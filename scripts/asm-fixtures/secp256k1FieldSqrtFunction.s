secf_sqrt_mod_p:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s3, 24(sp)
  sd s4, 32(sp)
  sd s5, 40(sp)
  mv s0, a0
  mv s1, a1
  la s4, secf_pow_result
  la s5, secf_pow_base
  la a0, secp256k1_one_be
  mv a1, s4
  jal ra, secf_copy32
  mv a0, s0
  mv a1, s5
  jal ra, secf_reduce_once
  li s3, 255
.Lsecf_sqrt_pow_loop:
  mv a0, s4
  mv a2, s4
  jal ra, secf_square_mod_p
  li t0, 255
  beq s3, t0, .Lsecf_sqrt_skip_mul
  li t0, 254
  beq s3, t0, .Lsecf_sqrt_skip_mul
  li t0, 30
  beq s3, t0, .Lsecf_sqrt_skip_mul
  li t0, 7
  beq s3, t0, .Lsecf_sqrt_skip_mul
  li t0, 6
  beq s3, t0, .Lsecf_sqrt_skip_mul
  li t0, 5
  beq s3, t0, .Lsecf_sqrt_skip_mul
  li t0, 4
  beq s3, t0, .Lsecf_sqrt_skip_mul
  li t0, 1
  beq s3, t0, .Lsecf_sqrt_skip_mul
  beqz s3, .Lsecf_sqrt_after_mul
  mv a0, s4
  mv a1, s5
  mv a2, s4
  jal ra, secf_mul_mod_p
.Lsecf_sqrt_after_mul:
  beqz s3, .Lsecf_sqrt_pow_done
.Lsecf_sqrt_skip_mul:
  beqz s3, .Lsecf_sqrt_pow_done
  addi s3, s3, -1
  j .Lsecf_sqrt_pow_loop
.Lsecf_sqrt_pow_done:
  mv a0, s4
  mv a1, s1
  jal ra, secf_copy32
  mv a0, s1
  la a2, secf_pow_verify
  jal ra, secf_square_mod_p
  la a0, secf_pow_verify
  mv a1, s0
  jal ra, secf_eq32
  bnez a0, .Lsecf_sqrt_ok
  mv a0, s1
  jal ra, secf_zero32
  li a0, 1
  j .Lsecf_sqrt_done
.Lsecf_sqrt_ok:
  li a0, 0
.Lsecf_sqrt_done:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s3, 24(sp)
  ld s4, 32(sp)
  ld s5, 40(sp)
  addi sp, sp, 64
  ret
