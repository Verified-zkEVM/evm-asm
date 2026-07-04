bnp_fp2_inv:
  addi sp, sp, -24
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  la a0, bnp_t0
  mv a1, s1
  mv a2, s1
  jal ra, bnp_fp_mul             # t0 = x0^2
  la a0, bnp_t1
  addi a1, s1, 32
  addi a2, s1, 32
  jal ra, bnp_fp_mul             # t1 = x1^2
  la a0, bnp_t0
  la a1, bnp_t0
  la a2, bnp_t1
  jal ra, bnp_fp_add             # t0 = x0^2 + x1^2
  la a0, bnp_t1
  la a1, bnp_t0
  la a2, bnp_p_minus_2_le
  jal ra, bnp_fp_pow             # t1 = norm^(p-2)
  la a0, bnp_t2
  mv a1, s1
  la a2, bnp_t1
  jal ra, bnp_fp_mul             # t2 = x0 / norm
  la a0, bnp_t0
  addi a1, s1, 32
  la a2, bnp_t1
  jal ra, bnp_fp_mul             # t0 = x1 / norm
  la a0, bnp_t0
  la a1, bnp_t0
  la a2, bnp_p_minus_1_le
  jal ra, bnp_fp_mul             # t0 = -x1 / norm
  la t0, bnp_t2
  ld t1, 0(t0);  sd t1,  0(s0)
  ld t1, 8(t0);  sd t1,  8(s0)
  ld t1, 16(t0); sd t1, 16(s0)
  ld t1, 24(t0); sd t1, 24(s0)
  la t0, bnp_t0
  ld t1, 0(t0);  sd t1, 32(s0)
  ld t1, 8(t0);  sd t1, 40(s0)
  ld t1, 16(t0); sd t1, 48(s0)
  ld t1, 24(t0); sd t1, 56(s0)
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 24
  ret
