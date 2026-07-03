blm_fp_pow:
  addi sp, sp, -48
  sd ra, 0(sp); sd s5, 8(sp); sd s6, 16(sp); sd s7, 24(sp); sd s8, 32(sp)
  mv s5, a0
  mv s6, a1
  mv s7, a2
  mv s8, a3
  la a0, blsf_le_one
  mv a1, s5
  li a2, 6
  jal ra, blsf_copy_quads        # dst = 1
.Lblm_fpp_loop:
  mv a0, s5
  mv a1, s5
  mv a2, s5
  jal ra, blsg2_fp_mul           # dst = dst^2 (in place)
  srli t0, s8, 6
  slli t0, t0, 3
  add t0, s7, t0
  ld t1, 0(t0)
  andi t2, s8, 63
  srl t1, t1, t2
  andi t1, t1, 1
  beqz t1, .Lblm_fpp_skip
  mv a0, s5
  mv a1, s6
  mv a2, s5
  jal ra, blsg2_fp_mul           # dst *= base
.Lblm_fpp_skip:
  beqz s8, .Lblm_fpp_done
  addi s8, s8, -1
  j .Lblm_fpp_loop
.Lblm_fpp_done:
  ld ra, 0(sp); ld s5, 8(sp); ld s6, 16(sp); ld s7, 24(sp); ld s8, 32(sp)
  addi sp, sp, 48
  ret
