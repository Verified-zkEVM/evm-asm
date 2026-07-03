bnp_fp_pow:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0
  mv s1, a1
  mv s2, a2
  li t0, 1
  sd t0, 0(s0)
  sd zero, 8(s0)
  sd zero, 16(s0)
  sd zero, 24(s0)
  li s3, 253                     # bit index
.Lbnp_pow_loop:
  mv a0, s0
  mv a1, s0
  mv a2, s0
  jal ra, bnp_fp_mul             # dst = dst^2
  srli t0, s3, 6
  slli t0, t0, 3
  add t0, s2, t0
  ld t1, 0(t0)
  andi t2, s3, 63
  srl t1, t1, t2
  andi t1, t1, 1
  beqz t1, .Lbnp_pow_skip
  mv a0, s0
  mv a1, s0
  mv a2, s1
  jal ra, bnp_fp_mul             # dst *= base
.Lbnp_pow_skip:
  beqz s3, .Lbnp_pow_done
  addi s3, s3, -1
  j .Lbnp_pow_loop
.Lbnp_pow_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
