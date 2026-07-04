blq_pow:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0
  mv s1, a1
  mv s2, a2
  mv s3, a3
  mv a0, s0
  jal ra, blq_set_one
.Lblq_pow_loop:
  la a0, blq_powt
  mv a1, s0
  mv a2, s0
  jal ra, blq_mul                # powt = dst^2
  la a0, blq_powt
  mv a1, s0
  jal ra, blq_copy
  srli t0, s3, 6
  slli t0, t0, 3
  add t0, s2, t0
  ld t1, 0(t0)
  andi t2, s3, 63
  srl t1, t1, t2
  andi t1, t1, 1
  beqz t1, .Lblq_pow_skip
  la a0, blq_powt
  mv a1, s0
  mv a2, s1
  jal ra, blq_mul                # powt = dst * base
  la a0, blq_powt
  mv a1, s0
  jal ra, blq_copy
.Lblq_pow_skip:
  beqz s3, .Lblq_pow_done
  addi s3, s3, -1
  j .Lblq_pow_loop
.Lblq_pow_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
