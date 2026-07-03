blsg2_fp2_inv:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  mv a0, s0
  mv a1, s0
  la a2, blsg2_n
  jal ra, blsg2_fp_mul           # n = c0^2
  addi a0, s0, 48
  addi a1, s0, 48
  la a2, blsg2_ft
  jal ra, blsg2_fp_mul           # ft = c1^2
  la a0, blsg2_n
  la a1, blsg2_ft
  la a2, blsg2_n
  jal ra, blsg2_fp_add           # n = c0^2 + c1^2
  la a0, blsg2_n
  la a1, blsg2_ninv
  jal ra, blsg2_fp_inv
  mv a0, s0
  la a1, blsg2_ninv
  mv a2, s1
  jal ra, blsg2_fp_mul           # dst.c0 = c0 * n^-1
  addi a0, s0, 48
  la a1, blsg2_ninv
  la a2, blsg2_ft
  jal ra, blsg2_fp_mul           # ft = c1 * n^-1
  la a0, blsg2_ft
  la a1, blsg2_pm1_le
  addi a2, s1, 48
  jal ra, blsg2_fp_mul           # dst.c1 = -ft
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
