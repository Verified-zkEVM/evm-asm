blsf_fp_mul:
  addi sp, sp, -16
  sd ra, 0(sp)
  sd a1, 8(sp)
  la a1, blsf_le_a
  li a2, 6
  jal ra, blsf_copy_quads
  ld a0, 8(sp)
  la a1, blsf_le_b
  li a2, 6
  jal ra, blsf_copy_quads
  la a0, blsf_mul_params
  .4byte 0x80b52073             # csrs 0x80B, a0 -> Arith384Mod
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
