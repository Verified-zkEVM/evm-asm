blsg2_fp_mul:
  la t0, blsg2_fp_params
  sd a0, 0(t0)
  sd a1, 8(t0)
  la a0, blsf_le_zero
  sd a0, 16(t0)
  la a0, blsf_le_p
  sd a0, 24(t0)
  sd a2, 32(t0)
  mv a0, t0
  .4byte 0x80b52073             # csrs 0x80B, a0 -> Arith384Mod
  ret
