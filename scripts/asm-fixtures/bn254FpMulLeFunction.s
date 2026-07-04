bnp_fp_mul:
  la t0, bnp_arith_params
  sd a1, 0(t0)
  sd a2, 8(t0)
  la t1, bnf_le_zero
  sd t1, 16(t0)
  la t1, bnf_le_p
  sd t1, 24(t0)
  sd a0, 32(t0)
  .4byte 0x8022a073             # csrs 0x802, t0 -> Arith256Mod
  ret
