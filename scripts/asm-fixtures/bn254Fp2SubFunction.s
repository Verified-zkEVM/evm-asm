bnp_fp2_sub:
  la t0, bnp_cplx_params
  sd a0, 0(t0)
  sd a1, 8(t0)
  .4byte 0x8092a073             # csrs 0x809, t0 -> Bn254ComplexSub
  ret
