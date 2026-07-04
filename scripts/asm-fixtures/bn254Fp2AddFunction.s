bnp_fp2_add:
  la t0, bnp_cplx_params
  sd a0, 0(t0)
  sd a1, 8(t0)
  .4byte 0x8082a073             # csrs 0x808, t0 -> Bn254ComplexAdd
  ret
