bnp_fp2_mul:
  la t0, bnp_cplx_params
  sd a0, 0(t0)
  sd a1, 8(t0)
  .4byte 0x80a2a073             # csrs 0x80A, t0 -> Bn254ComplexMul
  ret
