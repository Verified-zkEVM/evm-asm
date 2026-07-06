blsg2_fp2_sub:
  la t0, blsf_cplx_params
  sd a0, 0(t0)
  sd a1, 8(t0)
  mv a0, t0
  .4byte 0x80f52073             # csrs 0x80F, a0 -> Bls12_381ComplexSub
  ret
