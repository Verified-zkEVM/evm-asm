blq_smul:
  li t5, 12
.Lblq_smul_loop:
  la t0, blq_arith_params
  sd a1, 0(t0)
  sd a2, 8(t0)
  la t4, blsf_le_zero
  sd t4, 16(t0)
  la t4, blsf_le_p
  sd t4, 24(t0)
  sd a0, 32(t0)
  mv t6, a0
  mv a0, t0
  .4byte 0x80b52073
  addi a0, t6, 48
  addi a1, a1, 48
  addi t5, t5, -1
  bnez t5, .Lblq_smul_loop
  ret
