bnq_smul:
  li t5, 12
.Lbnq_smul_loop:
  la t0, bnp_arith_params
  sd a1, 0(t0)
  sd a2, 8(t0)
  la t4, bnf_le_zero
  sd t4, 16(t0)
  la t4, bnf_le_p
  sd t4, 24(t0)
  sd a0, 32(t0)
  .4byte 0x8022a073
  addi a0, a0, 32
  addi a1, a1, 32
  addi t5, t5, -1
  bnez t5, .Lbnq_smul_loop
  ret
