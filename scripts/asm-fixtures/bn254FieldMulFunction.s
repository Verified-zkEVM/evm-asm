bnf_mul_mod_p:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  mv s0, a1
  mv s1, a2
  la a1, bnf_le_a
  jal ra, bnf_be_to_le
  mv a0, s0
  la a1, bnf_le_b
  jal ra, bnf_be_to_le
  la t0, bnf_mul_params
  .4byte 0x8022a073           # csrs 0x802, t0 -> Arith256Mod
  la a0, bnf_le_d
  mv a1, s1
  jal ra, bnf_le_to_be
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  addi sp, sp, 32
  ret
