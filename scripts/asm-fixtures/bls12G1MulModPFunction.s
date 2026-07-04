blsg_mul_mod_p:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  mv s0, a1
  mv s1, a2
  la a1, blsf_le_a
  jal ra, blsg_be_to_le
  mv a0, s0
  la a1, blsf_le_b
  jal ra, blsg_be_to_le
  la a0, blsf_mul_params
  .4byte 0x80b52073           # csrs 0x80B, a0 -> Arith384Mod
  la a0, blsf_le_d
  mv a1, s1
  jal ra, blsg_le_to_be
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  addi sp, sp, 32
  ret
