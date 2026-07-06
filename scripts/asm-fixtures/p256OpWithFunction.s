p256_op_with:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a1
  mv s1, a2
  mv s2, a3
  la a1, p256_le_a
  jal ra, p256_be_to_le
  mv a0, s0
  la a1, p256_le_b
  jal ra, p256_be_to_le
  mv t0, s2
  .4byte 0x8022a073              # csrs 0x802, t0 -> Arith256Mod
  la a0, p256_le_d
  mv a1, s1
  jal ra, p256_le_to_be
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
