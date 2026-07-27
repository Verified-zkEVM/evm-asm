block_access_list_hash:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1
  addi s2, s0, 16
  addi t3, s2, 44; addi a0, t3, 528; jal ra, bah_u32le
  addi t3, s2, 44; add t4, t3, a0
  la t0, bah_bal_start; sd t4, 0(t0)
  addi a0, s2, 4; jal ra, bah_u32le; add t5, s2, a0
  la t0, bah_bal_start; ld t4, 0(t0)
  sub a1, t5, t4; mv a0, t4; mv a2, s1
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 32
  j block_access_list_hash_core
