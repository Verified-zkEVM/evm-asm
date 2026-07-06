blsg2_encode:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0
  mv s1, a1
  li s2, 0
.Lblsg2_enc_felt:
  slli t0, s2, 4
  slli t1, s2, 5
  add t0, t0, t1                 # 48 * felt index
  add a0, s0, t0
  add a1, s1, t0
  jal ra, blsg_le_to_be
  addi s2, s2, 1
  li t0, 4
  bne s2, t0, .Lblsg2_enc_felt
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
