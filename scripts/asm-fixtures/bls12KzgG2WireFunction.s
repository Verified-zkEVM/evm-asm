blsk_g2_wire:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0
  mv s1, a1
  li s2, 0                       # felt index 0..3
.Lblsk_g2w_felt:
  slli t0, s2, 6
  add t1, s1, t0
  li t2, 16
.Lblsk_g2w_pad:
  sb zero, 0(t1)
  addi t1, t1, 1
  addi t2, t2, -1
  bnez t2, .Lblsk_g2w_pad
  slli t0, s2, 4
  slli t2, s2, 5
  add t0, t0, t2                 # 48 * felt index
  add a0, s0, t0
  slli t0, s2, 6
  add a1, s1, t0
  addi a1, a1, 16
  jal ra, blsg_le_to_be
  addi s2, s2, 1
  li t0, 4
  bne s2, t0, .Lblsk_g2w_felt
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
