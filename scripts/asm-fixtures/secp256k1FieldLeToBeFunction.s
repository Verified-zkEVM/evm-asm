secf_le_to_be:
  li t0, 0                   # limb index
.Lsecf_l2b_quad:
  slli t1, t0, 3
  add t2, a0, t1
  ld t3, 0(t2)
  li t1, 31
  slli t2, t0, 3
  sub t1, t1, t2
  add t1, a1, t1             # BE offset of the limb's LSB
  li t4, 8
.Lsecf_l2b_byte:
  andi t5, t3, 0xff
  sb t5, 0(t1)
  srli t3, t3, 8
  addi t1, t1, -1
  addi t4, t4, -1
  bnez t4, .Lsecf_l2b_byte
  addi t0, t0, 1
  li t1, 4
  bne t0, t1, .Lsecf_l2b_quad
  ret
