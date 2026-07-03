p256_be_to_le:
  li t0, 0                       # limb index
.Lp256_b2l_quad:
  li t1, 24
  slli t2, t0, 3
  sub t1, t1, t2
  add t1, a0, t1                 # BE offset of the limb's MSB
  li t3, 0
  li t4, 8
.Lp256_b2l_byte:
  slli t3, t3, 8
  lbu t5, 0(t1)
  or t3, t3, t5
  addi t1, t1, 1
  addi t4, t4, -1
  bnez t4, .Lp256_b2l_byte
  slli t2, t0, 3
  add t2, a1, t2
  sd t3, 0(t2)
  addi t0, t0, 1
  li t1, 4
  bne t0, t1, .Lp256_b2l_quad
  ret
