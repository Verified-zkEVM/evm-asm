blsk_g1_wire:
  li t0, 0                       # coord index 0/1
.Lblsk_g1w_coord:
  slli t1, t0, 6
  add t1, a1, t1                 # wire felt base
  li t2, 16
.Lblsk_g1w_pad:
  sb zero, 0(t1)
  addi t1, t1, 1
  addi t2, t2, -1
  bnez t2, .Lblsk_g1w_pad
  slli t2, t0, 4
  slli t3, t0, 5
  add t2, t2, t3                 # 48 * coord index
  add t2, a0, t2
  li t3, 48
.Lblsk_g1w_copy:
  lbu t4, 0(t2)
  sb t4, 0(t1)
  addi t1, t1, 1
  addi t2, t2, 1
  addi t3, t3, -1
  bnez t3, .Lblsk_g1w_copy
  addi t0, t0, 1
  li t1, 2
  bne t0, t1, .Lblsk_g1w_coord
  ret
