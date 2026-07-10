swd_write_be8:
  li t0, 0
  li t1, 8
.Lswd8:
  beq t0, t1, .Lswd8d
  li t2, 56; slli t3, t0, 3; sub t2, t2, t3
  srl t4, a0, t2; andi t4, t4, 0xff
  add t5, a1, t0; sb t4, 0(t5)
  addi t0, t0, 1; j .Lswd8
.Lswd8d:
  ret
