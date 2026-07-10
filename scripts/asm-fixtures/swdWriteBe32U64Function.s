swd_write_be32_u64:
  li t0, 0
  li t1, 32
.Lswd_z:
  beq t0, t1, .Lswd_zd
  add t2, a1, t0; sb x0, 0(t2); addi t0, t0, 1; j .Lswd_z
.Lswd_zd:
  # write the 8 BE bytes into offsets 24..31
  li t0, 0
  li t1, 8
.Lswd_b:
  beq t0, t1, .Lswd_bd
  li t2, 56; slli t3, t0, 3; sub t2, t2, t3   # shift = 56 - 8*t0
  srl t4, a0, t2; andi t4, t4, 0xff
  addi t5, a1, 24; add t5, t5, t0; sb t4, 0(t5)
  addi t0, t0, 1; j .Lswd_b
.Lswd_bd:
  ret
