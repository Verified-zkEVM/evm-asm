headers_parent_hash:
  lbu t0, 0(a0)
  li t1, 0xc0
  bltu t0, t1, .Lhph_fail
  li t1, 0xf8
  bltu t0, t1, .Lhph_short
  li t1, 0xf7
  sub t2, t0, t1
  li t3, 2
  bltu t3, t2, .Lhph_fail
  addi t2, t2, 1
  add a0, a0, t2
  sub a1, a1, t2
  j .Lhph_after_prefix
.Lhph_short:
  addi a0, a0, 1
  addi a1, a1, -1
.Lhph_after_prefix:
  li t0, 33
  bltu a1, t0, .Lhph_fail
  lbu t1, 0(a0)
  li t2, 0xa0
  bne t1, t2, .Lhph_fail
  li t0, 0
.Lhph_copy:
  li t1, 32
  beq t0, t1, .Lhph_ok
  addi t2, a0, 1
  add t2, t2, t0
  lbu t3, 0(t2)
  add t2, a2, t0
  sb t3, 0(t2)
  addi t0, t0, 1
  j .Lhph_copy
.Lhph_ok:
  li a0, 0
  ret
.Lhph_fail:
  li a0, 1
  ret
