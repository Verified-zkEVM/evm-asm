widx_cmp32:
  li t0, 32
.Lwidx_cmp_loop:
  beqz t0, .Lwidx_cmp_eq
  lbu t1, 0(a0)
  lbu t2, 0(a1)
  bltu t1, t2, .Lwidx_cmp_lt
  bltu t2, t1, .Lwidx_cmp_gt
  addi a0, a0, 1
  addi a1, a1, 1
  addi t0, t0, -1
  j .Lwidx_cmp_loop
.Lwidx_cmp_lt:
  li a0, 0
  ret
.Lwidx_cmp_eq:
  li a0, 1
  ret
.Lwidx_cmp_gt:
  li a0, 2
  ret
