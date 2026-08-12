widx_swap_records:
  beq a0, a1, .Lwidx_swap_ret
  li t6, 6
.Lwidx_swap_loop:
  beqz t6, .Lwidx_swap_ret
  ld t0, 0(a0)
  ld t1, 0(a1)
  sd t1, 0(a0)
  sd t0, 0(a1)
  addi a0, a0, 8
  addi a1, a1, 8
  addi t6, t6, -1
  j .Lwidx_swap_loop
.Lwidx_swap_ret:
  ret
