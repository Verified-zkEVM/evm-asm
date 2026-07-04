check_gas_limit:
  li t0, 5000                 # GAS_LIMIT_MINIMUM
  bltu a0, t0, .Lcgl_fail_min
  # max_adjustment_delta = parent_gas_limit >> 10  (== /1024)
  srli t1, a1, 10
  # abs_diff = |new - parent|
  bgtu a0, a1, .Lcgl_pos
  sub t2, a1, a0
  j .Lcgl_check
.Lcgl_pos:
  sub t2, a0, a1
.Lcgl_check:
  bgeu t2, t1, .Lcgl_fail_jump
  li a0, 0
  ret
.Lcgl_fail_min:
  li a0, 1
  ret
.Lcgl_fail_jump:
  li a0, 2
  ret
