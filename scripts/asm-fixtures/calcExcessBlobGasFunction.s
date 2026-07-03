calc_excess_blob_gas:
  add t0, a0, a1              # parent_excess + parent_used
  bgeu t0, a2, .Lcebg_pos     # >= target → return diff
  li a0, 0
  ret
.Lcebg_pos:
  sub a0, t0, a2
  ret
