message_call_gas:
  mv t0, a0                   # value_nonzero
  mv t1, a1                   # requested gas
  mv t2, a2                   # gas_left
  mv t3, a3                   # memory_cost
  mv t4, a4                   # extra_gas
  add t5, t3, t4              # memory_cost + extra_gas
  bltu t5, t3, .Lmcg_input_overflow
  li t6, 0
  beqz t0, .Lmcg_have_stipend
  li t6, 2300
.Lmcg_have_stipend:
  bltu t2, t5, .Lmcg_uncapped
  sub a5, t2, t5              # available after memory/extra
  srli a6, a5, 6
  sub a6, a5, a6              # max_message_call_gas
  mv a3, t1
  bgeu a6, t1, .Lmcg_have_capped
  mv a3, a6
  j .Lmcg_have_capped
.Lmcg_uncapped:
  mv a3, t1
.Lmcg_have_capped:
  add a1, a3, t4              # cost
  bltu a1, a3, .Lmcg_output_overflow
  add a2, a3, t6              # sub_call
  bltu a2, a3, .Lmcg_output_overflow
  li a0, 0
  ret
.Lmcg_input_overflow:
  li a0, 1
  li a1, 0
  li a2, 0
  li a3, 0
  ret
.Lmcg_output_overflow:
  li a0, 2
  li a1, 0
  li a2, 0
  li a3, 0
  ret
