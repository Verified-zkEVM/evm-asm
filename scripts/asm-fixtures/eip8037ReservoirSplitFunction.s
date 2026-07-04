eip8037_reservoir_split:
  # a0=tx_gas, a1=intrinsic_total, a2=intrinsic_regular,
  # a3=gas_out, a4=state_reservoir_out
  bltu a0, a1, .Le8037_underflow
  li t0, 16777216            # TX_MAX_GAS_LIMIT
  bltu t0, a2, .Le8037_regular_too_large
  sub t1, a0, a1             # execution_gas
  sub t2, t0, a2             # regular_gas_budget
  mv t3, t1                  # gas = execution_gas by default
  bltu t1, t2, .Le8037_have_gas
  mv t3, t2                  # gas = regular_gas_budget
.Le8037_have_gas:
  sub t4, t1, t3             # state_gas_reservoir
  sd t3, 0(a3)
  sd t4, 0(a4)
  li a0, 0
  ret
.Le8037_underflow:
  sd zero, 0(a3)
  sd zero, 0(a4)
  li a0, 1
  ret
.Le8037_regular_too_large:
  sd zero, 0(a3)
  sd zero, 0(a4)
  li a0, 2
  ret
