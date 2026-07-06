validate_header_basic:
  ld t0, 88(a0)              # this.gas_used
  ld t1, 80(a0)              # this.gas_limit
  bgtu t0, t1, .Lvhb_fail_gas
  ld t0, 64(a0)              # this.number
  beqz t0, .Lvhb_fail_number
  ld t1, 64(a1)              # parent.number
  addi t1, t1, 1
  bne t0, t1, .Lvhb_fail_number
  ld t0, 72(a0)              # this.timestamp
  ld t1, 72(a1)              # parent.timestamp
  bgeu t1, t0, .Lvhb_fail_timestamp  # parent_ts >= this_ts → fail
  li a0, 0
  ret
.Lvhb_fail_gas:
  li a0, 1
  ret
.Lvhb_fail_number:
  li a0, 2
  ret
.Lvhb_fail_timestamp:
  li a0, 3
  ret
