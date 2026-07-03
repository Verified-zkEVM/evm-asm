tx_refund_cap:
  bltu a0, a1, .Ltrc_invalid
  sub t0, a0, a1              # gas_used_before_refund
  sd t0, 0(a3)
  li t1, 5
  divu t2, t0, t1             # one-fifth cap
  sd t2, 8(a3)
  mv t3, a2
  bltu t2, t3, .Ltrc_use_cap
  mv t4, t3
  j .Ltrc_apply
.Ltrc_use_cap:
  mv t4, t2
.Ltrc_apply:
  sd t4, 16(a3)
  sub t5, t0, t4
  sd t5, 24(a3)
  li a0, 0
  ret
.Ltrc_invalid:
  sd zero, 0(a3)
  sd zero, 8(a3)
  sd zero, 16(a3)
  sd zero, 24(a3)
  li a0, 1
  ret
