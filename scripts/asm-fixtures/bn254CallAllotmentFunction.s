bn254_call_allotment:
  ld x17, 568(x20)
  srli x22, x17, 6
  sub x22, x17, x22              # max send = remaining - remaining/64
  ld x23, 8(x12)
  ld x24, 16(x12)
  or x23, x23, x24
  ld x24, 24(x12)
  or x23, x23, x24
  bnez x23, .Lbn254_allot_cap    # gas word >= 2^64: cap
  ld x23, 0(x12)
  bgeu x23, x22, .Lbn254_allot_cap
  mv x22, x23
.Lbn254_allot_cap:
  ret
