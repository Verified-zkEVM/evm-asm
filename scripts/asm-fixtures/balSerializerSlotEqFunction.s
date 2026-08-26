bal_serializer_slot_eq:
  ld t0, 0(a0);  ld t1, 0(a1);  bne t0, t1, .Lbsse_no
  ld t0, 8(a0);  ld t1, 8(a1);  bne t0, t1, .Lbsse_no
  ld t0, 16(a0); ld t1, 16(a1); bne t0, t1, .Lbsse_no
  ld t0, 24(a0); ld t1, 24(a1); bne t0, t1, .Lbsse_no
  li a0, 1; ret
.Lbsse_no:
  li a0, 0; ret
