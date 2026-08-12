widx_record_ptr:
  slli t0, a0, 5             # i * 32
  slli t1, a0, 4             # i * 16
  add t0, t0, t1             # i * 48
  la a0, widx_records
  add a0, a0, t0
  ret
