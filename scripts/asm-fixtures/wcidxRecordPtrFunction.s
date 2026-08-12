wcidx_record_ptr:
  slli x5, x10, 5
  slli x6, x10, 4
  add x5, x5, x6
  la x10, wcidx_records
  add x10, x10, x5
  jalr x0, 0(x1)
