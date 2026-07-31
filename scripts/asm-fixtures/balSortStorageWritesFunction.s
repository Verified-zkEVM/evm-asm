bal_sort_storage_writes:
  addi sp, sp, -16
  sd ra, 0(sp)
  li a0, 0xa1fa0000
  la t0, storage_writes_count; ld a1, 0(t0)
  li a2, 128
  li a3, 0x20201400
  li a4, 2
  jal ra, bal_canonical_sort
  ld ra, 0(sp); addi sp, sp, 16
  ret
