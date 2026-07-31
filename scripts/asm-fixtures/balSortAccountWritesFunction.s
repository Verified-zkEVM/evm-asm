bal_sort_account_writes:
  addi sp, sp, -16
  sd ra, 0(sp)
  li a0, 0xa24a0000
  la t0, account_writes_count; ld a1, 0(t0)
  li a2, 128
  li a3, 0x9400
  li a4, 1
  jal ra, bal_canonical_sort
  ld ra, 0(sp); addi sp, sp, 16
  ret
