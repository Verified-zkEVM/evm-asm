read_sets_incorporate_tx:
  addi sp, sp, -16; sd ra, 0(sp)
  li a0, 0xa23349c0; la a1, tx_storage_reads_count; li a2, 0xa1908780
  la a3, storage_reads_count; li a4, 64; li a5, 64; li a6, 66666
  la a7, storage_reads_overflow; jal ra, read_sets_merge_one
  li a0, 0xa24349c0; la a1, tx_account_reads_count; li a2, 0xa1d1a200
  la a3, account_reads_count; li a4, 32; li a5, 20; li a6, 66666
  la a7, account_reads_overflow; jal ra, read_sets_merge_one
  li a0, 0xa24b49c0; la a1, tx_code_reads_count; li a2, 0xa1f22f40
  la a3, code_reads_count; li a4, 64; li a5, 64; li a6, 66666
  la a7, code_reads_overflow; jal ra, read_sets_merge_one
  ld ra, 0(sp); addi sp, sp, 16
  j read_sets_discard_tx
