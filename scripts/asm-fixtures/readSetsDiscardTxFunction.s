read_sets_discard_tx:
  la t0, tx_storage_reads_count; sd zero, 0(t0)
  la t0, tx_account_reads_count; sd zero, 0(t0)
  la t0, tx_code_reads_count;    sd zero, 0(t0)
  ret
