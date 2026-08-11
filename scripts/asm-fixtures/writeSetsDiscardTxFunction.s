write_sets_discard_tx:
  la t0, tx_storage_writes_count; sd zero, 0(t0)
  la t0, tx_storage_writes_overflow; sd zero, 0(t0)
  la t0, storage_writes_undo_count; sd zero, 0(t0)
  ret
