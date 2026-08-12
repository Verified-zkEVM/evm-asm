account_writes_incorporate_tx:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  la s0, tx_account_writes_count; ld s1, 0(s0)
  li s2, 0xbf780000
  li s3, 0
.Lawi_loop:
  bgeu s3, s1, .Lawi_clear
  slli a0, s3, 7; add a0, s2, a0
.Lawi_merge:
  jal ra, account_writes_block_upsert
.Lawi_next:
  addi s3, s3, 1; j .Lawi_loop
.Lawi_clear:
  la s0, tx_account_writes_count; sd zero, 0(s0)
  la s0, tx_account_writes_overflow; sd zero, 0(s0)
  la s0, account_writes_undo_count; sd zero, 0(s0)
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
