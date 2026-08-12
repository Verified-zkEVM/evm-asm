write_sets_incorporate_tx:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  la t0, current_block_access_index; ld a0, 0(t0)
  jal ra, bal_emit_storage_changes
  la s0, tx_storage_writes_count; ld s1, 0(s0)
  li s2, 2731900608
  li s3, 0
.Lwsi_loop:
  bgeu s3, s1, .Lwsi_clear
  slli s4, s3, 7; add s4, s2, s4
  mv a0, s4; addi a1, s4, 32; addi a2, s4, 64; addi a3, s4, 96
  jal ra, storage_writes_block_upsert
  addi s3, s3, 1; j .Lwsi_loop
.Lwsi_clear:
  sd zero, 0(s0)
  la s5, tx_storage_writes_overflow; sd zero, 0(s5)
  la s5, storage_writes_undo_count; sd zero, 0(s5)
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 80
  ret
