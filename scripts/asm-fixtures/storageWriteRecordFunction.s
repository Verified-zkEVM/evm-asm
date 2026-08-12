storage_write_record:
  addi sp, sp, -112
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  sd ra, 56(sp); sd a3, 64(sp); sd a4, 72(sp); sd a5, 80(sp)
  sd a6, 88(sp); sd a0, 96(sp)
  la t0, tx_storage_writes_count; ld t1, 0(t0)
  li t3, 2731900608
  li t4, 0
.Lswr_scan:
  bgeu t4, t1, .Lswr_append
  slli t5, t4, 7; add t5, t3, t5
  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lswr_next
  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lswr_next
  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lswr_next
  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lswr_next
  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lswr_next
  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lswr_next
  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lswr_next
  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lswr_next
  ld t2, 64(t5); ld t6, 0(a2); bne t2, t6, .Lswr_journal_hit
  ld t2, 72(t5); ld t6, 8(a2); bne t2, t6, .Lswr_journal_hit
  ld t2, 80(t5); ld t6, 16(a2); bne t2, t6, .Lswr_journal_hit
  ld t2, 88(t5); ld t6, 24(a2); bne t2, t6, .Lswr_journal_hit
  j .Lswr_store
.Lswr_journal_hit:
  mv a3, t4; li a4, 0; addi a5, t5, 64
  jal ra, storage_writes_undo_push
  bnez a0, .Lswr_overflow
  ld a0, 96(sp)
  j .Lswr_store
.Lswr_next:
  addi t4, t4, 1; j .Lswr_scan
.Lswr_append:
  li t2, 5588
  bgeu t1, t2, .Lswr_overflow
  mv a3, t1; li a4, 1; li a5, 0
  jal ra, storage_writes_undo_push
  bnez a0, .Lswr_overflow
  ld a0, 96(sp)
  slli t5, t1, 7; add t5, t3, t5
  ld t2, 0(a0);  sd t2, 0(t5)
  ld t2, 8(a0);  sd t2, 8(t5)
  ld t2, 16(a0); sd t2, 16(t5)
  ld t2, 24(a0); sd t2, 24(t5)
  ld t2, 0(a1);  sd t2, 32(t5)
  ld t2, 8(a1);  sd t2, 40(t5)
  ld t2, 16(a1); sd t2, 48(t5)
  ld t2, 24(a1); sd t2, 56(t5)
  beqz a6, .Lswr_base_zero
  ld t2, 0(a6);  sd t2, 96(t5)
  ld t2, 8(a6);  sd t2, 104(t5)
  ld t2, 16(a6); sd t2, 112(t5)
  ld t2, 24(a6); sd t2, 120(t5)
  j .Lswr_base_done
.Lswr_base_zero:
  sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5)
.Lswr_base_done:
  addi t1, t1, 1; sd t1, 0(t0)
.Lswr_store:
  ld t2, 0(a2);  sd t2, 64(t5)
  ld t2, 8(a2);  sd t2, 72(t5)
  ld t2, 16(a2); sd t2, 80(t5)
  ld t2, 24(a2); sd t2, 88(t5)
  j .Lswr_done
.Lswr_overflow:
  la t0, tx_storage_writes_overflow; li t1, 1; sd t1, 0(t0); la t0, storage_writes_overflow; sd t1, 0(t0)
.Lswr_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  ld ra, 56(sp); ld a3, 64(sp); ld a4, 72(sp); ld a5, 80(sp)
  ld a6, 88(sp); ld a0, 96(sp)
  addi sp, sp, 112
  ret
