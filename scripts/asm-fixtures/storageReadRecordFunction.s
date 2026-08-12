storage_read_record:
  addi sp, sp, -112
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp); sd ra, 56(sp)
  sd a0, 88(sp); sd a1, 96(sp); sd a2, 104(sp)
  la t0, system_call_mode; ld t0, 0(t0); beqz t0, .Lsrr_tx
  jal ra, storage_read_record_block; j .Lsrr_done
.Lsrr_tx:
  la t0, tx_storage_reads_count; ld t1, 0(t0)
  li t2, 16384
  bgeu t1, t2, .Lsrr_overflow
  li t3, 0xa23349c0
  li t4, 0
.Lsrr_scan:
  bgeu t4, t1, .Lsrr_append
  slli t5, t4, 6; add t5, t3, t5
  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lsrr_next
  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lsrr_next
  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lsrr_next
  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lsrr_next
  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lsrr_next
  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lsrr_next
  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lsrr_next
  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lsrr_next
  j .Lsrr_intern_account
.Lsrr_next:
  addi t4, t4, 1; j .Lsrr_scan
.Lsrr_append:
  slli t5, t1, 6; add t5, t3, t5
  ld t2, 0(a0);  sd t2, 0(t5)
  ld t2, 8(a0);  sd t2, 8(t5)
  ld t2, 16(a0); sd t2, 16(t5)
  ld t2, 24(a0); sd t2, 24(t5)
  ld t2, 0(a1);  sd t2, 32(t5)
  ld t2, 8(a1);  sd t2, 40(t5)
  ld t2, 16(a1); sd t2, 48(t5)
  ld t2, 24(a1); sd t2, 56(t5)
  addi t1, t1, 1; sd t1, 0(t0)
.Lsrr_intern_account:
  addi a1, sp, 64
  jal ra, exec_log_addr_to_bal_canonical
  mv a0, a1; jal ra, bal_builder_ensure_account
  j .Lsrr_done
.Lsrr_overflow:
  la t0, tx_storage_reads_overflow; li t1, 1; sd t1, 0(t0)
.Lsrr_done:
  ld a0, 88(sp); ld a1, 96(sp); ld a2, 104(sp)
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp); ld ra, 56(sp)
  addi sp, sp, 112
  ret
