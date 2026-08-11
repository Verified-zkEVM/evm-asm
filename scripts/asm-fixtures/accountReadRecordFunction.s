account_read_record:
  addi sp, sp, -64
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  la t0, runtime_tx_account_read_suppress; ld t1, 0(t0); bnez t1, .Larr_done
  la t0, tx_account_reads_count; ld t1, 0(t0)
  li t2, 16384
  bgeu t1, t2, .Larr_overflow
  li t2, 0xa24349c0
  li t3, 0
.Larr_scan:
  bgeu t3, t1, .Larr_append
  slli t4, t3, 5; add t4, t2, t4
  li t5, 0
.Larr_bytes:
  li t6, 20; beq t5, t6, .Larr_done
  add t6, t4, t5; lbu t6, 0(t6)
  add t0, a0, t5; lbu t0, 0(t0)
  bne t6, t0, .Larr_next
  addi t5, t5, 1; j .Larr_bytes
.Larr_next:
  la t0, tx_account_reads_count
  addi t3, t3, 1; j .Larr_scan
.Larr_append:
  slli t4, t1, 5; add t4, t2, t4
  sd zero, 0(t4); sd zero, 8(t4); sd zero, 16(t4); sd zero, 24(t4)
  li t5, 0
.Larr_copy:
  li t6, 20; beq t5, t6, .Larr_bump
  add t6, a0, t5; lbu t6, 0(t6)
  add t0, t4, t5; sb t6, 0(t0)
  addi t5, t5, 1; j .Larr_copy
.Larr_bump:
  la t0, tx_account_reads_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  j .Larr_done
.Larr_overflow:
  la t0, tx_account_reads_overflow; li t1, 1; sd t1, 0(t0)
.Larr_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  addi sp, sp, 64
  ret
