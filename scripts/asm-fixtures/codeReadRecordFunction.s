code_read_record:
  addi sp, sp, -64
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  la t0, tx_code_reads_count; ld t1, 0(t0)
  li t2, 8192
  bgeu t1, t2, .Lcrr_overflow
  li t2, 0xa24b49c0
  li t3, 0
.Lcrr_scan:
  bgeu t3, t1, .Lcrr_append
  slli t4, t3, 6; add t4, t2, t4
  li t5, 0
.Lcrr_cmp_addr:
  li t6, 20; beq t5, t6, .Lcrr_cmp_hash
  add t6, t4, t5; lbu t6, 0(t6)
  add t0, a0, t5; lbu t0, 0(t0)
  bne t6, t0, .Lcrr_next
  addi t5, t5, 1; j .Lcrr_cmp_addr
.Lcrr_cmp_hash:
  li t5, 0
.Lcrr_cmp_hash_loop:
  li t6, 32; beq t5, t6, .Lcrr_done
  add t6, t4, t5; lbu t6, 32(t6)
  add t0, a1, t5; lbu t0, 0(t0)
  bne t6, t0, .Lcrr_next
  addi t5, t5, 1; j .Lcrr_cmp_hash_loop
.Lcrr_next:
  la t0, tx_code_reads_count
  addi t3, t3, 1; j .Lcrr_scan
.Lcrr_append:
  slli t4, t1, 6; add t4, t2, t4
  sd zero, 0(t4); sd zero, 8(t4); sd zero, 16(t4); sd zero, 24(t4)
  li t5, 0
.Lcrr_cp_addr:
  li t6, 20; beq t5, t6, .Lcrr_cp_hash
  add t6, a0, t5; lbu t6, 0(t6)
  add t0, t4, t5; sb t6, 0(t0)
  addi t5, t5, 1; j .Lcrr_cp_addr
.Lcrr_cp_hash:
  li t5, 0
.Lcrr_cp_hash_loop:
  li t6, 32; beq t5, t6, .Lcrr_bump
  add t6, a1, t5; lbu t6, 0(t6)
  add t0, t4, t5; sb t6, 32(t0)
  addi t5, t5, 1; j .Lcrr_cp_hash_loop
.Lcrr_bump:
  la t0, tx_code_reads_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  j .Lcrr_done
.Lcrr_overflow:
  la t0, tx_code_reads_overflow; li t1, 1; sd t1, 0(t0)
.Lcrr_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  addi sp, sp, 64
  ret
