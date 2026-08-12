bal_gas_valid_from_builder:
  addi sp, sp, -96
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0
  la t0, bal_builder_account_count; ld s1, 0(t0)
  la t0, bal_builder_storage_change_count; ld s2, 0(t0)
  li s3, 0
  li s4, 0
  li s6, 0
.Lbgvfb_ch:
  bgeu s3, s2, .Lbgvfb_ch_done
  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add s5, t2, t1
  beqz s4, .Lbgvfb_ch_new
  li t0, 96; mul t1, s6, t0; la t2, bal_builder_storage_changes; add t4, t2, t1
  li t5, 0
.Lbgvfb_ch_acmp:
  li t0, 20; beq t5, t0, .Lbgvfb_ch_scmp
  add t0, s5, t5; add t1, t4, t5
  lbu t2, 0(t0); lbu t3, 0(t1); bne t2, t3, .Lbgvfb_ch_new
  addi t5, t5, 1; j .Lbgvfb_ch_acmp
.Lbgvfb_ch_scmp:
  li t5, 0
.Lbgvfb_ch_scmp_loop:
  li t0, 32; beq t5, t0, .Lbgvfb_ch_next
  addi t0, s5, 32; add t0, t0, t5
  addi t1, t4, 32; add t1, t1, t5
  lbu t2, 0(t0); lbu t3, 0(t1); bne t2, t3, .Lbgvfb_ch_new
  addi t5, t5, 1; j .Lbgvfb_ch_scmp_loop
.Lbgvfb_ch_new:
  addi s1, s1, 1
  mv s6, s3
  li s4, 1
.Lbgvfb_ch_next:
  addi s3, s3, 1; j .Lbgvfb_ch
.Lbgvfb_ch_done:
  la t0, storage_reads_count; ld s2, 0(t0)
  li s3, 0
.Lbgvfb_rd:
  bgeu s3, s2, .Lbgvfb_test
  slli t0, s3, 6; li t1, 0xa1908780; add s5, t1, t0
  li t5, 0
.Lbgvfb_rd_rev:
  li t0, 20; beq t5, t0, .Lbgvfb_rd_chk
  li t0, 19; sub t0, t0, t5; add t0, s5, t0; lbu t1, 0(t0)
  addi t0, sp, 64; add t0, t0, t5; sb t1, 0(t0)
  addi t5, t5, 1; j .Lbgvfb_rd_rev
.Lbgvfb_rd_chk:
  addi a0, s5, 32
  addi a1, sp, 64
  jal ra, bal_serializer_slot_written
  bnez a0, .Lbgvfb_rd_next
  addi s1, s1, 1
.Lbgvfb_rd_next:
  addi s3, s3, 1; j .Lbgvfb_rd
.Lbgvfb_test:
  li t0, 2000
  mul t1, s1, t0
  bltu s0, t1, .Lbgvfb_exceed
  li a0, 0; j .Lbgvfb_ret
.Lbgvfb_exceed:
  li a0, 1
.Lbgvfb_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 96
  ret
