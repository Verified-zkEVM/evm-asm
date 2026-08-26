bal_builder_record_storage_change:
  addi sp, sp, -48; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)
  jal ra, bal_builder_ensure_account; bltz a0, .Lbrsc_overflow
  la t0, bal_builder_storage_change_count; ld t1, 0(t0)
  li t4, 0
.Lbrsc_scan:
  bgeu t4, t1, .Lbrsc_append
  li t2, 96; mul t2, t4, t2; la t3, bal_builder_storage_changes; add t5, t3, t2
  ld t2, 24(t5); ld t6, 16(sp); bne t2, t6, .Lbrsc_next
  ld a4, 24(sp)
  ld t2, 32(t5); ld t6, 0(a4);  bne t2, t6, .Lbrsc_next
  ld t2, 40(t5); ld t6, 8(a4);  bne t2, t6, .Lbrsc_next
  ld t2, 48(t5); ld t6, 16(a4); bne t2, t6, .Lbrsc_next
  ld t2, 56(t5); ld t6, 24(a4); bne t2, t6, .Lbrsc_next
  ld a4, 8(sp); li t2, 20; mv t6, t5
.Lbrsc_acmp:
  beqz t2, .Lbrsc_hit
  lbu a5, 0(a4); lbu a6, 0(t6); bne a5, a6, .Lbrsc_next
  addi a4, a4, 1; addi t6, t6, 1; addi t2, t2, -1; j .Lbrsc_acmp
.Lbrsc_next:
  addi t4, t4, 1; j .Lbrsc_scan
.Lbrsc_hit:
  ld a4, 32(sp)
  ld t2, 0(a4);  sd t2, 64(t5)
  ld t2, 8(a4);  sd t2, 72(t5)
  ld t2, 16(a4); sd t2, 80(t5)
  ld t2, 24(a4); sd t2, 88(t5)
  j .Lbrsc_ret
.Lbrsc_append:
  li t2, 47522
  bgeu t1, t2, .Lbrsc_overflow
  li t2, 96; mul t2, t1, t2; la t3, bal_builder_storage_changes; add t5, t3, t2
  ld a4, 8(sp); li t2, 20; mv t6, t5
.Lbrsc_wa:
  beqz t2, .Lbrsc_wpad; lbu a5, 0(a4); sb a5, 0(t6); addi a4, a4, 1; addi t6, t6, 1; addi t2, t2, -1; j .Lbrsc_wa
.Lbrsc_wpad:
  sb zero, 20(t5); sb zero, 21(t5); sb zero, 22(t5); sb zero, 23(t5)
  ld t2, 16(sp); sd t2, 24(t5)
  ld a4, 24(sp)
  ld t2, 0(a4);  sd t2, 32(t5)
  ld t2, 8(a4);  sd t2, 40(t5)
  ld t2, 16(a4); sd t2, 48(t5)
  ld t2, 24(a4); sd t2, 56(t5)
  ld a4, 32(sp)
  ld t2, 0(a4);  sd t2, 64(t5)
  ld t2, 8(a4);  sd t2, 72(t5)
  ld t2, 16(a4); sd t2, 80(t5)
  ld t2, 24(a4); sd t2, 88(t5)
  addi t1, t1, 1; la t0, bal_builder_storage_change_count; sd t1, 0(t0)
  j .Lbrsc_ret
.Lbrsc_overflow:
  la t0, bal_builder_storage_change_overflow; li t1, 1; sd t1, 0(t0)
  la t0, bal_builder_overflow; sd t1, 0(t0)
.Lbrsc_ret:
  ld ra, 0(sp); addi sp, sp, 48; ret
