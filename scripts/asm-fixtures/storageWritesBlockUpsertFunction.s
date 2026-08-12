storage_writes_block_upsert:
  addi sp, sp, -64
  sd t0, 0(sp); sd t1, 8(sp); sd t2, 16(sp); sd t3, 24(sp)
  sd t4, 32(sp); sd t5, 40(sp); sd t6, 48(sp)
  la t0, storage_writes_count; ld t1, 0(t0)
  li t3, 2723367360
  li t4, 0
.Lswb_scan:
  bgeu t4, t1, .Lswb_append
  slli t5, t4, 7; add t5, t3, t5
  ld t2, 0(t5);  ld t6, 0(a0);  bne t2, t6, .Lswb_next
  ld t2, 8(t5);  ld t6, 8(a0);  bne t2, t6, .Lswb_next
  ld t2, 16(t5); ld t6, 16(a0); bne t2, t6, .Lswb_next
  ld t2, 24(t5); ld t6, 24(a0); bne t2, t6, .Lswb_next
  ld t2, 32(t5); ld t6, 0(a1);  bne t2, t6, .Lswb_next
  ld t2, 40(t5); ld t6, 8(a1);  bne t2, t6, .Lswb_next
  ld t2, 48(t5); ld t6, 16(a1); bne t2, t6, .Lswb_next
  ld t2, 56(t5); ld t6, 24(a1); bne t2, t6, .Lswb_next
  j .Lswb_store
.Lswb_next:
  addi t4, t4, 1; j .Lswb_scan
.Lswb_append:
  li t2, 66666
  bgeu t1, t2, .Lswb_overflow
  slli t5, t1, 7; add t5, t3, t5
  ld t2, 0(a0);  sd t2, 0(t5)
  ld t2, 8(a0);  sd t2, 8(t5)
  ld t2, 16(a0); sd t2, 16(t5)
  ld t2, 24(a0); sd t2, 24(t5)
  ld t2, 0(a1);  sd t2, 32(t5)
  ld t2, 8(a1);  sd t2, 40(t5)
  ld t2, 16(a1); sd t2, 48(t5)
  ld t2, 24(a1); sd t2, 56(t5)
  beqz a3, .Lswb_base_zero
  ld t2, 0(a3);  sd t2, 96(t5)
  ld t2, 8(a3);  sd t2, 104(t5)
  ld t2, 16(a3); sd t2, 112(t5)
  ld t2, 24(a3); sd t2, 120(t5)
  j .Lswb_base_done
.Lswb_base_zero:
  sd zero, 96(t5); sd zero, 104(t5); sd zero, 112(t5); sd zero, 120(t5)
.Lswb_base_done:
  addi t1, t1, 1; sd t1, 0(t0)
.Lswb_store:
  ld t2, 0(a2);  sd t2, 64(t5)
  ld t2, 8(a2);  sd t2, 72(t5)
  ld t2, 16(a2); sd t2, 80(t5)
  ld t2, 24(a2); sd t2, 88(t5)
  j .Lswb_done
.Lswb_overflow:
  la t0, storage_writes_overflow; li t1, 1; sd t1, 0(t0)
.Lswb_done:
  ld t0, 0(sp); ld t1, 8(sp); ld t2, 16(sp); ld t3, 24(sp)
  ld t4, 32(sp); ld t5, 40(sp); ld t6, 48(sp)
  addi sp, sp, 64
  ret
