nonstorage_effect_latest_balance:
  li t6, 0                      # found flag
  la t5, exec_nonstorage_effect_count; ld t5, 0(t5)   # count
  la a2, exec_nonstorage_effect_log                   # log base
  li t0, 0                      # entry index i
.Lnelb_loop:
  beq t0, t5, .Lnelb_done
  li t1, 112; mul t1, t0, t1; add t2, a2, t1   # entry ptr = base + i*112
  ld t3, 0(t2);  ld t4, 0(a0);  bne t3, t4, .Lnelb_next   # match addr@0 (32B, 20B addr + 12B zero)
  ld t3, 8(t2);  ld t4, 8(a0);  bne t3, t4, .Lnelb_next
  lwu t3, 16(t2); lwu t4, 16(a0); bne t3, t4, .Lnelb_next  # key bytes 16..19 only
  addi zero, zero, 0; addi zero, zero, 0; addi zero, zero, 0  # byte 20 is mask; 21..31 padding
  ld t3, 64(t2); sd t3, 0(a1)   # post_balance@64 -> out (overwrite keeps the LAST match)
  ld t3, 72(t2); sd t3, 8(a1)
  ld t3, 80(t2); sd t3, 16(a1)
  ld t3, 88(t2); sd t3, 24(a1)
  li t6, 1
.Lnelb_next:
  addi t0, t0, 1; j .Lnelb_loop
.Lnelb_done:
  mv a0, t6
  ret
