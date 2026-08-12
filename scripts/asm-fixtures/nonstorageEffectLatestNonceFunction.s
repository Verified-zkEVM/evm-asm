# a0 = addr ptr (20B compared), a1 = out u64 ptr -> a0 = 1/0
nonstorage_effect_latest_nonce:
  la t0, exec_nonstorage_effect_log
  la t1, exec_nonstorage_effect_count
  ld t1, 0(t1)
  li t2, 112
  mul t1, t1, t2
  add t1, t0, t1
  li a2, 0
.Lneln_scan:
  beq t0, t1, .Lneln_done
  ld t3, 0(t0); ld t4, 0(a0); bne t3, t4, .Lneln_next
  ld t3, 8(t0); ld t4, 8(a0); bne t3, t4, .Lneln_next
  lw t3, 16(t0); lw t4, 16(a0); bne t3, t4, .Lneln_next
  ld t3, 104(t0); sd t3, 0(a1)
  li a2, 1
.Lneln_next:
  addi t0, t0, 112
  j .Lneln_scan
.Lneln_done:
  mv a0, a2
  ret
