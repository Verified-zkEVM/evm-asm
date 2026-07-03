exec_log_latest_value:
  li t6, 0                      # found flag
  li t0, 0                      # entry index i
.Lelv_loop:
  beq t0, a3, .Lelv_done
  slli t1, t0, 7; add t2, a2, t1   # entry ptr = base + i*128
  # match addrHash (entry@0 vs a0)
  ld t3, 0(t2);  ld t4, 0(a0);  bne t3, t4, .Lelv_next
  ld t3, 8(t2);  ld t4, 8(a0);  bne t3, t4, .Lelv_next
  ld t3, 16(t2); ld t4, 16(a0); bne t3, t4, .Lelv_next
  ld t3, 24(t2); ld t4, 24(a0); bne t3, t4, .Lelv_next
  # match slotKey (entry@32 vs a1)
  ld t3, 32(t2); ld t4, 0(a1);  bne t3, t4, .Lelv_next
  ld t3, 40(t2); ld t4, 8(a1);  bne t3, t4, .Lelv_next
  ld t3, 48(t2); ld t4, 16(a1); bne t3, t4, .Lelv_next
  ld t3, 56(t2); ld t4, 24(a1); bne t3, t4, .Lelv_next
  # matching entry: copy current (entry@96) -> out; set found. Overwrite keeps the LAST match.
  ld t3, 96(t2);  sd t3, 0(a4)
  ld t3, 104(t2); sd t3, 8(a4)
  ld t3, 112(t2); sd t3, 16(a4)
  ld t3, 120(t2); sd t3, 24(a4)
  li t6, 1
.Lelv_next:
  addi t0, t0, 1; j .Lelv_loop
.Lelv_done:
  mv a0, t6
  ret
