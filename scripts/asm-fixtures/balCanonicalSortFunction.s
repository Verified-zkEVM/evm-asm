bal_canonical_sort:
  addi sp, sp, -112
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  li t0, 1; bltu a4, t0, .Lbalsort_bad_segs
  li t0, 3; bgtu a4, t0, .Lbalsort_bad_segs
  j .Lbalsort_segs_ok
.Lbalsort_bad_segs:
  li a0, 2; j .Lbalsort_ret
.Lbalsort_segs_ok:
  beqz a5, .Lbalsort_over_capacity; bltu a5, a1, .Lbalsort_over_capacity
  mv s0, a0
  mv s1, a1
  mv s8, a2
  mv s10, a3
  li s9, 0; li t1, 0
.Lbalsort_keysum:
  bgeu t1, a4, .Lbalsort_keysummed
  slli t2, t1, 4; addi t2, t2, 8; srl t0, s10, t2; andi t0, t0, 0x7f
  add s9, s9, t0; addi t1, t1, 1; j .Lbalsort_keysum
.Lbalsort_keysummed:
  beqz s9, .Lbalsort_bad_segs
  slli s11, s9, 1
  la s2, bal_sort_ranges; li s3, 0
  li t0, 2; bltu s1, t0, .Lbalsort_ok
  sd zero, 0(s2); sd s1, 8(s2); sd zero, 16(s2); sd zero, 24(s2); li s3, 1
.Lbalsort_pop:
  beqz s3, .Lbalsort_ok
  addi s3, s3, -1; slli t0, s3, 5; add t0, s2, t0
  ld s4, 0(t0); ld s5, 8(t0); ld s6, 16(t0)
  addi t1, s4, 1; bgeu t1, s5, .Lbalsort_pop
  bgeu s6, s11, .Lbalsort_pop
  mv s7, s4; li t6, 0
.Lbalsort_digit:
  li t0, 16; beq t6, t0, .Lbalsort_pop
  mv t1, s7
.Lbalsort_scan:
  beq t1, s5, .Lbalsort_group
  mul t0, t1, s8; add t0, s0, t0
  srli t2, s6, 1
  li a6, 0
.Lbalsort_dig_seg:
  slli a7, a6, 4; srl t5, s10, a7; andi t5, t5, 255
  addi a7, a7, 8; srl t3, s10, a7; andi t3, t3, 0x7f
  bltu t2, t3, .Lbalsort_dig_in
  sub t2, t2, t3; addi a6, a6, 1; j .Lbalsort_dig_seg
.Lbalsort_dig_in:
  slli a7, a6, 4; addi a7, a7, 8; srl a7, s10, a7; andi a7, a7, 0x80
  bnez a7, .Lbalsort_dig_be
  add t5, t5, t3; addi t5, t5, -1; sub t5, t5, t2
  j .Lbalsort_dig_have
.Lbalsort_dig_be:
  add t5, t5, t2
.Lbalsort_dig_have:
  add t5, t0, t5; lbu t3, 0(t5)
  andi a7, s6, 1; bnez a7, .Lbalsort_dig_low
  srli t3, t3, 4
.Lbalsort_dig_low:
  andi t3, t3, 15
  bne t3, t6, .Lbalsort_scan_next
  beq t1, s7, .Lbalsort_scan_match
  mul t2, s7, s8; add t2, s0, t2
  mv t4, s8
.Lbalsort_swap:
  ld t5, 0(t0); ld a5, 0(t2); sd a5, 0(t0); sd t5, 0(t2)
  addi t0, t0, 8; addi t2, t2, 8; addi t4, t4, -8; bnez t4, .Lbalsort_swap
.Lbalsort_scan_match:
  addi s7, s7, 1
.Lbalsort_scan_next:
  addi t1, t1, 1; j .Lbalsort_scan
.Lbalsort_group:
  addi t0, s4, 1; bgeu t0, s7, .Lbalsort_digit_next
  li t0, 2048; bgeu s3, t0, .Lbalsort_stack_full
  slli t0, s3, 5; add t0, s2, t0
  sd s4, 0(t0); sd s7, 8(t0); addi t1, s6, 1; sd t1, 16(t0); sd zero, 24(t0)
  addi s3, s3, 1
.Lbalsort_digit_next:
  mv s4, s7; addi t6, t6, 1; j .Lbalsort_digit
.Lbalsort_over_capacity:
  li a0, 1; j .Lbalsort_ret
.Lbalsort_stack_full:
  li a0, 3; j .Lbalsort_ret
.Lbalsort_ok:
  li a0, 0
.Lbalsort_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
