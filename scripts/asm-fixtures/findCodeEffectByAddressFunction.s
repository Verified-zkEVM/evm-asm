find_code_effect_by_address:
  mv t0, a0                   # cursor (entry base)
  mv t1, a1                   # remaining count
.Lfce_loop:
  beqz t1, .Lfce_none
  mv t2, t0; mv t3, a2; li t4, 20
.Lfce_cmp:
  beqz t4, .Lfce_found
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lfce_next
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lfce_cmp
.Lfce_next:
  ld t5, 40(t0); addi t5, t5, 55; andi t5, t5, -8   # stride = round8(48 + code_len)
  add t0, t0, t5; addi t1, t1, -1; j .Lfce_loop
.Lfce_found:
  mv a0, t0; ret
.Lfce_none:
  li a0, 0; ret
