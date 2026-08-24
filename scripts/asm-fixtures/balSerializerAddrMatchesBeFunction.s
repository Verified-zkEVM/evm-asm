bal_serializer_addr_matches_be:
  li t0, 20; li t1, 0
.Lbsab_cmp:
  beq t1, t0, .Lbsab_yes
  add t2, a0, t1; add t3, a1, t1
  lbu t4, 0(t2); lbu t5, 0(t3); bne t4, t5, .Lbsab_no
  addi t1, t1, 1; j .Lbsab_cmp
.Lbsab_yes:
  li a0, 1; ret
.Lbsab_no:
  li a0, 0; ret
