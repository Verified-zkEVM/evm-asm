bal_serializer_addr_matches:
  li t0, 20; li t1, 0
.Lbsam_cmp:
  beq t1, t0, .Lbsam_yes
  add t2, a0, t1
  li t3, 19; sub t3, t3, t1; add t3, a1, t3
  lbu t4, 0(t2); lbu t5, 0(t3); bne t4, t5, .Lbsam_no
  addi t1, t1, 1; j .Lbsam_cmp
.Lbsam_yes:
  li a0, 1; ret
.Lbsam_no:
  li a0, 0; ret
