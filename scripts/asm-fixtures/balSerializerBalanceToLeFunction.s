bal_serializer_balance_to_le:
  la t0, bal_serializer_balance_le; li t1, 32; addi t2, a0, 31
.Lbsbl_rev:
  beqz t1, .Lbsbl_done
  lbu t3, 0(t2); sb t3, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1
  j .Lbsbl_rev
.Lbsbl_done:
  ret
