bal_serializer_slot_to_le:
  la t0, bal_serializer_slot_le; li t1, 32; addi t2, a0, 31
.Lbssl_rev:
  beqz t1, .Lbssl_done
  lbu t3, 0(t2); sb t3, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1
  j .Lbssl_rev
.Lbssl_done:
  ret
