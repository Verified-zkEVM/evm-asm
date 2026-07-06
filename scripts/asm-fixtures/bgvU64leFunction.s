bgv_u64le:
  li t0, 0; li t2, 0
.Lbgv64:
  li t3, 8; beq t2, t3, .Lbgv64d
  add t4, a0, t2; lbu t5, 0(t4); slli t6, t2, 3; sll t5, t5, t6; or t0, t0, t5
  addi t2, t2, 1; j .Lbgv64
.Lbgv64d:
  mv a0, t0; ret
