bv_mtx_committed_snapshot_append:
  li t0, 0                      # j = 0
.Lcssa_loop:
  beq t0, a2, .Lcssa_done
  bgeu a4, a5, .Lcssa_overflow
  slli t1, t0, 7; add t1, a1, t1   # src = live[j]
  slli t2, a4, 7; add t2, a3, t2   # dst = table[count]
  sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2); sd zero, 24(t2)
  li t3, 0
.Lcssa_addr:
  li t4, 20; beq t3, t4, .Lcssa_addr_done
  add t5, a0, t3; lbu t6, 0(t5); add t5, t2, t3; sb t6, 0(t5); addi t3, t3, 1; j .Lcssa_addr
.Lcssa_addr_done:
  ld t3, 32(t1);  sd t3, 32(t2);  ld t3, 40(t1);  sd t3, 40(t2)
  ld t3, 48(t1);  sd t3, 48(t2);  ld t3, 56(t1);  sd t3, 56(t2)
  ld t3, 64(t1);  sd t3, 64(t2);  ld t3, 72(t1);  sd t3, 72(t2)
  ld t3, 80(t1);  sd t3, 80(t2);  ld t3, 88(t1);  sd t3, 88(t2)
  ld t3, 96(t1);  sd t3, 96(t2);  ld t3, 104(t1); sd t3, 104(t2)
  ld t3, 112(t1); sd t3, 112(t2); ld t3, 120(t1); sd t3, 120(t2)
  addi a4, a4, 1; addi t0, t0, 1; j .Lcssa_loop
.Lcssa_overflow:
  li t0, 1; sd t0, 0(a6); mv a0, a4; li a1, 1; ret
.Lcssa_done:
  mv a0, a4; li a1, 0; ret
