bal_serializer_slot_written:
  addi sp, sp, -32; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp)
  la t0, bal_builder_storage_change_count; ld t1, 0(t0)
  li t3, 0
.Lbssw_scan:
  bgeu t3, t1, .Lbssw_no
  li t0, 96; mul t2, t3, t0; la t4, bal_builder_storage_changes; add t4, t4, t2
  ld a2, 8(sp)
  li t5, 32; li t6, 0
.Lbssw_scmp:
  beq t6, t5, .Lbssw_slot_eq
  add t0, a2, t6
  li t2, 31; sub t2, t2, t6; addi t2, t2, 32; add t2, t4, t2
  lbu t0, 0(t0); lbu t2, 0(t2); bne t0, t2, .Lbssw_next
  addi t6, t6, 1; j .Lbssw_scmp
.Lbssw_slot_eq:
  ld a2, 16(sp); li t5, 20; li t6, 0
.Lbssw_acmp:
  beq t6, t5, .Lbssw_yes
  add t0, a2, t6; add t2, t4, t6
  lbu t0, 0(t0); lbu t2, 0(t2); bne t0, t2, .Lbssw_next
  addi t6, t6, 1; j .Lbssw_acmp
.Lbssw_next:
  addi t3, t3, 1; j .Lbssw_scan
.Lbssw_yes:
  li a0, 1; j .Lbssw_ret
.Lbssw_no:
  li a0, 0
.Lbssw_ret:
  ld ra, 0(sp); addi sp, sp, 32; ret
