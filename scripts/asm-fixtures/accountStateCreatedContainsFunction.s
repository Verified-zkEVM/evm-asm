account_state_created_contains:
  la t0, account_state_overflow; ld t1, 0(t0); bnez t1, .Lascc_overflow
  la t0, account_state_created_count; ld t1, 0(t0); li t2, 8192; bgtu t1, t2, .Lascc_no; li t2, 0; la t3, account_state_created
.Lascc_entry:
  bgeu t2, t1, .Lascc_no; li t4, 0
.Lascc_bytes:
  li t5, 20; beq t4, t5, .Lascc_yes; add t5, a0, t4; lbu t6, 0(t5); add t5, t3, t4; lbu a1, 0(t5); bne t6, a1, .Lascc_next; addi t4, t4, 1; j .Lascc_bytes
.Lascc_next:
  addi t3, t3, 32; addi t2, t2, 1; j .Lascc_entry
.Lascc_yes:
  li a0, 1; ret
.Lascc_no:
  li a0, 0; ret
.Lascc_overflow:
  li a0, 2; ret
