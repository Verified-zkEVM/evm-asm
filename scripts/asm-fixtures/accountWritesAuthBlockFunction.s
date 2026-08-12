account_writes_auth_block:
  addi sp, sp, -40; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); mv s0, a0; mv s1, a1; mv s2, a2; mv a0, s0; jal ra, account_read_record
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lawab_loop:
  bgeu t3, t1, .Lawab_miss; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawab_cmp:
  beqz t6, .Lawab_key; lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4, .Lawab_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawab_cmp
.Lawab_next:
  addi t3, t3, 1; j .Lawab_loop
.Lawab_key:
  ld t0, 112(t5); andi t1, t0, 2; beqz t1, .Lawab_next; andi t1, t0, 8; beqz t1, .Lawab_next; andi t1, t0, 16; beqz t1, .Lawab_next
  ld t1, 64(t5); sd t1, 0(s1); ld t1, 96(t5); sd t1, 0(s2); andi t1, t0, 4; beqz t1, .Lawab_no_code; ld a1, 80(t5); ld a2, 88(t5); j .Lawab_code_ready
.Lawab_no_code:
  li a1, 0; li a2, 0
.Lawab_code_ready:
  ld t1, 96(t5); andi t1, t1, 2; bnez t1, .Lawab_live; li a0, 2; j .Lawab_ret
.Lawab_live:
  li a0, 1; j .Lawab_ret
.Lawab_miss:
  li a0, 0; li a1, 0; li a2, 0
.Lawab_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 40; ret
