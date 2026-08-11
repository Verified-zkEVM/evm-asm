bal_map_builder_has_row:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  li t0, 1; bne s4, t0, .Lbamh_nonce; li t0, 32; bne s3, t0, .Lbamh_miss
  la t0, bal_builder_balance_count; ld s4, 0(t0); la s5, bal_builder_balance_changes; li t0, 0
.Lbamh_bal_loop:
  bgeu t0, s4, .Lbamh_miss
  slli t1, t0, 6; add t2, s5, t1; li t3, 0
.Lbamh_bal_addr:
  li t4, 20; beq t3, t4, .Lbamh_bal_bai; add t4, t2, t3; add t5, s0, t3; lbu t6, 0(t4); lbu a4, 0(t5); bne t6, a4, .Lbamh_bal_next; addi t3, t3, 1; j .Lbamh_bal_addr
.Lbamh_bal_bai:
  ld t1, 24(t2); bne t1, s1, .Lbamh_bal_next
  ld t1, 32(t2); ld t3, 0(s2); bne t1, t3, .Lbamh_bal_next; ld t1, 40(t2); ld t3, 8(s2); bne t1, t3, .Lbamh_bal_next; ld t1, 48(t2); ld t3, 16(s2); bne t1, t3, .Lbamh_bal_next; ld t1, 56(t2); ld t3, 24(s2); bne t1, t3, .Lbamh_bal_next; li a0, 0; j .Lbamh_ret
.Lbamh_bal_next:
  addi t0, t0, 1; j .Lbamh_bal_loop
.Lbamh_nonce:
  li t0, 2; bne s4, t0, .Lbamh_code; li t0, 8; bne s3, t0, .Lbamh_miss
  la t0, bal_builder_nonce_count; ld s4, 0(t0); la s5, bal_builder_nonce_changes; li t0, 0
.Lbamh_non_loop:
  bgeu t0, s4, .Lbamh_miss
  slli t1, t0, 5; slli t3, t0, 3; add t1, t1, t3; add t2, s5, t1; li t3, 0
.Lbamh_non_addr:
  li t4, 20; beq t3, t4, .Lbamh_non_bai; add t4, t2, t3; add t5, s0, t3; lbu t6, 0(t4); lbu a4, 0(t5); bne t6, a4, .Lbamh_non_next; addi t3, t3, 1; j .Lbamh_non_addr
.Lbamh_non_bai:
  ld t1, 24(t2); bne t1, s1, .Lbamh_non_next; ld t1, 32(t2); ld t3, 0(s2); bne t1, t3, .Lbamh_non_next; li a0, 0; j .Lbamh_ret
.Lbamh_non_next:
  addi t0, t0, 1; j .Lbamh_non_loop
.Lbamh_code:
  la t0, bal_builder_code_count; ld s4, 0(t0); la s5, bal_builder_code_changes; li t0, 0
.Lbamh_code_loop:
  bgeu t0, s4, .Lbamh_miss; slli t1, t0, 6; add t2, s5, t1; li t3, 0
.Lbamh_code_addr:
  li t4, 20; beq t3, t4, .Lbamh_code_bai; add t4, t2, t3; add t5, s0, t3; lbu t6, 0(t4); lbu a4, 0(t5); bne t6, a4, .Lbamh_code_next; addi t3, t3, 1; j .Lbamh_code_addr
.Lbamh_code_bai:
  ld t1, 24(t2); bne t1, s1, .Lbamh_code_next; ld t1, 40(t2); bne t1, s3, .Lbamh_code_next; ld t1, 32(t2); mv t3, s2; li t4, 0
.Lbamh_code_bytes:
  beq t4, s3, .Lbamh_hit; add t5, t1, t4; add t6, t3, t4; lbu a4, 0(t5); lbu a5, 0(t6); bne a4, a5, .Lbamh_code_next; addi t4, t4, 1; j .Lbamh_code_bytes
.Lbamh_code_next:
  addi t0, t0, 1; j .Lbamh_code_loop
.Lbamh_hit:
  li a0, 0; j .Lbamh_ret
.Lbamh_miss:
  li a0, 1
.Lbamh_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64; ret
