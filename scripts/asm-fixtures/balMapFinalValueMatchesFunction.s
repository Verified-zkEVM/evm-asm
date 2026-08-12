bal_map_final_value_matches:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0; mv s1, a1; li t0, 1; beq s1, t0, .Lbmfv_balance; li t0, 2; beq s1, t0, .Lbmfv_nonce; li t0, 3; beq s1, t0, .Lbmfv_code; j .Lbmfv_miss
.Lbmfv_balance:
  ld t0, 112(s0); li t1, 1; and t0, t0, t1; beqz t0, .Lbmfv_ok; la t0, bal_builder_balance_count; ld s2, 0(t0); la s3, bal_builder_balance_changes; li s4, 0; li s7, 0
.Lbmfv_bal_loop:
  bgeu s4, s2, .Lbmfv_bal_done; slli t0, s4, 6; add t1, s3, t0; li t2, 20; mv t3, t1; mv t4, s0
.Lbmfv_bal_addr:
  beqz t2, .Lbmfv_bal_candidate; lbu t5, 0(t3); lbu t6, 0(t4); bne t5, t6, .Lbmfv_bal_next; addi t3, t3, 1; addi t4, t4, 1; addi t2, t2, -1; j .Lbmfv_bal_addr
.Lbmfv_bal_candidate:
  ld t2, 24(t1); beqz s7, .Lbmfv_bal_take; bltu t2, s6, .Lbmfv_bal_next
.Lbmfv_bal_take:
  mv s5, t1; mv s6, t2; li s7, 1
.Lbmfv_bal_next:
  addi s4, s4, 1; j .Lbmfv_bal_loop
.Lbmfv_bal_done:
  beqz s7, .Lbmfv_ok; ld t0, 32(s0); ld t1, 32(s5); bne t0, t1, .Lbmfv_miss; ld t0, 40(s0); ld t1, 40(s5); bne t0, t1, .Lbmfv_miss; ld t0, 48(s0); ld t1, 48(s5); bne t0, t1, .Lbmfv_miss; ld t0, 56(s0); ld t1, 56(s5); bne t0, t1, .Lbmfv_miss; j .Lbmfv_ok
.Lbmfv_nonce:
  ld t0, 112(s0); li t1, 2; and t0, t0, t1; beqz t0, .Lbmfv_ok; la t0, bal_builder_nonce_count; ld s2, 0(t0); la s3, bal_builder_nonce_changes; li s4, 0; li s7, 0
.Lbmfv_non_loop:
  bgeu s4, s2, .Lbmfv_non_done; slli t0, s4, 5; slli t2, s4, 3; add t0, t0, t2; add t1, s3, t0; li t2, 20; mv t3, t1; mv t4, s0
.Lbmfv_non_addr:
  beqz t2, .Lbmfv_non_candidate; lbu t5, 0(t3); lbu t6, 0(t4); bne t5, t6, .Lbmfv_non_next; addi t3, t3, 1; addi t4, t4, 1; addi t2, t2, -1; j .Lbmfv_non_addr
.Lbmfv_non_candidate:
  ld t2, 24(t1); beqz s7, .Lbmfv_non_take; bltu t2, s6, .Lbmfv_non_next; bne t2, s6, .Lbmfv_non_take; ld t3, 32(t1); ld t4, 32(s5); bgeu t4, t3, .Lbmfv_non_next
.Lbmfv_non_take:
  mv s5, t1; mv s6, t2; li s7, 1
.Lbmfv_non_next:
  addi s4, s4, 1; j .Lbmfv_non_loop
.Lbmfv_non_done:
  beqz s7, .Lbmfv_ok; ld t0, 64(s0); ld t1, 32(s5); bne t0, t1, .Lbmfv_miss; j .Lbmfv_ok
.Lbmfv_code:
  ld t0, 112(s0); li t1, 4; and t0, t0, t1; beqz t0, .Lbmfv_ok; la t0, bal_builder_code_count; ld s2, 0(t0); la s3, bal_builder_code_changes; li s4, 0; li s7, 0
.Lbmfv_code_loop:
  bgeu s4, s2, .Lbmfv_code_done; slli t0, s4, 6; add t1, s3, t0; li t2, 20; mv t3, t1; mv t4, s0
.Lbmfv_code_addr:
  beqz t2, .Lbmfv_code_candidate; lbu t5, 0(t3); lbu t6, 0(t4); bne t5, t6, .Lbmfv_code_next; addi t3, t3, 1; addi t4, t4, 1; addi t2, t2, -1; j .Lbmfv_code_addr
.Lbmfv_code_candidate:
  ld t2, 24(t1); beqz s7, .Lbmfv_code_take; bltu t2, s6, .Lbmfv_code_next
.Lbmfv_code_take:
  mv s5, t1; mv s6, t2; li s7, 1
.Lbmfv_code_next:
  addi s4, s4, 1; j .Lbmfv_code_loop
.Lbmfv_code_done:
  beqz s7, .Lbmfv_ok; ld s2, 88(s0); ld s3, 80(s0); ld s6, 32(s5); li s4, 0
.Lbmfv_code_bytes:
  beq s4, s2, .Lbmfv_ok; add t0, s3, s4; add t1, s6, s4; lbu t2, 0(t0); lbu t3, 0(t1); bne t2, t3, .Lbmfv_miss; addi s4, s4, 1; j .Lbmfv_code_bytes
.Lbmfv_ok:
  li a0, 0; j .Lbmfv_ret
.Lbmfv_miss:
  li a0, 1
.Lbmfv_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 80; ret
