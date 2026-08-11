bal_map_account_matches:
  addi sp, sp, -112
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init; bnez a2, .Lbmam_parse; sd a0, 64(sp); sd a1, 72(sp)
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; li t0, 20; bne a2, t0, .Lbmam_miss; sub t0, a0, a2; li t1, 0
.Lbmam_addr:
  li t6, 20; beq t1, t6, .Lbmam_addr_done; add t2, t0, t1; add t3, s2, t1; lbu t4, 0(t2); lbu t5, 0(t3); bne t4, t5, .Lbmam_miss; addi t1, t1, 1; j .Lbmam_addr
.Lbmam_addr_done:
  sd a0, 64(sp); ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2
  li t2, 1; beq s6, t2, .Lbmam_field
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2; li t2, 2; beq s6, t2, .Lbmam_field
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; sd a0, 64(sp); mv t0, a0; sub t0, t0, a2; mv t1, a2
.Lbmam_field:
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmam_parse; mv s0, a0; mv s1, a1
.Lbmam_loop:
  beq s0, s1, .Lbmam_miss; mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; sd s0, 64(sp); sd s1, 72(sp); mv a0, t0; mv a1, t1; jal ra, rlp_walk_init; bnez a2, .Lbmam_parse; mv s0, a0; mv s1, a1; sd s0, 80(sp); sd s1, 88(sp)
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64; bnez a1, .Lbmam_parse; bne a0, s3, .Lbmam_next_tuple
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next; bnez a1, .Lbmam_parse; mv s0, a0; sub t0, a0, a2; mv t1, a2; li t2, 1; beq s6, t2, .Lbmam_balance; li t2, 2; beq s6, t2, .Lbmam_nonce
  bne t1, s5, .Lbmam_next_tuple; li t2, 0
.Lbmam_code_cmp:
  beq t2, s5, .Lbmam_hit; add t3, t0, t2; add t4, s4, t2; lbu t5, 0(t3); lbu t6, 0(t4); bne t5, t6, .Lbmam_next_tuple; addi t2, t2, 1; j .Lbmam_code_cmp
.Lbmam_balance:
  mv a0, t0; mv a1, t1; la a2, bame_value; jal ra, rlp_content_to_u256_be; bnez a0, .Lbmam_parse; la t6, bame_value; ld t2, 0(t6); ld t3, 0(s4); bne t2, t3, .Lbmam_next_tuple; ld t2, 8(t6); ld t3, 8(s4); bne t2, t3, .Lbmam_next_tuple; ld t2, 16(t6); ld t3, 16(s4); bne t2, t3, .Lbmam_next_tuple; ld t2, 24(t6); ld t3, 24(s4); bne t2, t3, .Lbmam_next_tuple; j .Lbmam_hit
.Lbmam_nonce:
  mv a0, t0; mv a1, t1; jal ra, rlp_content_to_u64; bnez a1, .Lbmam_parse; ld t2, 0(s4); beq a0, t2, .Lbmam_hit
.Lbmam_next_tuple:
  ld s0, 64(sp); ld s1, 72(sp); j .Lbmam_loop
.Lbmam_hit:
  li a0, 0; j .Lbmam_ret
.Lbmam_miss:
  li a0, 1; j .Lbmam_ret
.Lbmam_parse:
  li a0, 2
.Lbmam_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 112; ret
