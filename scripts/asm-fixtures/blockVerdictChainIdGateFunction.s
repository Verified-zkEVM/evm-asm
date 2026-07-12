block_verdict_chain_id_gate:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  la t0, bv_tx_list_ptr; ld s0, 0(t0)
  la t0, bv_tx_list_len; ld s1, 0(t0)
  li t0, 4; bltu s1, t0, .Lcig_ok
  mv a0, s0; jal ra, bgv_u32le
  andi t0, a0, 3; bnez t0, .Lcig_ok
  srli s2, a0, 2
  beqz s2, .Lcig_ok
  li s3, 0
.Lcig_loop:
  beq s3, s2, .Lcig_ok
  slli t0, s3, 2; add a0, s0, t0; jal ra, bgv_u32le
  mv s4, a0
  addi t0, s3, 1; beq t0, s2, .Lcig_last
  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le
  mv s5, a0; j .Lcig_have_end
.Lcig_last:
  mv s5, s1
.Lcig_have_end:
  slli t0, s2, 2; bltu s4, t0, .Lcig_ok
  bltu s5, s4, .Lcig_ok
  bltu s1, s5, .Lcig_ok
  add a0, s0, s4; sub a1, s5, s4
  beqz a1, .Lcig_ok
  la a2, cig_type; la a3, cig_inner_off
  jal ra, tx_type_dispatch
  bnez a0, .Lcig_ok
  la t0, cig_type; ld t0, 0(t0)
  bnez t0, .Lcig_typed
  add a0, s0, s4; sub a1, s5, s4; li a2, 6; la a3, cig_off; la a4, cig_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lcig_ok
  la t0, cig_len; ld t1, 0(t0)
  li t2, 16; bgtu t1, t2, .Lcig_reject
  la t0, cig_off; ld t0, 0(t0); add t0, t0, s0; add t0, t0, s4
  li t3, 0; li t4, 0
.Lcig_vdec:
  beqz t1, .Lcig_vdone
  slli t3, t3, 8; srli t5, t4, 56; or t3, t3, t5; slli t4, t4, 8
  lbu t5, 0(t0); or t4, t4, t5
  addi t0, t0, 1; addi t1, t1, -1; j .Lcig_vdec
.Lcig_vdone:
  bnez t3, .Lcig_v_155
  li t5, 27; beq t4, t5, .Lcig_next
  li t5, 28; beq t4, t5, .Lcig_next
.Lcig_v_155:
  la t0, bv_chain_id; ld t5, 0(t0)
  slli t6, t5, 1
  srli t5, t5, 63
  addi t0, t6, 35
  bgeu t0, t6, .Lcig_v_nocarry
  addi t5, t5, 1
.Lcig_v_nocarry:
  bne t3, t5, .Lcig_v_try_odd
  beq t4, t0, .Lcig_next
.Lcig_v_try_odd:
  addi t1, t0, 1
  mv t2, t5
  bnez t1, .Lcig_v_odd_nocarry
  addi t2, t2, 1
.Lcig_v_odd_nocarry:
  bne t3, t2, .Lcig_reject
  bne t4, t1, .Lcig_reject
  j .Lcig_next
.Lcig_typed:
  la t0, cig_inner_off; ld t2, 0(t0)
  add a0, s0, s4; add a0, a0, t2
  sub a1, s5, s4; sub a1, a1, t2
  li a2, 0; la a3, cig_off; la a4, cig_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lcig_ok
  la t0, cig_len; ld t1, 0(t0)
  li t2, 8; bgtu t1, t2, .Lcig_reject
  la t0, cig_off; ld t0, 0(t0); add t0, t0, s0; add t0, t0, s4
  la t3, cig_inner_off; ld t3, 0(t3); add t0, t0, t3
  li t4, 0
.Lcig_cdec:
  beqz t1, .Lcig_cdone
  slli t4, t4, 8; lbu t5, 0(t0); or t4, t4, t5
  addi t0, t0, 1; addi t1, t1, -1; j .Lcig_cdec
.Lcig_cdone:
  la t0, bv_chain_id; ld t5, 0(t0)
  bne t4, t5, .Lcig_reject
.Lcig_next:
  addi s3, s3, 1; j .Lcig_loop
.Lcig_ok:
  li a0, 0
  j .Lcig_ret
.Lcig_reject:
  li a0, 1
.Lcig_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
