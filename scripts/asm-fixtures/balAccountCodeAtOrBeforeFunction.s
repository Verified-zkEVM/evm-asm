bal_account_code_at_or_before:
  addi sp, sp, -160
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3
  sd zero, 56(s2); sd zero, 64(s2); sd zero, 72(s2); sd zero, 152(sp)
  mv a0, s0; mv a1, s1; li a2, 5; addi a3, sp, 80; addi a4, sp, 88; jal ra, rlp_list_nth_item
  bnez a0, .Lbcab_fail
  ld t0, 80(sp); add s4, s0, t0; ld s5, 88(sp)
  mv a0, s4; mv a1, s5; addi a2, sp, 96; jal ra, rlp_list_count_items
  bnez a0, .Lbcab_fail
  li s6, 0; li s7, 0
.Lbcab_loop:
  ld t0, 96(sp); beq s6, t0, .Lbcab_done
  mv a0, s4; mv a1, s5; mv a2, s6; addi a3, sp, 104; addi a4, sp, 112; jal ra, rlp_list_nth_item
  bnez a0, .Lbcab_fail
  ld t0, 104(sp); add s8, s4, t0; ld t1, 112(sp)
  mv a0, s8; mv a1, t1; li a2, 0; addi a3, sp, 120; jal ra, rlp_field_to_u64_strict
  bnez a0, .Lbcab_fail
  ld t0, 120(sp); bgtu t0, s3, .Lbcab_next; bltu t0, s7, .Lbcab_next
  sd t0, 152(sp); mv a0, s8; ld a1, 112(sp); li a2, 1; addi a3, sp, 128; addi a4, sp, 136; jal ra, rlp_list_nth_item
  bnez a0, .Lbcab_fail
  ld t1, 128(sp); add t1, s8, t1; sub t1, t1, s0; sd t1, 64(s2); ld t1, 136(sp); sd t1, 72(s2); li t1, 1; sd t1, 56(s2); ld s7, 152(sp)
.Lbcab_next:
  addi s6, s6, 1; j .Lbcab_loop
.Lbcab_done:
  li a0, 0; j .Lbcab_ret
.Lbcab_fail:
  li a0, 1
.Lbcab_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 160; ret
