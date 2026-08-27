eip7702_auth_state_prepare:
  addi sp, sp, -176; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp); sd a4, 136(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3
  la t0, runtime_tx_auth_state_refund; sd zero, 0(t0); la t0, runtime_tx_auth_state_charge; sd zero, 0(t0); la t0, runtime_tx_auth_regular_refund; sd zero, 0(t0); la t0, runtime_tx_top_frame_regular_gas; sd zero, 0(t0); la t0, teer_success_count; sd zero, 0(t0)
  ld t0, 136(sp); li t1, -1; beq t0, t1, .L77prep_aggregate_mode; la t0, runtime_tx_auth_state_charged; li t1, 1; sd t1, 0(t0)
.L77prep_aggregate_mode:
  li t0, 4; bne s3, t0, .L77prep_ok
  mv a0, s0; mv a1, s1; li a2, 9; la a3, b1an_auth_off; la a4, b1an_auth_len; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_outer
  la t0, b1an_auth_off; ld t0, 0(t0); add s4, s0, t0; la t0, b1an_auth_len; ld s5, 0(t0)
  mv a0, s4; mv a1, s5; la a2, b1an_auth_count; jal ra, rlp_list_count_items; bnez a0, .L77prep_bad_list
  la t0, b1an_auth_count; ld s6, 0(t0); li s7, 0
  mv a0, s0; mv a1, s1; li a2, 5; addi a3, sp, 144; addi a4, sp, 152; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_outer; ld t0, 144(sp); add t0, s0, t0; sd t0, 144(sp)
  mv a0, s0; mv a1, s1; li a2, 6; addi a3, sp, 160; addi a4, sp, 168; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_outer; ld t0, 168(sp); bnez t0, .L77prep_value_nonzero; sd zero, 160(sp); j .L77prep_value_done
.L77prep_value_nonzero:
  li t0, 1; sd t0, 160(sp)
.L77prep_value_done:
.L77prep_loop:
  la t0, runtime_tx_auth_state_charge; sd zero, 0(t0)
  bgeu s7, s6, .L77prep_ok
  mv a0, s4; mv a1, s5; mv a2, s7; la a3, b1an_item_off; la a4, b1an_item_len; jal ra, rlp_item_span; bnez a0, .L77prep_bad_span
  la t0, b1an_item_off; ld t0, 0(t0); add s8, s4, t0; la t0, b1an_item_len; ld s9, 0(t0)
  mv a0, s8; mv a1, s9; li a2, 0; la a3, b1an_target_off; la a4, b1an_target_len; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_chain; la t0, b1an_target_len; ld t0, 0(t0); li t1, 8; bltu t1, t0, .L77prep_chain_wide
  mv a0, s8; mv a1, s9; li a2, 0; la a3, b1an_field; jal ra, rlp_field_to_u64_strict; bnez a0, .L77prep_bad_chain; la t0, b1an_field; ld t0, 0(t0); beqz t0, .L77prep_chain_ok; la t1, bv_chain_id; ld t1, 0(t1); bne t0, t1, .L77prep_next; j .L77prep_chain_ok
.L77prep_chain_wide:
  la t0, b1an_target_off; ld t0, 0(t0); add a0, s8, t0; la t0, b1an_target_len; ld a1, 0(t0); la a2, b1an_recover_scratch; jal ra, rlp_content_to_u256_be_strict; bnez a0, .L77prep_bad_chain; j .L77prep_next
.L77prep_chain_ok:
  mv a0, s8; mv a1, s9; li a2, 2; la a3, b1an_signed_nonce; jal ra, rlp_field_to_u64_strict; bnez a0, .L77prep_bad_nonce; la t0, b1an_signed_nonce; ld t0, 0(t0); li t1, -1; beq t0, t1, .L77prep_next
  mv a0, s8; mv a1, s9; li a2, 1; la a3, b1an_target_off; la a4, b1an_target_len; jal ra, rlp_list_nth_item; bnez a0, .L77prep_bad_target; la t0, b1an_target_off; ld t0, 0(t0); add s10, s8, t0; la t0, b1an_target_len; ld t0, 0(t0); beqz t0, .L77prep_target_maybe_null; li t1, 20; bne t0, t1, .L77prep_next; li s11, 1; li t0, 0
.L77prep_target_zero_loop:
  li t1, 20; beq t0, t1, .L77prep_target_all_zero; add t1, s10, t0; lbu t1, 0(t1); bnez t1, .L77prep_recover; addi t0, t0, 1; j .L77prep_target_zero_loop
.L77prep_target_all_zero:
  li s10, 0; li s11, 0; j .L77prep_recover
.L77prep_target_maybe_null:
  li s10, 0; li s11, 0
.L77prep_target_null:
  li s10, 0; li s11, 0
.L77prep_recover:
  mv a0, s8; mv a1, s9; la a2, b1an_authority; la a3, b1an_recover_scratch; jal ra, eip7702_authorization_recover_address; bnez a0, .L77prep_next
  la a0, b1an_authority; jal ra, eip7702_authority_asof; sd a0, 104(sp); sd a1, 112(sp); sd a2, 120(sp); li t0, 2; bgeu a0, t0, .L77prep_next
  la t0, b1an_signed_nonce; ld t0, 0(t0); ld t1, 112(sp)
  bne t0, t1, .L77prep_next
  li t0, 1; sd t0, 128(sp); sd zero, 168(sp); la t0, teer_success_count; ld t1, 0(t0); li t2, 0
.L77prep_seen_loop:
  bgeu t2, t1, .L77prep_seen_append; slli t3, t2, 5; la t4, teer_success_table; add t4, t4, t3; li t5, 0
.L77prep_seen_cmp:
  li t6, 20; beq t5, t6, .L77prep_seen_found; la t3, b1an_authority; add t3, t3, t5; lbu t6, 0(t3); add t3, t4, t5; lbu t3, 0(t3); bne t6, t3, .L77prep_seen_next; addi t5, t5, 1; j .L77prep_seen_cmp
.L77prep_seen_next:
  addi t2, t2, 1; j .L77prep_seen_loop
.L77prep_seen_found:
  lw t0, 20(t4); sd t0, 168(sp); sd zero, 128(sp); j .L77prep_charges
.L77prep_seen_append:
  li t3, 2144; bgeu t1, t3, .L77prep_bad; slli t3, t1, 5; la t4, teer_success_table; add t4, t4, t3; la t5, b1an_authority; li t6, 0
.L77prep_seen_copy:
  li t3, 20; beq t6, t3, .L77prep_seen_stored; add t3, t5, t6; lbu t3, 0(t3); add a4, t4, t6; sb t3, 0(a4); addi t6, t6, 1; j .L77prep_seen_copy
.L77prep_seen_stored:
  sw zero, 20(t4); la t0, teer_success_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
.L77prep_charges:
  ld t0, 104(sp); bnez t0, .L77prep_no_new; la t0, runtime_tx_auth_state_refund; ld t1, 0(t0); li t2, 183600; add t1, t1, t2; sd t1, 0(t0); la t0, runtime_tx_auth_state_charge; ld t1, 0(t0); add t1, t1, t2; sd t1, 0(t0)
.L77prep_no_new:
  beqz s11, .L77prep_no_auth_base; ld t0, 120(sp); bnez t0, .L77prep_no_auth_base; ld t0, 168(sp); bnez t0, .L77prep_no_auth_base; la t0, runtime_tx_auth_state_refund; ld t1, 0(t0); li t2, 35190; add t1, t1, t2; sd t1, 0(t0); la t0, runtime_tx_auth_state_charge; ld t1, 0(t0); add t1, t1, t2; sd t1, 0(t0); li t0, 1; sw t0, 20(t4)
.L77prep_no_auth_base:
  ld t0, 136(sp); li t1, -1; beq t0, t1, .L77prep_auth_charge_done; la t0, runtime_tx_auth_state_charge; ld t1, 0(t0); beqz t1, .L77prep_auth_charge_done; la t2, evm_state_gas_left; ld t3, 0(t2); bgeu t3, t1, .L77prep_auth_charge_reservoir; sub t4, t1, t3; ld t0, 136(sp); bltu t0, t4, .L77prep_auth_charge_oog; sd zero, 0(t2); sub t0, t0, t4; sd t0, 136(sp); j .L77prep_auth_charge_used
.L77prep_auth_charge_reservoir:
  sub t3, t3, t1; sd t3, 0(t2)
.L77prep_auth_charge_used:
  la t2, runtime_tx_auth_state_charge; sd zero, 0(t2); j .L77prep_auth_charge_done
.L77prep_auth_charge_oog:
  li a0, 2; j .L77prep_ret
.L77prep_auth_charge_done:
.L77prep_regular:
  ld t0, 128(sp); beqz t0, .L77prep_record; la t0, b1an_authority; li t1, 0
.L77prep_sender_cmp:
  li t2, 20; beq t1, t2, .L77prep_not_sender; add t2, t0, t1; lbu t3, 0(t2); add t2, s2, t1; lbu t4, 0(t2); bne t3, t4, .L77prep_not_sender; addi t1, t1, 1; j .L77prep_sender_cmp
.L77prep_not_sender:
  li t2, 20; beq t1, t2, .L77prep_record; ld t0, 160(sp); beqz t0, .L77prep_charge_regular; ld t0, 152(sp); li t1, 20; bne t0, t1, .L77prep_charge_regular; ld t0, 144(sp); la t1, b1an_authority; li t2, 0
.L77prep_recipient_cmp:
  li t3, 20; beq t2, t3, .L77prep_record; add t3, t0, t2; lbu t4, 0(t3); add t3, t1, t2; lbu t3, 0(t3); bne t4, t3, .L77prep_charge_regular; addi t2, t2, 1; j .L77prep_recipient_cmp
.L77prep_charge_regular:
  ld t0, 136(sp); li t1, -1; beq t0, t1, .L77prep_charge_regular_acc
  la t2, runtime_tx_top_frame_regular_gas; ld t3, 0(t2); li t4, 8000; add t3, t3, t4; bltu t0, t3, .L77prep_auth_charge_oog
.L77prep_charge_regular_acc:
  la t0, runtime_tx_auth_regular_refund; ld t1, 0(t0); li t2, 8000; add t1, t1, t2; sd t1, 0(t0); la t0, runtime_tx_top_frame_regular_gas; ld t1, 0(t0); li t2, 8000; add t1, t1, t2; sd t1, 0(t0)
.L77prep_record:
  beqz s11, .L77prep_state_code_null; la t0, eip7702_auth_code_next; ld t1, 0(t0); li t2, 25588; bgeu t1, t2, .L77prep_bad_record; slli t3, t1, 3; slli t4, t1, 4; add t3, t3, t4; la t4, eip7702_auth_code_slots; add s8, t4, t3; addi t1, t1, 1; sd t1, 0(t0); li t0, 0xef; sb t0, 0(s8); li t0, 1; sb t0, 1(s8); sb zero, 2(s8); li t0, 0
.L77prep_state_code_copy:
  li t1, 20; beq t0, t1, .L77prep_state_code_ready; add t1, s10, t0; lbu t2, 0(t1); add t1, s8, t0; addi t1, t1, 3; sb t2, 0(t1); addi t0, t0, 1; j .L77prep_state_code_copy
.L77prep_state_code_null:
  li s8, 0
.L77prep_state_code_ready:
  la t0, exec_code_effect_next; ld t1, 0(t0); addi t2, t1, 48; li t3, 1048576; bgtu t2, t3, .L77prep_code_overflow
  la t3, exec_code_effect_log; add t3, t3, t1; sd zero, 0(t3); sd zero, 8(t3); sd zero, 16(t3); sd zero, 24(t3)
  la t4, b1an_authority; mv t5, t3; li t6, 20
.L77prep_code_addr:
  beqz t6, .L77prep_code_addr_done; lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .L77prep_code_addr
.L77prep_code_addr_done:
  li t4, 1; sd t4, 32(t3); sd zero, 40(t3); la t0, exec_code_effect_count; ld t4, 0(t0); addi t4, t4, 1; sd t4, 0(t0); la t0, exec_code_effect_next; sd t2, 0(t0); j .L77prep_code_done
.L77prep_code_overflow:
  la t0, exec_code_effect_overflow; li t1, 1; sd t1, 0(t0)
.L77prep_code_done:
  la a0, b1an_authority; la a1, nse_zero_bal; la a2, nse_zero_bal; ld a3, 112(sp); addi a4, a3, 1; jal ra, record_nonstorage_effect_nonce_only_after_account_state; bnez a0, .L77prep_bad_record
  la a0, b1an_authority; li a1, 0; ld a2, 112(sp); addi a2, a2, 1; mv a3, s8; li a4, 23; bnez s11, .L77prep_auth_code_record_emit; li a4, 0
.L77prep_auth_code_record_emit:
  li a5, 1; li a6, 62; li a7, 2
  jal ra, account_write_record; j .L77prep_next
.L77prep_next:
  addi s7, s7, 1; j .L77prep_loop
.L77prep_ok:
  li a0, 0; j .L77prep_ret
.L77prep_bad_outer:
.L77prep_bad_list:
.L77prep_bad_span:
.L77prep_bad_chain:
.L77prep_bad_nonce:
.L77prep_bad_target:
.L77prep_bad_record:
.L77prep_bad:
  li a0, 1
.L77prep_ret:
  ld a4, 136(sp); ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp); addi sp, sp, 176; ret
