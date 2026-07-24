tx_eip7702_existing_authority_refund:
  addi sp, sp, -176
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  sd a5, 104(sp)              # current block_access_index
  mv s0, a0                   # tx ptr
  mv s1, a1                   # tx len
  mv s2, a2                   # BAL ptr
  mv s3, a3                   # reserved
  mv s4, a4                   # chain id
  # Preserve the caller's sender ABI while this replay derives the current
  # transaction sender.  The legacy charge logic reads bv_stx_sender_addr.
  la t0, bv_stx_sender_addr; la t1, teer_sender_addr
  ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1)
  ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)
  # Recover this transaction's authenticated sender from public_keys[i].
  # Both the multi-tx gas replay and runtime call this helper with the same
  # one-based block index, so this is the single source for the
  # process_transaction sender-nonce increment that precedes auth validation.
  addi a0, a5, -1; li t0, 65; mul a0, a0, t0
  la t0, bv_public_keys_ptr; ld t0, 0(t0); add a0, a0, t0; addi a0, a0, 1
  la a1, bv_stx_sender_addr; jal ra, address_from_pubkey
  li s10, 0                   # accumulated state CHARGE
  la t0, teer_regular_refund; sd zero, 0(t0)   # accumulated regular CHARGE
  la t0, teer_success_count; sd zero, 0(t0)
  la t0, teer_predelegated_count; sd zero, 0(t0)
  la t0, teer_rolled_back; sd zero, 0(t0)
  beqz s2, .Lteer_done
  mv a0, s0; mv a1, s1; la a2, teer_type; la a3, teer_inner_off
  jal ra, tx_type_dispatch
  bnez a0, .Lteer_done
  la t0, teer_type; ld t1, 0(t0); li t2, 4; bne t1, t2, .Lteer_done
  la t0, teer_inner_off; ld t1, 0(t0); add s5, s0, t1; sub s6, s1, t1
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init
  bnez a2, .Lteer_done
  mv s8, a0; mv s9, a1
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s8, a0
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s8, a0
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s8, a0
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s8, a0
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s8, a0
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next; bnez a1, .Lteer_done
  sub t5, a0, a2
  la t0, teer_recipient_ptr; sd t5, 0(t0)
  la t0, teer_recipient_len; sd a2, 0(t0)
  mv s8, a0
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next; bnez a1, .Lteer_done
  snez t5, a2; la t0, teer_value_nonzero; sd t5, 0(t0)
  la t0, teer_inner_off; ld t1, 0(t0); add s5, s0, t1; sub s6, s1, t1
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init
  bnez a2, .Lteer_done
  mv s5, a0; mv s6, a1
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Lteer_done
  sub s5, a0, a2; mv s6, a2
  mv a0, s5; mv a1, s6; la a2, teer_auth_count
  jal ra, rlp_list_count_items
  bnez a0, .Lteer_done
  la t0, teer_auth_count; ld s7, 0(t0)
.Lteer_single_loop_setup:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init
  bnez a2, .Lteer_done
  mv s5, a0; mv s6, a1; li s8, 0
.Lteer_loop:
  beq s8, s7, .Lteer_done
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next
  bnez a1, .Lteer_done
  mv s5, a0; sub s9, a0, a2; sd a2, 136(sp)
  mv a0, s9; ld a1, 136(sp); jal ra, rlp_walk_init
  bnez a2, .Lteer_next
  sd a0, 112(sp); sd a1, 120(sp)
  ld a0, 112(sp); ld a1, 120(sp); jal ra, rlp_walk_next
  bnez a1, .Lteer_next
  sd a0, 112(sp); sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64
  bnez a1, .Lteer_next
  mv t1, a0; beqz t1, .Lteer_chain_ok; bne t1, s4, .Lteer_invalid_auth_full_refund
.Lteer_chain_ok:
  ld a0, 112(sp); ld a1, 120(sp); jal ra, rlp_walk_next
  bnez a1, .Lteer_next
  sd a0, 112(sp); li t2, 20; bne a2, t2, .Lteer_next
  sub s11, a0, a2
  # Preserve target nullness before parsing the authorization nonce.  The RLP
  # helpers are not part of this helper's saved-register ABI, so s11 cannot be
  # treated as stable across the later cursor/content calls.
  mv t2, s11; li t3, 20; li t4, 0
.Lteer_target_nonzero_or:
  beqz t3, .Lteer_target_nonzero_done
  lbu t5, 0(t2); or t4, t4, t5
  addi t2, t2, 1; addi t3, t3, -1; j .Lteer_target_nonzero_or
.Lteer_target_nonzero_done:
  sd t4, 160(sp)
  ld a0, 112(sp); ld a1, 120(sp); jal ra, rlp_walk_next
  bnez a1, .Lteer_next
  sd a0, 112(sp); sub a0, a0, a2; mv a1, a2
  jal ra, rlp_content_to_u64
  bnez a1, .Lteer_next
  mv t1, a0; li t2, -1; beq t1, t2, .Lteer_invalid_auth_full_refund
  sd t1, 144(sp)              # signed authorization nonce
  mv a0, s9; ld a1, 136(sp); la a2, teer_authority; la a3, teer_recover_scratch
  jal ra, eip7702_authorization_recover_address
  bnez a0, .Lteer_invalid_auth_full_refund
  # A prior successfully validated tuple with this exact (authority, nonce)
  # necessarily incremented the live nonce, so this occurrence is invalid.
  # v0.6.0: the same scan also counts prior applied auths for this authority
  # (teer_prior_count -- intra-tx nonce advance + written set) and whether a
  # prior non-NULL set exists (teer_prior_set_flag -- delegation_set_for).
  la t0, teer_prior_count; sd zero, 0(t0)
  la t0, teer_prior_set_flag; sd zero, 0(t0)
  la t0, teer_success_count; ld t1, 0(t0); li t2, 0
.Lteer_success_find_loop:
  beq t2, t1, .Lteer_success_not_found
  slli t3, t2, 5; la t4, teer_success_table; add t3, t3, t4
  la t4, teer_authority; mv t5, t3; li t6, 20
.Lteer_success_addr_cmp:
  beqz t6, .Lteer_success_addr_match
  lbu a6, 0(t4); lbu a7, 0(t5); bne a6, a7, .Lteer_success_find_next
  addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lteer_success_addr_cmp
.Lteer_success_addr_match:
  ld t4, 24(t3); ld t5, 144(sp); beq t4, t5, .Lteer_invalid_auth_full_refund
  la t4, teer_prior_count; ld t5, 0(t4); addi t5, t5, 1; sd t5, 0(t4)
  lw t4, 20(t3); bnez t4, .Lteer_success_find_next
  la t4, teer_prior_set_flag; li t5, 1; sd t5, 0(t4)
.Lteer_success_find_next:
  addi t2, t2, 1; j .Lteer_success_find_loop
.Lteer_success_not_found:
  # S2: after the legacy local scan has established the per-tx prior count,
  # admit against the persistent S1 nonce row.  The single-tx route does not
  # materialize S1, so it deliberately uses that local count as its exact
  # one-transaction delta while retaining the same header-code predicate.
  la a0, bv_eip7702_authority_table
  la t0, bv_eip7702_authority_count; ld a1, 0(t0)
  la a2, teer_authority
  jal ra, eip7702_authority_state_find
  beqz a0, .Lteer_state_row
  la t0, svf_tx_count; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lteer_invalid_auth_full_refund
  sd zero, 152(sp)
  j .Lteer_state_gate
.Lteer_state_row:
  sd a1, 152(sp)
.Lteer_state_gate:
  jal ra, .Lteer_state_admit
  bnez a0, .Lteer_invalid_auth_full_refund
  # S4 commit: S1 has now authenticated this tuple's header-code/nonce
  # admission.  Charge a non-null undelegated -> delegated transition here,
  # before the legacy BAL-final accounting path.  That path intentionally
  # omits self-funded sender authorities after their sender-side nonce/code
  # change, but it must not suppress this protocol state charge.
  ld t4, 160(sp)
  beqz t4, .Lteer_s4_admit_done
  la t0, teer_prior_set_flag; ld t1, 0(t0); bnez t1, .Lteer_s4_admit_done
  ld t0, 152(sp)
  beqz t0, .Lteer_s4_admit_done
  ld t1, 40(t0)
  bnez t1, .Lteer_s4_admit_done
  li t3, 35190
  add s10, s10, t3
  li t1, 1
  sd t1, 40(t0)
.Lteer_s4_admit_done:
  mv a0, s2; mv a1, s3; la a2, teer_authority; la a3, teer_acct_ptr; la a4, teer_acct_len
  jal ra, bal_find_account_by_address
  bnez a0, .Lteer_no_bal_entry
  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0); la a2, teer_finals
  jal ra, bal_account_nonstorage_finals
  bnez a0, .Lteer_next
  la t2, teer_acct_absent; sd zero, 0(t2)
  la t0, teer_records_ptr; ld t0, 0(t0); beqz t0, .Lteer_absent_set_done
  la t1, bfa_index; ld t1, 0(t1); slli t2, t1, 4; slli t3, t1, 3; add t2, t2, t3; add t2, t0, t2
  ld t3, 16(t2); beqz t3, .Lteer_absent_set_done
  la t2, teer_acct_absent; li t3, 1; sd t3, 0(t2)
.Lteer_absent_set_done:
  # execution-specs validate_authorization returns None when recovered authority
  # has non-empty ordinary code, and set_delegation refunds the full auth state
  # charge plus ACCOUNT_WRITE for every None case. In single-tx blocks the header
  # pre-state code is the live authority code at set_delegation time.
  la t0, svf_tx_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lteer_invalid_code_check_done
  la t0, bv_witness_state_ptr; ld a3, 0(t0); beqz a3, .Lteer_invalid_code_check_done
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)
  la a2, teer_authority
  la t0, bv_witness_state_len; ld a4, 0(t0)
  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)
  jal ra, code_at_header_state_root
  bnez a0, .Lteer_invalid_code_check_done
  la t0, cahsr_code_length; ld t1, 0(t0); beqz t1, .Lteer_invalid_code_check_done
  li t2, 23; bne t1, t2, .Lteer_invalid_auth_full_refund
  la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1
  lbu t1, 0(t0); li t2, 0xef; bne t1, t2, .Lteer_invalid_auth_full_refund
  lbu t1, 1(t0); li t2, 0x01; bne t1, t2, .Lteer_invalid_auth_full_refund
  lbu t1, 2(t0); bnez t1, .Lteer_invalid_auth_full_refund
  j .Lteer_invalid_code_check_done
.Lteer_no_bal_entry:
  la t0, teer_acct_ptr; sd zero, 0(t0); la t0, teer_acct_len; sd zero, 0(t0)
  la t0, bv_witness_state_ptr; ld a3, 0(t0); beqz a3, .Lteer_next
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)
  la a2, teer_authority
  la t0, bv_witness_state_len; ld a4, 0(t0)
  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)
  jal ra, code_at_header_state_root
  bnez a0, .Lteer_nbe_code_ok
  la t0, cahsr_code_length; ld t1, 0(t0); beqz t1, .Lteer_nbe_code_ok
  li t2, 23; bne t1, t2, .Lteer_next
  la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1
  lbu t1, 0(t0); li t2, 0xef; bne t1, t2, .Lteer_next
  lbu t1, 1(t0); li t2, 0x01; bne t1, t2, .Lteer_next
  lbu t1, 2(t0); bnez t1, .Lteer_next
.Lteer_nbe_code_ok:
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)
  la a2, teer_authority; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, teer_pre_acct
  jal ra, account_at_header_state_root
  beqz a0, .Lteer_nbe_have_acct
  li t0, 1; bne a0, t0, .Lteer_next
  la t2, teer_acct_absent; li t3, 1; sd t3, 0(t2)
  la t2, teer_rolled_back; li t3, 1; sd t3, 0(t2)
  li t1, 0; j .Lteer_nonce_sender_adjust
.Lteer_nbe_have_acct:
  la t2, teer_acct_absent; sd zero, 0(t2)
  la t2, teer_rolled_back; li t3, 1; sd t3, 0(t2)
  la t0, teer_pre_acct; ld t1, 0(t0)
  j .Lteer_nonce_sender_adjust
.Lteer_invalid_auth_full_refund:
  # v0.6.0: an authorization that fails validate_authorization is
  # skipped -- it charges nothing (the v0.5.0 full-refund is gone with
  # the worst-case intrinsic).
  j .Lteer_next
.Lteer_invalid_code_check_done:
  # validate_authorization compares against the live nonce immediately before
  # this transaction's authorization processing. Recover that value from the
  # latest earlier BAL nonce tuple; fall back to header state when none exists.
  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0); ld a2, 104(sp)
  jal ra, bal_account_nonce_before_index
  beqz a0, .Lteer_nonce_have_live
  li t0, 1; bne a0, t0, .Lteer_nonce_check_done
  la t0, bv_witness_state_ptr; ld t0, 0(t0); beqz t0, .Lteer_nonce_check_done
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)
  la a2, teer_authority; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, teer_pre_acct
  jal ra, account_at_header_state_root
  beqz a0, .Lteer_nonce_have_pre
  li t0, 1; bne a0, t0, .Lteer_nonce_check_done
  li t1, 0; j .Lteer_nonce_sender_adjust
.Lteer_nonce_have_pre:
  la t0, teer_pre_acct; ld t1, 0(t0)        # header-state nonce
  j .Lteer_nonce_sender_adjust
.Lteer_nonce_have_live:
  mv t1, a1                                  # latest prior BAL nonce
.Lteer_nonce_sender_adjust:
  # process_transaction increments the sender nonce before set_delegation.
  # For a self-sponsored authorization the live comparison nonce is therefore
  # header_nonce + 1; other authorities still compare against header_nonce.
  la t2, teer_authority; la t3, bv_stx_sender_addr; li t4, 20
.Lteer_nonce_sender_cmp:
  beqz t4, .Lteer_nonce_sender_match
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lteer_nonce_expected_ready
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lteer_nonce_sender_cmp
.Lteer_nonce_sender_match:
  addi t1, t1, 1
.Lteer_nonce_expected_ready:
  # v0.6.0 generic loop handles repeated authorities: each prior applied
  # auth for this authority advanced the live nonce by one.
  la t2, teer_prior_count; ld t2, 0(t2); add t1, t1, t2
  ld t2, 144(sp); bne t1, t2, .Lteer_invalid_auth_full_refund
.Lteer_nonce_check_done:
  la t0, teer_acct_ptr; ld t1, 0(t0); beqz t1, .Lteer_applied_known
  la t0, teer_finals; ld t1, 40(t0); beqz t1, .Lteer_mark_rolled_back
  la t0, teer_finals; ld t1, 48(t0); ld t2, 144(sp); bgtu t1, t2, .Lteer_applied_known
.Lteer_mark_rolled_back:
  la t0, teer_rolled_back; li t1, 1; sd t1, 0(t0)
.Lteer_applied_known:
  la t0, teer_prior_count; ld t1, 0(t0); bnez t1, .Lteer_charge_auth_base
  la t0, teer_acct_absent; ld t3, 0(t0); beqz t3, .Lteer_charge_account_write
  li t3, 183600
  add s10, s10, t3
.Lteer_charge_account_write:
  la t2, teer_authority; la t3, bv_stx_sender_addr; li t4, 20
.Lteer_aw_sender_cmp:
  beqz t4, .Lteer_charge_auth_base
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lteer_aw_sender_diff
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lteer_aw_sender_cmp
.Lteer_aw_sender_diff:
  la t0, teer_value_nonzero; ld t1, 0(t0); beqz t1, .Lteer_aw_charge
  la t0, teer_recipient_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lteer_aw_charge
  la t2, teer_authority; la t0, teer_recipient_ptr; ld t3, 0(t0); li t4, 20
.Lteer_aw_recip_cmp:
  beqz t4, .Lteer_charge_auth_base
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lteer_aw_charge
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lteer_aw_recip_cmp
.Lteer_aw_charge:
  la t0, teer_regular_refund; ld t4, 0(t0); li t3, 8000; add t4, t4, t3; sd t4, 0(t0)
.Lteer_charge_auth_base:
  mv t2, s11; li t3, 20; li t4, 0
.Lteer_ab_null_or:
  beqz t3, .Lteer_ab_null_ready
  lbu t5, 0(t2); or t4, t4, t5; addi t2, t2, 1; addi t3, t3, -1; j .Lteer_ab_null_or
.Lteer_ab_null_ready:
  # The recovery/BAL helpers may clobber s11.  Use the target-nullness
  # snapshot taken while the RLP target pointer was authoritative.
  ld t4, 160(sp)
  beqz t4, .Lteer_success_append
  la t0, teer_prior_set_flag; ld t1, 0(t0); bnez t1, .Lteer_success_append
  # S4: whenever S1 materialized a persistent authority row, it is the
  # authoritative block-pre delegation classifier.  `svf_tx_count` is a
  # per-dispatch value (one even while processing a multi-tx block), so it
  # must not select the mutable-code legacy path here.
  ld t0, 152(sp)
  beqz t0, .Lteer_ab_legacy_classify
  ld t1, 40(t0)
  bnez t1, .Lteer_success_append
  li t3, 35190
  add s10, s10, t3
  li t1, 1
  sd t1, 40(t0)
  j .Lteer_success_append
.Lteer_ab_legacy_classify:
  la t0, svf_tx_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lteer_ab_multitx
  la t0, bv_witness_state_ptr; ld a3, 0(t0); beqz a3, .Lteer_ab_charge
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)
  la a2, teer_authority
  la t0, bv_witness_state_len; ld a4, 0(t0)
  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)
  jal ra, code_at_header_state_root
  bnez a0, .Lteer_ab_charge
  la t0, cahsr_code_length; ld t0, 0(t0); li t1, 23; bne t0, t1, .Lteer_ab_charge
  la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1
  lbu t1, 0(t0); li t2, 0xef; bne t1, t2, .Lteer_ab_charge
  lbu t1, 1(t0); li t2, 0x01; bne t1, t2, .Lteer_ab_charge
  lbu t1, 2(t0); bnez t1, .Lteer_ab_charge
  la t0, teer_predelegated_count; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  j .Lteer_success_append
.Lteer_ab_multitx:
  # Legacy fallback when S1 has no row: nonce tuples are not delegation
  # evidence, because the sender-side parser may already have advanced this
  # authority's nonce in this same transaction.
  ld t0, 152(sp)
  beqz t0, .Lteer_ab_charge
  ld t1, 40(t0)
  bnez t1, .Lteer_success_append
  li t3, 35190
  add s10, s10, t3
  li t1, 1
  sd t1, 40(t0)
  j .Lteer_success_append
.Lteer_ab_charge:
  li t3, 35190
  add s10, s10, t3
.Lteer_success_append:
  # Record only tuples that have passed the chain/signature/code/nonce gates.
  # This is the commit point for the S1 block-global nonce state: local charge
  # accounting has accepted the tuple, so later transactions observe nonce+1.
  ld t0, 152(sp); beqz t0, .Lteer_state_delta_done; ld t1, 32(t0); addi t1, t1, 1; sd t1, 32(t0)
.Lteer_state_delta_done:
  # Capacity covers the protocol maximum; the guard remains conservative.
  la t0, teer_success_count; ld t1, 0(t0); li t2, 1060; bgeu t1, t2, .Lteer_success_append_done
  slli t2, t1, 5; la t3, teer_success_table; add t2, t2, t3
  la t3, teer_authority; mv t4, t2; li t5, 20
.Lteer_success_copy:
  beqz t5, .Lteer_success_copy_done
  lbu t6, 0(t3); sb t6, 0(t4); addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lteer_success_copy
.Lteer_success_copy_done:
  sw zero, 20(t2); mv t3, s11; li t4, 20
.Lteer_success_target_zero_loop:
  beqz t4, .Lteer_success_target_is_zero
  lbu t5, 0(t3); bnez t5, .Lteer_success_target_flag_done
  addi t3, t3, 1; addi t4, t4, -1; j .Lteer_success_target_zero_loop
.Lteer_success_target_is_zero:
  li t3, 1; sw t3, 20(t2)
.Lteer_success_target_flag_done:
  ld t3, 144(sp); sd t3, 24(t2); addi t1, t1, 1; sd t1, 0(t0)
.Lteer_success_append_done:
.Lteer_next:
  addi s8, s8, 1; j .Lteer_loop
.Lteer_done:
  la t0, teer_sender_addr; la t1, bv_stx_sender_addr
  ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1)
  ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)
  mv a0, s10
  la t0, teer_regular_refund; ld a1, 0(t0)
  la t0, teer_wouldbe_state; sd a0, 0(t0)
  la t0, teer_wouldbe_regular; sd a1, 0(t0)
  la t0, teer_rolled_back; ld t1, 0(t0); beqz t1, .Lteer_ret_applied
  li a0, 0; li a1, 0
.Lteer_ret_applied:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 176
  ret

# S2 state admission subroutine.  The outer frame has already saved the row
# at 152(sp) and signed nonce at 144(sp); keep ra in its unused 128(sp) slot
# across the header-code lookup.
.Lteer_state_admit:
  sd ra, 128(sp)
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0)
  la t0, sv_pre_rlp_len; ld a1, 0(t0)
  la a2, teer_authority
  la t0, bv_witness_state_ptr; ld a3, 0(t0)
  la t0, bv_witness_state_len; ld a4, 0(t0)
  la t0, svf_codes_ptr; ld a5, 0(t0)
  la t0, svf_codes_len; ld a6, 0(t0)
  jal ra, code_at_header_state_root
  beqz a0, .Lteer_state_found
  li t0, 1; beq a0, t0, .Lteer_state_absent
  li t0, 5; beq a0, t0, .Lteer_state_empty_hash
  j .Lteer_state_bad
.Lteer_state_found:
  la t0, cahsr_code_length; ld t1, 0(t0)
  beqz t1, .Lteer_state_header_nonce
  li t2, 23; bne t1, t2, .Lteer_state_bad
  la t0, svf_codes_ptr; ld t0, 0(t0)
  la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1
  lbu t1, 0(t0); li t2, 239; bne t1, t2, .Lteer_state_bad
  lbu t1, 1(t0); li t2, 1; bne t1, t2, .Lteer_state_bad
  lbu t1, 2(t0); bnez t1, .Lteer_state_bad
  j .Lteer_state_header_nonce
.Lteer_state_empty_hash:
  la t0, cahsr_acct_struct; addi t0, t0, 72
  la t1, chahsr_empty_code_hash
  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lteer_state_bad
  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lteer_state_bad
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lteer_state_bad
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lteer_state_bad
  j .Lteer_state_header_nonce
.Lteer_state_absent:
  li t0, 0
  j .Lteer_state_compare
.Lteer_state_header_nonce:
  la t1, cahsr_acct_struct; ld t0, 0(t1)
.Lteer_state_compare:
  ld t1, 152(sp); bnez t1, .Lteer_state_persistent_delta
  la t1, teer_prior_count; ld t1, 0(t1); j .Lteer_state_have_delta
.Lteer_state_persistent_delta:
  ld t1, 32(t1)
.Lteer_state_have_delta:
  add t0, t0, t1
  # process_transaction increments the transaction sender before it walks
  # this authorization list.  Apply that one per-transaction increment here
  # only for a self-funded authority; S1's persistent delta already carries
  # every successfully applied earlier authorization for this authority.
  la t2, teer_authority; la t3, bv_stx_sender_addr; li t4, 20
.Lteer_state_sender_cmp:
  beqz t4, .Lteer_state_sender_match
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lteer_state_compare_signed
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lteer_state_sender_cmp
.Lteer_state_sender_match:
  addi t0, t0, 1
.Lteer_state_compare_signed:
  ld t1, 144(sp); bne t0, t1, .Lteer_state_bad
  li a0, 0
  j .Lteer_state_ret
.Lteer_state_bad:
  li a0, 1
.Lteer_state_ret:
  ld ra, 128(sp)
  ret
