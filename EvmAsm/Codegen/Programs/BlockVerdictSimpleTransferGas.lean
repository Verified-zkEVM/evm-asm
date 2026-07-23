/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

  Simple-transfer gas publication helper for block_verdict.
-/

import EvmAsm.Codegen.Programs.AmsterdamSystemTx

namespace EvmAsm.Codegen

/-! Compute the EIP-2780 top-frame recipient state-gas charge for an
    empty-code top-level value transfer.

    Result:
      t0 = 0 or StateGasCosts.NEW_ACCOUNT

    Clobbers t0-t6/a0-a4. Requires `s0 = block_verdict params`; `ctxLabel`
    names a simple-transfer/multi-tx context with recipient and value. -/
def topLevelValueRecipientStateGasAsm (tag ctxLabel : String) : String :=
  "  li t0, 0\n" ++
  "  la t1, " ++ ctxLabel ++ "\n" ++
  "  ld t2,  96(t1); ld t3, 104(t1); or t2, t2, t3\n" ++
  "  ld t3, 112(t1); or t2, t2, t3\n" ++
  "  ld t3, 120(t1); or t2, t2, t3\n" ++
  "  beqz t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); addi a2, t1, 72; ld a3, 80(s0); ld a4, 88(s0)\n" ++
  "  jal ra, account_exists_at_header_state_root\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_state_zero\n" ++
  "  la t2, aex_predicate; ld t2, 0(t2)\n" ++
  "  beqz t2, .L" ++ tag ++ "_recipient_state_charge\n" ++
  "  la t1, " ++ ctxLabel ++ "\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); addi a2, t1, 72; ld a3, 80(s0); ld a4, 88(s0)\n" ++
  "  jal ra, account_is_empty_at_header_state_root\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_state_zero\n" ++
  "  la t2, aie_predicate; ld t2, 0(t2)\n" ++
  "  beqz t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  ".L" ++ tag ++ "_recipient_state_charge:\n" ++
  "  la t1, " ++ ctxLabel ++ "\n" ++
  "  la t2, bv_bal_start; ld a0, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a1, 0(t2)\n" ++
  "  addi a2, t1, 72; la a3, bfa_out_ptr; la a4, bfa_out_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_state_apply_charge\n" ++
  "  la t1, bfa_index; ld t1, 0(t1)\n" ++
  "  slli t2, t1, 4; slli t3, t1, 3; add t2, t2, t3; la t3, basr_records; add t2, t3, t2\n" ++
  "  ld t3, 16(t2); bnez t3, .L" ++ tag ++ "_recipient_state_apply_charge\n" ++
  "  ld a0, 0(t2); ld a1, 8(t2); la a2, aie_predicate\n" ++
  "  jal ra, account_is_eip161_empty\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_state_apply_charge\n" ++
  "  la t1, aie_predicate; ld t1, 0(t1); beqz t1, .L" ++ tag ++ "_recipient_state_zero\n" ++
  ".L" ++ tag ++ "_recipient_state_apply_charge:\n" ++
  liAmsterdamNewAccountStateGas "t0" ++
  "  j .L" ++ tag ++ "_recipient_state_done\n" ++
  ".L" ++ tag ++ "_recipient_state_zero:\n" ++
  "  li t0, 0\n" ++
  ".L" ++ tag ++ "_recipient_state_done:\n"

/-! Compute Amsterdam intrinsic regular gas and calldata floor for the non-creation
    simple-transfer shortcut. This mirrors the runtime dispatcher setup path but
    reads calldata/access-list fields from the already extracted simple-transfer
    context, because the shortcut does not call the runtime dispatcher.

    a0 = simple_transfer_tx_context ptr
    returns a0=status, a1=intrinsic_regular, a2=calldata_floor, a3=intrinsic_state. -/
def simpleTransferIntrinsicGasFunction : String :=
  "simple_transfer_intrinsic_gas:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  li s1, 12000                 # Amsterdam TX_BASE\n" ++
  "  li s2, 12000                 # v0.6.0 calldata floor base = TX_BASE + recipient regular gas\n" ++
  "  ld a0, 24(s0); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, bmvmx_sender_addr; addi t1, s0, 72; li t2, 20\n" ++
  ".Lstig_self_cmp:\n" ++
  "  beqz t2, .Lstig_sender_done\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lstig_not_self\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lstig_self_cmp\n" ++
  ".Lstig_not_self:\n" ++
  "  li t5, 3000; add s1, s1, t5; add s2, s2, t5  # COLD_ACCOUNT_ACCESS (also anchors the floor)\n" ++
  "  ld t0, 96(s0); ld t1, 104(s0); or t0, t0, t1\n" ++
  "  ld t1, 112(s0); or t0, t0, t1\n" ++
  "  ld t1, 120(s0); or t0, t0, t1\n" ++
  "  beqz t0, .Lstig_sender_done\n" ++
  "  li t5, 6000; add s1, s1, t5; add s2, s2, t5  # TRANSFER_LOG + TX_VALUE (also anchors the floor)\n" ++
  ".Lstig_sender_done:\n" ++
  "  ld s3, 56(s0)                # calldata ptr\n" ++
  "  ld s4, 64(s0)                # calldata len\n" ++
  ".Lstig_data_loop:\n" ++
  "  beqz s4, .Lstig_access_list\n" ++
  "  lbu t0, 0(s3)\n" ++
  "  beqz t0, .Lstig_zero_byte\n" ++
  "  addi s1, s1, 16\n" ++
  "  addi s2, s2, 64\n" ++
  "  j .Lstig_data_step\n" ++
  ".Lstig_zero_byte:\n" ++
  "  addi s1, s1, 4\n" ++
  "  addi s2, s2, 64\n" ++
  ".Lstig_data_step:\n" ++
  "  addi s3, s3, 1\n" ++
  "  addi s4, s4, -1\n" ++
  "  j .Lstig_data_loop\n" ++
  ".Lstig_access_list:\n" ++
  "  la t0, runtime_tx_access_list_address_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_storage_key_count; sd zero, 0(t0)\n" ++
  "  ld t0, 160(s0)\n" ++
  "  beqz t0, .Lstig_store_done\n" ++
  "  li a2, 7; li t1, 1; beq t0, t1, .Lstig_access_field\n" ++
  "  li a2, 8; li t1, 2; beq t0, t1, .Lstig_access_field\n" ++
  "  li t1, 3; beq t0, t1, .Lstig_access_field\n" ++
  "  li t1, 4; beq t0, t1, .Lstig_access_field\n" ++
  "  j .Lstig_store_done\n" ++
  ".Lstig_access_field:\n" ++
  "  ld a0, 176(s0); ld a1, 184(s0); la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  ld t0, 176(s0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, bsg_access_len; ld a1, 0(t1)\n" ++
  "  la a2, runtime_tx_access_list_address_count; la a3, runtime_tx_access_list_storage_key_count\n" ++
  "  jal ra, access_list_count\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  la t0, runtime_tx_access_list_address_count; ld t1, 0(t0)\n" ++
  ".Lstig_addr_loop:\n" ++
  "  beqz t1, .Lstig_slot_count\n" ++
  "  li t2, 4280\n" ++
  "  add s1, s1, t2\n" ++
  "  li t2, 1280\n" ++
  "  add s2, s2, t2\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lstig_addr_loop\n" ++
  ".Lstig_slot_count:\n" ++
  "  la t0, runtime_tx_access_list_storage_key_count; ld t1, 0(t0)\n" ++
  ".Lstig_slot_loop:\n" ++
  "  beqz t1, .Lstig_store_done\n" ++
  "  li t2, 5048\n" ++
  "  add s1, s1, t2\n" ++
  "  li t2, 2048\n" ++
  "  add s2, s2, t2\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lstig_slot_loop\n" ++
  ".Lstig_store_done:\n" ++
  "  ld t0, 160(s0); li t1, 4; bne t0, t1, .Lstig_auth_done\n" ++
  "  ld a0, 176(s0); ld a1, 184(s0); li a2, 9; la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  ld t0, 176(s0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, bsg_access_len; ld a1, 0(t1); la a2, teer_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  -- v0.6.0: REGULAR_PER_AUTH_BASE_COST 7816 only (ACCOUNT_WRITE 8000
  -- left the intrinsic; charged exactly by the auth replay).
  "  la t0, teer_auth_count; ld t1, 0(t0); li t2, 7816; mul t1, t1, t2; add s1, s1, t1\n" ++
  ".Lstig_auth_done:\n" ++
  "  la t0, runtime_tx_calldata_floor; sd s2, 0(t0)\n" ++
  "  la t0, runtime_tx_intrinsic_regular; sd s1, 0(t0)\n" ++
  "  sd s1, 48(sp); sd s2, 56(sp)\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_runtime_intrinsic_state_gas\n" ++
  "  jal ra, tx_intrinsic_state_gas\n" ++
  "  bnez a0, .Lstig_fail\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0)\n" ++
  "  la t0, bv_bal_start; ld a2, 0(t0); la t0, bv_bal_len; ld a3, 0(t0)\n" ++
  "  la t0, teer_records_ptr; la t1, basr_records; sd t1, 0(t0)\n" ++
  "  la t0, bv_chain_id; ld a4, 0(t0); li a5, 1\n" ++
  "  jal ra, tx_eip7702_existing_authority_refund_with_sender_nonce\n" ++
  -- v0.6.0: fold the WOULD-BE charges (state into the state dimension,
  -- ACCOUNT_WRITE regular into the intrinsic-regular output/cell) so
  -- every simple-transfer consumer reproduces the spec's charge-point
  -- OOG; the v0.5.0 refund subtraction is gone with the flip.
  "  la t2, teer_wouldbe_state; ld t2, 0(t2)\n" ++
  "  la t0, bv_runtime_intrinsic_state_gas; ld t1, 0(t0); add t1, t1, t2; sd t1, 0(t0)\n" ++
  "  ld s1, 48(sp); ld s2, 56(sp)\n" ++
  "  la t2, teer_wouldbe_regular; ld t2, 0(t2); add s1, s1, t2\n" ++
  "  la t0, runtime_tx_intrinsic_regular; sd s1, 0(t0)\n" ++
  "  li a0, 0; mv a1, s1; mv a2, s2; mv a3, t1\n" ++
  "  j .Lstig_ret\n" ++
  ".Lstig_fail:\n" ++
  "  li a0, 1; li a1, 0; li a2, 0; li a3, 0\n" ++
  ".Lstig_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n"


end EvmAsm.Codegen
