/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxEoa

  Multi-tx EOA recipient settlement fragment for block_verdict.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

namespace EvmAsm.Codegen

/-- Multi-tx EOA recipient settlement fragment, concatenated at the empty-code
    recipient branch in `block_verdict`. -/
def blockVerdictMtxEoaSettlement : String :=
  "  j .Lbv_mtx_is_eoa\n" ++
  ".Lbv_mtx_is_eoa:\n" ++
  -- fhsxz.2.4.2.63.1.6.2.7.3.1: multi-tx EOA recipient settlement.
  -- Empty-code recipients execute the canonical STOP body, so reuse the same
  -- stage_runtime_payload + runtime_dispatcher_call gas path as the single-tx
  -- EOA branch, but store into the strided multi-tx result arrays. This makes
  -- receipt gas/status/log windows complete for all-EOA multi-tx value blocks.
  "  la a0, bv_mtx_ctx\n" ++
  "  la a1, bv_runtime_payload\n" ++
  "  la t2, bv_exec_p; ld a2, 0(t2)\n" ++
  "  la a3, bv_stop_code\n" ++
  "  li a4, 1\n" ++
  "  li a5, 0\n" ++
  "  li a6, 0\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  "  la t0, runtime_tx_access_list_address_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_storage_key_count; sd zero, 0(t0)\n" ++
  "  la t6, bv_mtx_ctx; ld t0, 160(t6); beqz t0, .Lbv_mtx_eoa_access_ready\n" ++
  "  li t1, 1; li a2, 7; beq t0, t1, .Lbv_mtx_eoa_access_field\n" ++
  "  li a2, 8; li t1, 2; beq t0, t1, .Lbv_mtx_eoa_access_field\n" ++
  "  li t1, 3; beq t0, t1, .Lbv_mtx_eoa_access_field\n" ++
  "  li t1, 4; bne t0, t1, .Lbv_mtx_bail\n" ++
  ".Lbv_mtx_eoa_access_field:\n" ++
  "  ld a0, 176(t6); ld a1, 184(t6); la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  "  la t6, bv_mtx_ctx; la t0, bsg_access_off; ld t0, 0(t0); ld a0, 176(t6); add a0, a0, t0\n" ++
  "  la t0, bsg_access_len; ld a1, 0(t0)\n" ++
  "  la a2, runtime_tx_access_list_address_count; la a3, runtime_tx_access_list_storage_key_count\n" ++
  "  jal ra, access_list_count\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  ".Lbv_mtx_eoa_access_ready:\n" ++
  -- Mirror dispatch_tx_runtime_code's EIP-7702 setup. The low-level EOA STOP
  -- shortcut still runs process_message_call semantics: authorization intrinsic
  -- charges, state refill, ACCOUNT_WRITE refund, and recovered-authority warming
  -- must therefore be staged before runtime_dispatcher_call as well.
  "  la t0, runtime_tx_auth_list_ptr; sd zero, 0(t0); la t0, runtime_tx_auth_list_len; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_warm_fn; sd zero, 0(t0); la t0, runtime_tx_auth_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_state_refund; sd zero, 0(t0); la t0, runtime_tx_auth_regular_refund; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_top_frame_regular_gas; sd zero, 0(t0)\n" ++
  "  la t6, bv_mtx_ctx; ld t0, 160(t6); li t1, 4; bne t0, t1, .Lbv_mtx_eoa_auth_ready\n" ++
  "  ld a0, 176(t6); ld a1, 184(t6); li a2, 9; la a3, dtrc_auth_off; la a4, dtrc_auth_len\n" ++
  "  jal ra, rlp_list_nth_item; bnez a0, .Lbv_mtx_bail\n" ++
  "  la t6, bv_mtx_ctx; ld t0, 176(t6); la t1, dtrc_auth_off; ld t1, 0(t1); add t2, t0, t1\n" ++
  "  la t0, runtime_tx_auth_list_ptr; sd t2, 0(t0); la t1, dtrc_auth_len; ld t2, 0(t1); la t0, runtime_tx_auth_list_len; sd t2, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_warm_fn; la t1, eip7702_warm_recovered_authorities; sd t1, 0(t0)\n" ++
  "  la t0, teer_records_ptr; la t1, basr_records; sd t1, 0(t0)\n" ++
  "  la t6, bv_mtx_ctx; ld a0, 8(t6); ld a1, 16(t6); la t0, bv_bal_start; ld a2, 0(t0); la t0, bv_bal_len; ld a3, 0(t0)\n" ++
  "  la t0, bv_chain_id; ld a4, 0(t0); la t0, bv_mtx_i; ld a5, 0(t0); addi a5, a5, 1\n" ++
  "  jal ra, tx_eip7702_existing_authority_refund\n" ++
  "  la t0, runtime_tx_auth_state_refund; sd a0, 0(t0); la t0, runtime_tx_auth_regular_refund; sd a1, 0(t0)\n" ++
  -- v0.6.0: the exact ACCOUNT_WRITE regular charge is applied at the top
  -- frame pre-dispatch (the callable-dispatcher setup consumes this cell).
  "  la t0, runtime_tx_top_frame_regular_gas; sd a1, 0(t0)\n" ++
  "  la t0, teer_auth_count; ld t1, 0(t0); la t0, runtime_tx_auth_count; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_eoa_auth_ready:\n" ++
  -- This shortcut calls the low-level STOP dispatcher directly, bypassing the
  -- full dispatch_tx_runtime_code setup reset. Reset the per-tx gas cells here
  -- so EIP-8037 state-gas accounting starts from this transaction's state, not
  -- the previous user/system call.
  "  la t0, evm_refund_acc; sd zero, 0(t0)\n" ++
  "  la t0, evm_state_gas_left; sd zero, 0(t0)\n" ++
  "  la t0, evm_state_gas_used; sd zero, 0(t0)\n" ++
  "  la t4, runtime_dispatcher_input_ptr; la t5, bv_runtime_payload; addi t5, t5, 8; sd t5, 0(t4)\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp)\n" ++
  "  jal ra, runtime_dispatcher_call\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  la t4, runtime_dispatcher_input_ptr; sd zero, 0(t4)\n" ++
  -- EIP-7708 top-level value-transfer log. STOP has no recipient logs, so
  -- emitting after dispatch preserves the spec log order for EOA recipients.
  "  la t0, bv_mtx_ctx; addi t0, t0, 96; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbv_mtx_eoa_tl7708_skip\n" ++
  "  la t0, bv_mtx_sender_addr; la t1, bv_mtx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_mtx_eoa_tl_selfcmp:\n" ++
  "  beqz t2, .Lbv_mtx_eoa_tl7708_skip\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_mtx_eoa_tl_notself\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_eoa_tl_selfcmp\n" ++
  ".Lbv_mtx_eoa_tl_notself:\n" ++
  "  addi sp, sp, -16\n  sd x20, 0(sp)\n" ++
  "  la t0, eip7708_tl_from32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_mtx_sender_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbv_mtx_eoa_tl_from:\n  beqz t3, .Lbv_mtx_eoa_tl_from_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_eoa_tl_from\n" ++
  ".Lbv_mtx_eoa_tl_from_d:\n" ++
  "  la t0, eip7708_tl_to32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_mtx_ctx; addi t1, t1, 91; mv t2, t0; li t3, 20\n" ++
  ".Lbv_mtx_eoa_tl_to:\n  beqz t3, .Lbv_mtx_eoa_tl_to_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_eoa_tl_to\n" ++
  ".Lbv_mtx_eoa_tl_to_d:\n" ++
  "  la t0, eip7708_tl_val32\n  la t1, bv_mtx_ctx; addi t1, t1, 127; mv t2, t0; li t3, 32\n" ++
  ".Lbv_mtx_eoa_tl_val:\n  beqz t3, .Lbv_mtx_eoa_tl_val_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_eoa_tl_val\n" ++
  ".Lbv_mtx_eoa_tl_val_d:\n" ++
  "  la x20, evm_env\n  la a0, eip7708_tl_from32\n  la a1, eip7708_tl_to32\n  la a2, eip7708_tl_val32\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  ld x20, 0(sp)\n  addi sp, sp, 16\n" ++
  "  bnez a0, .Lbv_mtx_eoa_tl7708_skip\n" ++
  "  li t1, 1; la t0, eip7708_tl_typed_avail; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_eoa_tl7708_skip:\n" ++
  "  jal ra, block_log_window_snapshot\n" ++
  topLevelValueRecipientStateGasAsm "bv_mtx_eoa" "bv_mtx_ctx" ++
  -- execution-specs charges this top-level NEW_ACCOUNT state gas against the
  -- transaction's CURRENT state. If an earlier tx in this block already created
  -- the same recipient, the header-state predicate still says absent, so suppress
  -- the repeat using the shortcut's created-recipient table.
  "  beqz t0, .Lbv_mtx_eoa_state_done\n" ++
  "  la t1, bv_mtx_created_recipient_count; ld t2, 0(t1); li t3, 0\n" ++
  ".Lbv_mtx_eoa_created_scan:\n" ++
  "  beq t3, t2, .Lbv_mtx_eoa_created_not_found\n" ++
  "  slli t4, t3, 5; la t5, bv_mtx_created_recipient_table; add t5, t5, t4\n" ++
  "  la t6, bv_mtx_ctx; addi t6, t6, 72; li a0, 20\n" ++
  ".Lbv_mtx_eoa_created_cmp:\n" ++
  "  beqz a0, .Lbv_mtx_eoa_created_found\n" ++
  "  lbu a1, 0(t5); lbu a2, 0(t6); bne a1, a2, .Lbv_mtx_eoa_created_next\n" ++
  "  addi t5, t5, 1; addi t6, t6, 1; addi a0, a0, -1; j .Lbv_mtx_eoa_created_cmp\n" ++
  ".Lbv_mtx_eoa_created_next:\n" ++
  "  addi t3, t3, 1; j .Lbv_mtx_eoa_created_scan\n" ++
  ".Lbv_mtx_eoa_created_found:\n" ++
  "  li t0, 0; j .Lbv_mtx_eoa_state_done\n" ++
  ".Lbv_mtx_eoa_created_not_found:\n" ++
  "  li t4, " ++ toString bvMtxFullTxCap ++ "; bgeu t2, t4, .Lbv_mtx_eoa_state_charge_ready\n" ++
  "  slli t4, t2, 5; la t5, bv_mtx_created_recipient_table; add t5, t5, t4\n" ++
  "  sd zero, 0(t5); sd zero, 8(t5); sd zero, 16(t5); sd zero, 24(t5)\n" ++
  "  la t6, bv_mtx_ctx; addi t6, t6, 72; li a0, 20\n" ++
  ".Lbv_mtx_eoa_created_copy:\n" ++
  "  beqz a0, .Lbv_mtx_eoa_created_stored\n" ++
  "  lbu a1, 0(t6); sb a1, 0(t5); addi t6, t6, 1; addi t5, t5, 1; addi a0, a0, -1; j .Lbv_mtx_eoa_created_copy\n" ++
  ".Lbv_mtx_eoa_created_stored:\n" ++
  "  addi t2, t2, 1; la t1, bv_mtx_created_recipient_count; sd t2, 0(t1)\n" ++
  ".Lbv_mtx_eoa_state_charge_ready:\n" ++
  "  la t1, evm_state_gas_left; ld t2, 0(t1)\n" ++
  "  bgeu t2, t0, .Lbv_mtx_eoa_state_res\n" ++
  "  sub t3, t0, t2; sd x0, 0(t1)\n" ++
  "  la t4, evm_env; ld t2, 568(t4); bltu t2, t3, .Lbv_mtx_bail\n" ++
  "  sub t2, t2, t3; sd t2, 568(t4); j .Lbv_mtx_eoa_state_used\n" ++
  ".Lbv_mtx_eoa_state_res:\n" ++
  "  sub t2, t2, t0; sd t2, 0(t1)\n" ++
  ".Lbv_mtx_eoa_state_used:\n" ++
  "  la t1, evm_state_gas_used; ld t2, 0(t1); add t2, t2, t0; sd t2, 0(t1)\n" ++
  ".Lbv_mtx_eoa_state_done:\n" ++
  "  jal ra, dispatcher_tx_gas_settle\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t0, t1, 3\n" ++
  "  la t3, bv_mtx_gas_left; add t3, t3, t0; sd a0, 0(t3)\n" ++
  "  la t3, bv_mtx_refund;   add t3, t3, t0; sd a1, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t0; sd a2, 0(t3)\n" ++
  "  la t3, bv_tx_is_creation_arr; add t3, t3, t0; la t4, bv_mtx_ctx; ld t5, 48(t4); sd t5, 0(t3)\n" ++
  "  la t4, runtime_tx_calldata_floor; ld t5, 0(t4)\n" ++
  "  la t3, bv_mtx_calldata; add t3, t3, t0; sd t5, 0(t3)\n" ++
  "  mv a0, t1; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t4, bv_receipts_completeness_shape; ld t4, 0(t4); li t5, 60; bgeu t4, t5, .Lbv_mtx_eoa_receipts_ready\n" ++
  bvReceiptsShapeSet 4 true ++
  ".Lbv_mtx_eoa_receipts_ready:\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0)\n" ++
  "  slli t4, t1, 4\n" ++
  "  la t3, bv_tx_log_window; add t3, t3, t4\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_mtx_loop\n"

end EvmAsm.Codegen
