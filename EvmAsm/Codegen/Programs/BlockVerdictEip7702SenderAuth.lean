/-
  EvmAsm.Codegen.Programs.BlockVerdictEip7702SenderAuth

  Assembly fragment for the EIP-7702 sender-as-authority nonce exception used by
  block_verdict's sender BAL post-nonce check.
-/

namespace EvmAsm.Codegen

/-- Inline block_verdict fragment for the type-4 sender-as-authority nonce case.
    Reached only after `sender_post_nonce_consistent` reports that BAL post_nonce
    is not `sender_pre + 1`. The fragment proves the single-auth self-authority
    case and then requires `sender_pre + 2`; otherwise it branches to
    `.Lbv_sender_nonce_fail`. -/
def eip7702SenderSelfAuthPostNonceCheck : String :=
  -- EIP-7702 self-authority exception: the tx sender nonce increments once for
  -- transaction execution and once more when a valid authorization tuple from the
  -- same authority installs delegation. Keep this precise: require type 4, exactly
  -- one zero-chain authorization, auth.nonce == sender_pre + 1, recovered authority
  -- == sender, and BAL post_nonce == sender_pre + 2.
  "  la t0, bv_simple_transfer_tx; ld t1, 160(t0); li t2, 4; bne t1, t2, .Lbv_sender_nonce_fail\n" ++
  "  ld a0, 176(t0); ld a1, 184(t0); li a2, 9; la a3, bsg_auth_off; la a4, bsg_auth_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t6, bv_simple_transfer_tx; ld t1, 176(t6); la t0, bsg_auth_off; ld t2, 0(t0); add t1, t1, t2; la t0, bsg_data_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsg_auth_len; ld t1, 0(t0); la t0, bsg_data_len; sd t1, 0(t0)\n" ++
  "  la t0, bsg_data_ptr; ld a0, 0(t0); la t0, bsg_data_len; ld a1, 0(t0); la a2, bsg_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bsg_auth_count; ld t0, 0(t0); li t1, 1; bne t0, t1, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bsg_data_ptr; ld a0, 0(t0); la t0, bsg_data_len; ld a1, 0(t0); li a2, 0; la a3, bsg_idx_off; la a4, bsg_idx_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bsg_data_ptr; ld t2, 0(t0); la t0, bsg_idx_off; ld t1, 0(t0); add t1, t2, t1; la t0, bsg_change_ptr; sd t1, 0(t0)\n" ++
  "  la t0, bsg_idx_len; ld t1, 0(t0); la t0, bsg_change_item_len; sd t1, 0(t0)\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); li a2, 0; la a3, bsg_index\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bsg_index; ld t0, 0(t0); bnez t0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); li a2, 2; la a3, bsg_index\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, tgbpvr_lookup; ld t1, 80(t0); addi t1, t1, 1; la t2, bsg_index; ld t2, 0(t2); bne t1, t2, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); la a2, teer_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, teer_authority; la t1, tgbpvr_lookup; addi t1, t1, 16; li t2, 20\n" ++
  ".Lbv_sender_auth_cmp:\n" ++
  "  beqz t2, .Lbv_sender_auth_match\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_sender_nonce_fail\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_sender_auth_cmp\n" ++
  ".Lbv_sender_auth_match:\n" ++
  "  la t0, tgbpvr_lookup; ld t1, 128(t0); li t2, -1; beq t1, t2, .Lbv_sender_nonce_fail\n" ++
  "  li t2, 8; bgtu t1, t2, .Lbv_sender_nonce_fail\n" ++
  "  addi t2, t0, 136; li t3, 0; mv t4, t1\n" ++
  ".Lbv_sender_post2_be:\n" ++
  "  beqz t4, .Lbv_sender_post2_de\n" ++
  "  slli t3, t3, 8; lbu t5, 0(t2); or t3, t3, t5; addi t2, t2, 1; addi t4, t4, -1; j .Lbv_sender_post2_be\n" ++
  ".Lbv_sender_post2_de:\n" ++
  "  ld t4, 80(t0); addi t4, t4, 2; bne t3, t4, .Lbv_sender_nonce_fail\n" ++
  ".Lbv_sender_nonce_checked:\n"

end EvmAsm.Codegen
