/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

  Simple-transfer gas publication helper for block_verdict.
-/

import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.CreateCodeEffectLog

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
  -- `process_message` evaluates account liveness against the transaction's
  -- current state.  A preceding value transfer can have made this recipient
  -- live even when the immutable header has no account for it.  Consult the
  -- current account-write tiers first.  Status 1/2 means a present account;
  -- Present-None status 3 deliberately falls through to the authenticated
  -- header predicate below.
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72\n" ++
  "  jal ra, account_writes_lookup_current\n" ++
  "  li t2, 1; beq a0, t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  "  li t2, 2; beq a0, t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  -- GH #11713: lookup_current requires STATE bit (8) and skips component-only
  -- BALANCE/NONCE/TOUCH/CODE rows so they cannot mask lower-tier code.  A prior
  -- top-level value transfer writes BALANCE|TOUCHED only (vm=0x21).  Spec
  -- charges NEW_ACCOUNT only when value>0 and not is_account_alive
  -- (interpreter.py:285-288 at e5a8caf1b).  is_account_alive = exists ∧
  -- ≠ EMPTY_ACCOUNT (state_tracker.py:445-463); EMPTY_ACCOUNT is zero balance
  -- AND zero nonce AND empty code.  So any of {nonzero bal, nonzero nonce,
  -- nonempty code} on the tx-then-block-cumulative map ⇒ alive.  Map helpers
  -- used: latest_balance, latest_nonce_tx, latest_nonce_block.  Code without
  -- STATE is covered below by a dual-tier HAS_CODE/codeLen probe (same maps,
  -- NOT created-set — mark_account_created is sticky on revert).
  "  addi sp, sp, -32\n" ++
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72; mv a1, sp\n" ++
  "  jal ra, account_writes_latest_balance\n" ++
  "  beqz a0, .L" ++ tag ++ "_recipient_nonce\n" ++
  "  ld t2, 0(sp); ld t3, 8(sp); or t2, t2, t3\n" ++
  "  ld t3, 16(sp); or t2, t2, t3\n" ++
  "  ld t3, 24(sp); or t2, t2, t3\n" ++
  "  bnez t2, .L" ++ tag ++ "_recipient_map_alive\n" ++
  ".L" ++ tag ++ "_recipient_nonce:\n" ++
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72; mv a1, sp\n" ++
  "  jal ra, account_writes_latest_nonce_tx\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_nonce_got\n" ++
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72; mv a1, sp\n" ++
  "  jal ra, account_writes_latest_nonce_block\n" ++
  "  beqz a0, .L" ++ tag ++ "_recipient_code\n" ++
  ".L" ++ tag ++ "_recipient_nonce_got:\n" ++
  "  ld t2, 0(sp); bnez t2, .L" ++ tag ++ "_recipient_map_alive\n" ++
  ".L" ++ tag ++ "_recipient_code:\n" ++
  -- Dual-tier HAS_CODE (mask value 4) with codeLen@+88: tx map then block map.
  -- Re-load addr: nonce helpers clobber t0-t6.
  "  la t1, " ++ ctxLabel ++ "; addi t0, t1, 72\n" ++
  "  la t1, tx_account_writes_count; ld t2, 0(t1); li t3, 0xa2b20000; li t4, 0\n" ++
  ".L" ++ tag ++ "_recipient_code_tx:\n" ++
  "  bgeu t4, t2, .L" ++ tag ++ "_recipient_code_blk_init\n" ++
  "  slli t5, t4, 7; add t5, t3, t5; mv a0, t5; mv a1, t0; li a2, 20\n" ++
  ".L" ++ tag ++ "_recipient_code_tx_cmp:\n" ++
  "  beqz a2, .L" ++ tag ++ "_recipient_code_tx_key\n" ++
  "  lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4, .L" ++ tag ++ "_recipient_code_tx_next\n" ++
  "  addi a0, a0, 1; addi a1, a1, 1; addi a2, a2, -1; j .L" ++ tag ++ "_recipient_code_tx_cmp\n" ++
  ".L" ++ tag ++ "_recipient_code_tx_next:\n" ++
  "  addi t4, t4, 1; j .L" ++ tag ++ "_recipient_code_tx\n" ++
  ".L" ++ tag ++ "_recipient_code_tx_key:\n" ++
  "  ld t6, 112(t5); andi t6, t6, 4; beqz t6, .L" ++ tag ++ "_recipient_code_tx_next\n" ++
  "  ld t6, 88(t5); bnez t6, .L" ++ tag ++ "_recipient_map_alive\n" ++
  "  j .L" ++ tag ++ "_recipient_code_tx_next\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_init:\n" ++
  "  la t1, account_writes_count; ld t2, 0(t1); li t3, 0xa28a0000; li t4, 0\n" ++
  ".L" ++ tag ++ "_recipient_code_blk:\n" ++
  "  bgeu t4, t2, .L" ++ tag ++ "_recipient_map_miss\n" ++
  "  slli t5, t4, 7; add t5, t3, t5; mv a0, t5; mv a1, t0; li a2, 20\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_cmp:\n" ++
  "  beqz a2, .L" ++ tag ++ "_recipient_code_blk_key\n" ++
  "  lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4, .L" ++ tag ++ "_recipient_code_blk_next\n" ++
  "  addi a0, a0, 1; addi a1, a1, 1; addi a2, a2, -1; j .L" ++ tag ++ "_recipient_code_blk_cmp\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_next:\n" ++
  "  addi t4, t4, 1; j .L" ++ tag ++ "_recipient_code_blk\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_key:\n" ++
  "  ld t6, 112(t5); andi t6, t6, 4; beqz t6, .L" ++ tag ++ "_recipient_code_blk_next\n" ++
  "  ld t6, 88(t5); bnez t6, .L" ++ tag ++ "_recipient_map_alive\n" ++
  "  j .L" ++ tag ++ "_recipient_code_blk_next\n" ++
  ".L" ++ tag ++ "_recipient_map_alive:\n" ++
  "  addi sp, sp, 32\n" ++
  "  j .L" ++ tag ++ "_recipient_state_zero\n" ++
  ".L" ++ tag ++ "_recipient_map_miss:\n" ++
  "  addi sp, sp, 32\n" ++
  ".L" ++ tag ++ "_recipient_state_header:\n" ++
  "  la t1, " ++ ctxLabel ++ "\n" ++
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
  -- GH #11398: no supplied-BAL consult.  execution-specs evaluates recipient
  -- liveness from tracked state alone (state_tracker.py); when the overlays
  -- and the authenticated header both miss, the account is dead at this point
  -- and the NEW_ACCOUNT state-gas charge applies.  The declared BAL arm that
  -- used to skip the charge here papered over tracked-state gaps for shapes
  -- the guest runtime does not replay; the provided BAL is hashed, never read
  -- for execution (fork.py:366/:390).
  ".L" ++ tag ++ "_recipient_state_apply_charge:\n" ++
  liAmsterdamNewAccountStateGas "t0" ++
  "  j .L" ++ tag ++ "_recipient_state_done\n" ++
  ".L" ++ tag ++ "_recipient_state_zero:\n" ++
  "  li t0, 0\n" ++
  ".L" ++ tag ++ "_recipient_state_done:\n"

/-! The simple-transfer/precompile publication arm does not pass through the
    callable dispatcher's post-authorization seam.  Capture the state-gas pool
    at its equivalent point, immediately after intrinsic gas has succeeded and
    before the top-level recipient charge is evaluated.  Keep both pool fields
    as baselines: a direct route may enter with a nonzero spill after a shared
    preparation prefix. -/
def directTransferStateGasBaselineAsm (tag : String) : String :=
  "  la t1, evm_state_gas_left; ld t2, 0(t1)\n" ++
  "  la t1, evm_state_gas_spilled; ld t3, 0(t1)\n" ++
  "  la t4, runtime_tx_state_gas_entry_left; sd t2, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_entry_spilled; sd t3, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_message_left; sd t2, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_message_spilled; sd t3, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_entry_valid; li t5, 1; sd t5, 0(t4)\n" ++
  ".L" ++ tag ++ "_state_gas_baseline_done:\n"

/-! Charge the direct top-level recipient state amount held in `t0`.  This is
    deliberately the same reservoir-first/spill-second accounting used by the
    runtime SSTORE path.  The surrounding publish code still performs the
    complete transaction-gas check, so this helper only materializes the pool
    transition and the authoritative executed-state accumulator. -/
def directTransferStateGasChargeAsm (tag : String) : String :=
  "  la t1, evm_state_gas_left; ld t2, 0(t1)\n" ++
  "  bltu t2, t0, .L" ++ tag ++ "_state_gas_spill\n" ++
  "  sub t2, t2, t0; sd t2, 0(t1)\n" ++
  "  j .L" ++ tag ++ "_state_gas_used\n" ++
  ".L" ++ tag ++ "_state_gas_spill:\n" ++
  "  sub t3, t0, t2; sd zero, 0(t1)\n" ++
  "  la t1, evm_state_gas_spilled; ld t4, 0(t1); add t4, t4, t3; sd t4, 0(t1)\n" ++
  ".L" ++ tag ++ "_state_gas_used:\n" ++
  "  la t1, evm_state_gas_used; ld t2, 0(t1); add t2, t2, t0; sd t2, 0(t1)\n"

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
  -- The common transaction boundary is the sole state-gas writer.  This
  -- shortcut only consumes its already-materialized state cell and adds the
  -- live auth regular component to ordinary intrinsic regular gas.
  "  la t0, bvgr_tx_state_gas; ld t1, 0(t0)\n" ++
  "  ld s1, 48(sp); ld s2, 56(sp)\n" ++
  "  la t2, runtime_tx_auth_regular_refund; ld t2, 0(t2); add s1, s1, t2\n" ++
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
