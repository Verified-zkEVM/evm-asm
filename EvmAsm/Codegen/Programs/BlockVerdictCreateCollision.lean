/-
  EvmAsm.Codegen.Programs.BlockVerdictCreateCollision

  Top-level CREATE collision handling for block_verdict.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate
import EvmAsm.Codegen.Programs.AmsterdamSystemTx

namespace EvmAsm.Codegen

/-- Single-transaction top-level CREATE collision branch.

    Execution-specs Amsterdam returns a transaction error output for a top-level
    contract-creation address collision: regular gas is fully consumed, the
    state-gas reservoir is left unspent, state_gas_used/state_refund remain
    zero, and no initcode executes. The branch derives CREATE(sender, tx.nonce),
    checks the pre-state EIP-684 code-or-nonce predicate, and materializes the
    corresponding gas-result windows before falling through to the shared gas
    gates. -/
def blockVerdictCreateCollisionBranch : String :=
  ".Lbv_creation_dispatch:\n" ++
  "  la t0, bvgr_tx_state_refund; sd zero, 0(t0)\n" ++
  "  la t0, bv_simple_transfer_tx; ld a0, 24(t0); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, sttc_nonce; ld a1, 0(t0); la a0, bmvmx_sender_addr; la a2, bv_create_addr; jal ra, address_compute_create\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_create_addr; ld a3, 80(s0); ld a4, 88(s0)\n" ++
  "  jal ra, has_code_or_nonce_at_header_state_root\n" ++
  "  bnez a0, .Lbv_creation_runtime_try\n" ++
  "  la t0, hcon_predicate; ld t0, 0(t0); beqz t0, .Lbv_creation_runtime_try\n" ++
  "  # Top-level CREATE collision: execution-specs returns an error output with\n" ++
  "  # gas_left=0 and state_gas_left=state_gas_reservoir. v0.6.0 has no\n" ++
  "  # NEW_ACCOUNT refund (a colliding target is non-empty, so prepare_dispatch\n" ++
  "  # never charges it). The guest gas-result arena has one gas_left scalar, so\n" ++
  "  # it carries just the reservoir: max(0, tx.gas - TX_MAX_GAS_LIMIT).\n" ++
  "  la t4, bv_simple_transfer_tx; ld t5, 40(t4)\n" ++
  "  li t4, 16777216\n" ++
  "  bgeu t5, t4, .Lbv_creation_collision_high_gas\n" ++
  "  li t5, 0\n" ++
  "  j .Lbv_creation_collision_gas_left_ready\n" ++
  ".Lbv_creation_collision_high_gas:\n" ++
  "  sub t5, t5, t4\n" ++
  ".Lbv_creation_collision_gas_left_ready:\n" ++
  "  la t4, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bv_runtime_refund_counter; sd zero, 0(t4)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd zero, 0(t4)\n" ++
  "  la t4, bv_tx_status_arr; sd zero, 0(t4)\n" ++
  "  li t5, 1; la t4, bv_tx_is_creation_arr; sd t5, 0(t4)   # intrinsic state reservoir is unspent\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  li a0, 0; li a1, 0; jal ra, block_verdict_tx_state_gas_inline_finalize\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_runtime_refund_counter; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_runtime_calldata_floor; sd t5, 0(t4)\n" ++
  "  li t5, 1; la t4, bvgr_runtime_count; sd t5, 0(t4)\n" ++
  -- rmqwf (class D): enforce the receipts-root/bloom consensus check for top-level
  -- CREATE collisions. The synthetic runtime gas_left above leaves receipt gas
  -- as the regular component, matching execution-specs collision output. The
  -- successful-creation shape-6 branch (BlockVerdictCreationStage) stays
  -- enforce=false until it has fixture
  -- coverage (top-level creations currently bail to the class-B dispatch shapes 60/61).
  bvReceiptsShapeSet 6 true ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_creation_runtime_try:\n" ++
  "  la t0, hcon_acct_struct; ld t1, 8(t0); ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2; ld t2, 32(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbv_creation_no_alive_refund\n" ++
  liAmsterdamNewAccountStateGas "t1" ++
  "  la t0, bvgr_tx_state_refund; sd t1, 0(t0)\n" ++
  ".Lbv_creation_no_alive_refund:\n" ++
  -- v0.6.0 prepare_dispatch: stage the top-frame NEW_ACCOUNT state charge for
  -- the dispatcher iff the target is EMPTY (alive target -> refund cell != 0
  -- above -> no charge). The dispatcher enforces reservoir-first affordability
  -- and halts before dispatch (all regular gas burned) on shortage.
  "  la t0, runtime_tx_create_state_charge; sd zero, 0(t0)\n" ++
  "  la t1, bvgr_tx_state_refund; ld t1, 0(t1); bnez t1, .Lbv_creation_charge_staged\n" ++
  liAmsterdamNewAccountStateGas "t1" ++
  "  la t0, runtime_tx_create_state_charge; sd t1, 0(t0)\n" ++
  ".Lbv_creation_charge_staged:\n" ++
  -- Validated-dispatch staging for the creation tx: the dispatcher's tx-gas
  -- path (validate_tx_gas = 1) consumes the access-list cardinalities/span
  -- and the auth/top-frame cells, so stage them exactly like the contract
  -- dispatch path. A creation tx cannot be type 4 (EIP-7702 requires a
  -- non-empty `to`), so the auth cells stay zero.
  "  la t0, runtime_tx_access_list_address_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_storage_key_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_ptr; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_len; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_seed_fn; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_list_ptr; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_list_len; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_warm_fn; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_state_refund; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_regular_refund; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_top_frame_regular_gas; sd zero, 0(t0)\n" ++
  "  la t0, bv_simple_transfer_tx; ld t0, 160(t0); beqz t0, .Lbv_creation_access_done\n" ++
  "  li a2, 7; li t1, 1; beq t0, t1, .Lbv_creation_access_field\n" ++
  "  li a2, 8; li t1, 2; beq t0, t1, .Lbv_creation_access_field\n" ++
  "  li t1, 3; beq t0, t1, .Lbv_creation_access_field\n" ++
  "  j .Lbv_creation_unsupported\n" ++
  ".Lbv_creation_access_field:\n" ++
  "  la t0, bv_simple_transfer_tx; ld a0, 176(t0); ld a1, 184(t0); la a3, bsg_access_off; la a4, bsg_access_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbv_creation_unsupported\n" ++
  "  la t0, bv_simple_transfer_tx; ld t0, 176(t0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, bsg_access_len; ld a1, 0(t1)\n" ++
  "  la a2, runtime_tx_access_list_address_count; la a3, runtime_tx_access_list_storage_key_count\n" ++
  "  jal ra, access_list_count\n" ++
  "  bnez a0, .Lbv_creation_unsupported\n" ++
  "  la t0, bv_simple_transfer_tx; ld t0, 176(t0); la t1, bsg_access_off; ld t1, 0(t1); add t2, t0, t1\n" ++
  "  la t0, runtime_tx_access_list_ptr; sd t2, 0(t0)\n" ++
  "  la t1, bsg_access_len; ld t2, 0(t1); la t0, runtime_tx_access_list_len; sd t2, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_seed_fn; la t1, seed_tx_access_list; sd t1, 0(t0)\n" ++
  ".Lbv_creation_access_done:\n" ++
  "  la a0, bv_simple_transfer_tx; la t0, bv_exec_p; ld a1, 0(t0); jal ra, block_verdict_single_tx_creation_runtime\n" ++
  "  beqz a0, .Lbv_after_tx_gas_precharge\n.Lbv_creation_unsupported:\n"


end EvmAsm.Codegen
