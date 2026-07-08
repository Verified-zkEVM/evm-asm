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
  "  la t0, bv_simple_transfer_tx; ld a0, 24(t0); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la t0, sttc_nonce; ld a1, 0(t0); la a0, bmvmx_sender_addr; la a2, bv_create_addr; jal ra, address_compute_create\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_create_addr; ld a3, 80(s0); ld a4, 88(s0)\n" ++
  "  jal ra, has_code_or_nonce_at_header_state_root\n" ++
  "  bnez a0, .Lbv_creation_runtime_try\n" ++
  "  la t0, hcon_predicate; ld t0, 0(t0); beqz t0, .Lbv_creation_runtime_try\n" ++
  "  # Top-level CREATE collision: execution-specs returns an error output before\n" ++
  "  # process_create_message with gas_left=0, state_gas_left=state_gas_reservoir,\n" ++
  "  # regular_gas_used=message.gas, and zero state_gas_used/state_refund.\n" ++
  "  # The guest gas-result arena has one gas_left scalar, so encode the unspent\n" ++
  "  # state reservoir there; tx_gas_result_increments then sees only regular gas\n" ++
  "  # as consumed, and eip8037_tx_state_gas nets intrinsic state gas back to zero.\n" ++
  liAmsterdamNewAccountStateGas "t5" ++
  "  la t4, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bv_runtime_refund_counter; sd zero, 0(t4)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd zero, 0(t4)\n" ++
  "  la t4, bv_tx_status_arr; sd zero, 0(t4)\n" ++
  "  li t5, 1; la t4, bv_tx_is_creation_arr; sd t5, 0(t4)   # intrinsic state reservoir is unspent\n" ++
  "  li a0, 0; jal ra, dispatcher_capture_exec_state_gas\n" ++
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
  "  la a0, bv_simple_transfer_tx; la t0, bv_exec_p; ld a1, 0(t0); jal ra, block_verdict_single_tx_creation_runtime\n" ++
  "  beqz a0, .Lbv_after_tx_gas_precharge\n.Lbv_creation_unsupported:\n"


end EvmAsm.Codegen
