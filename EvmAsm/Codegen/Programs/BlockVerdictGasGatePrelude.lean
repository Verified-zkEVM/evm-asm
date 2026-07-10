/-
  EvmAsm.Codegen.Programs.BlockVerdictGasGatePrelude

  Gas-gate prelude fragment for `block_verdict`, split from
  BlockVerdictFunction.lean for FileSizeGuard.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate

namespace EvmAsm.Codegen

/-- Runtime gas-result preparation and EIP-8037/EIP-7778 gate prelude. -/
def blockVerdictGasGatePrelude : String :=
  ".Lbv_after_tx_gas_precharge:\n" ++
  -- fhsxz.2.4.2.57.11.6.5.2.1.3: prefill the transaction-count and
  -- intrinsic-state-gas substrate BEFORE eip8037_tx_gas_gate. The gate still
  -- runs unconditionally: a substrate parse/fill failure zeros the prefix and
  -- falls through, preserving the old conservative gate behavior while making
  -- the exact per-tx state dimension available to the follow-up gate patch.
  "  la t2, bvgr_arena_tx_count; sd zero, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  li a2, " ++ toString bvMtxFullTxCap ++ "\n" ++
  "  jal ra, block_verdict_tx_gas_limits\n" ++
  "  bnez a0, .Lbv_pregate_state_gas_ready\n" ++
  "  la t2, bvgr_arena_tx_count; sd a1, 0(t2)\n" ++
  -- `tx_eip7702_existing_authority_refund` distinguishes a marker already
  -- present in pre-state from one written by the current authorization.  This
  -- early gas phase runs before state-root validation normally initializes
  -- `svf_tx_count`; publish the independently parsed transaction count here
  -- so a one-tx block cannot mistake its own final marker for prior state.
  "  la t2, svf_tx_count; sd a1, 0(t2)\n" ++
  -- The EIP-7702 refund classifier must compare a recovered authority with
  -- the transaction sender to account for `process_transaction`'s prior nonce
  -- increment.  The contract path initializes `bv_stx_sender_addr` itself,
  -- but the EOA path reaches this common gas phase without doing so.  For the
  -- single-transaction context represented by `bv_simple_transfer_tx`, derive
  -- it from the already validated public key before classifying refunds.
  "  li t3, 1; bne a1, t3, .Lbv_pregate_sender_ready\n" ++
  "  la t2, bv_simple_transfer_tx; ld t3, 0(t2); bnez t3, .Lbv_pregate_sender_ready\n" ++
  "  ld a0, 24(t2); la a1, bv_stx_sender_addr; jal ra, address_from_pubkey\n" ++
  ".Lbv_pregate_sender_ready:\n" ++
  "  la t2, bv_tx_list_ptr; ld a0, 0(t2)\n  la t2, bv_tx_list_len; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  la a3, bvgr_tx_state_gas\n" ++
  "  la t2, teer_records_ptr; la t3, basr_records; sd t3, 0(t2)\n" ++
  "  la t2, bv_bal_start; ld a4, 0(t2)\n  la t2, bv_bal_len; ld a5, 0(t2)\n  la t2, bv_chain_id; ld a6, 0(t2)\n" ++
  "  jal ra, block_verdict_tx_state_gas_array\n" ++
  "  beqz a0, .Lbv_pregate_state_gas_ready\n" ++
  "  la t2, bvgr_tx_state_gas; la t3, bvgr_arena_tx_count; ld t3, 0(t3); li t4, 0\n" ++
  ".Lbv_pregate_state_gas_zero:\n" ++
  "  beq t4, t3, .Lbv_pregate_state_gas_ready\n" ++
  "  slli t5, t4, 3; add t5, t2, t5; sd zero, 0(t5); addi t4, t4, 1; j .Lbv_pregate_state_gas_zero\n" ++
  ".Lbv_pregate_state_gas_ready:\n" ++
  "  # EIP-8037 tx inclusion gas gate: reject parse-supported legacy tx blocks\n" ++
  "  # whose worst regular/state gas exceeds the remaining 2D block budget.\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)             # exec_payload\n" ++
  "  la t2, bv_bal_start; ld a1, 0(t2)          # bal_start\n" ++
  "  la t2, bv_bal_len; ld a2, 0(t2)            # bal_len\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  mv a3, a0                                  # gas_limit\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  jal ra, eip8037_tx_gas_gate\n" ++
  "  bnez a0, .Lbv_eip8037_gas_fail\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la t2, bvgr_runtime_gas_left_ptr; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_runtime_refund_counter_ptr; ld a2, 0(t2)\n" ++
  "  la t2, bvgr_runtime_calldata_floor_ptr; ld a3, 0(t2)\n" ++
  "  la t2, bvgr_runtime_count; ld a4, 0(t2)\n" ++
  "  li a5, " ++ toString bvMtxFullTxCap ++ "\n" ++
  "  jal ra, block_verdict_gas_result_arena_prepare\n" ++
  bvRuntimeCompletenessSetFromArenaStatus ++
  ""

end EvmAsm.Codegen
