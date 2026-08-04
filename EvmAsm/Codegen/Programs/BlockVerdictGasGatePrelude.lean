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
  -- Publish the independently parsed transaction count for the later runtime
  -- and receipt gates.  Intrinsic/auth state gas is already materialized at
  -- each live transaction boundary; do not replay it here from block-final
  -- data.
  "  la t2, svf_tx_count; sd a1, 0(t2)\n" ++
  ".Lbv_pregate_state_gas_ready:\n" ++
  "  # EIP-8037 tx inclusion gas gate: reject parse-supported legacy tx blocks\n" ++
  "  # whose worst regular/state gas exceeds the remaining 2D block budget.\n" ++
  "  # #11428: supplied-BAL a1/a2 transport retired (consumer deleted in #11424).\n" ++
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
