/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPrecompileGas

  Depth-0 thin wrapper around `precompile_shared_execute` (#11163 item 2).
  Fills the shared descriptor from the MTx context, runs select_price, charges
  nothing here (settlement charges t6 on the lane-2 success exit), executes the
  shared core, and routes a0 status to lane-2 success/fail exits.
-/

import EvmAsm.Codegen.Programs.PrecompileRuntime

namespace EvmAsm.Codegen

def blockVerdictSimpleTransferPrecompileGasAsmFor (ctxLabel : String) : String :=
  "  # Depth-0 precompile thin wrapper: descriptor → select_price → execute.\n" ++
  "  # Spec: pin e5a8caf1b interpreter.py process_message after move_ether.\n" ++
  ".Lbv_tx_gas_precharge_pc0_prefix:\n" ++
  "  la t0, precompile_shared_ctx; la t1, " ++ ctxLabel ++ "; addi t1, t1, 72; sd t1, 0(t0)\n" ++
  "  la t1, " ++ ctxLabel ++ "; ld t1, 56(t1); sd t1, 8(t0)\n" ++
  "  la t1, " ++ ctxLabel ++ "; ld t1, 64(t1); sd t1, 16(t0)\n" ++
  "  jal ra, precompile_shared_select_price\n" ++
  "  la t0, precompile_shared_selector; ld t3, 0(t0); la t2, " ++ ctxLabel ++ "\n" ++
  precompileSharedStatusFailAsm ".Lbv_simple_transfer_precompile_fail" ++
  "  beqz t3, .Lbv_mtx_precompile_not_active\n" ++
  "  jal ra, precompile_shared_execute\n" ++
  "  bnez a0, .Lbv_simple_transfer_precompile_fail\n" ++
  precompileSharedLoadCostAsm "t6" ++
  "  j .Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge\n"

def blockVerdictSimpleTransferPrecompileGasAsm : String :=
  blockVerdictSimpleTransferPrecompileGasAsmFor "bv_simple_transfer_tx"

end EvmAsm.Codegen
