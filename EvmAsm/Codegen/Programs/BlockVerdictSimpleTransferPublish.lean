/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPublish

  Simple-transfer runtime publication assembly, split from BlockVerdictFunction.
-/

import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

namespace EvmAsm.Codegen

def blockVerdictSimpleTransferPublishAsmFor (_ctxLabel : String) : String :=
  ".Lbv_simple_transfer_precompile_fail:\n" ++
  -- Mode 2 has already paid the transaction-level intrinsic/upfront gas in
  -- the shared dispatcher.  Jump straight to its exceptional-halt join and
  -- avoid the legacy direct-publication wrapper.
  "  la t0, bv_mtx_precompile_lane; ld t0, 0(t0); li t1, 2; beq t0, t1, .Ldtrc_mtx_precompile_failure\n" ++
  -- `bv_mtx_precompile_lane` has exactly one non-zero writer: `BlockVerdictMtxEoa.lean:26` stores 2 on the instruction before the jump into this region, so lane==0 cannot reach this fail label; the fall-through into the emit stub is the lane-not-2 path.
  ".Lbv_simple_transfer_emit_tl_then_after_tx_gas_precharge:\n" ++
  -- The shared dispatcher owns intrinsic gas, state-gas rollback, and the
  -- final MTx publication for mode 2; only the selector's cost in t6 is new.
  "  la t0, bv_mtx_precompile_lane; ld t0, 0(t0); li t1, 2; beq t0, t1, .Ldtrc_mtx_precompile_success\n"

def blockVerdictSimpleTransferPublishAsm : String :=
  blockVerdictSimpleTransferPublishAsmFor "bv_simple_transfer_tx"

end EvmAsm.Codegen
