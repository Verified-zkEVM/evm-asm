/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxEoa

  MTx top-level precompile execution adapter.

  Ordinary empty-code recipients no longer have a settlement route here:
  `dispatch_tx_runtime_code` stages zero-byte code and owns the common
  `process_message` setup and settlement.  A deferred status-2 code witness
  also uses that setup through `runtime_dispatcher_prepare_only`; the MTx
  wrapper alone decodes its tri-state continuation.
-/

import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas
import EvmAsm.Codegen.Programs.PrecompileRuntime

namespace EvmAsm.Codegen

/-- Enter the active-precompile execution adapter from the top-level message
    route.  It remains a distinct settlement path; ordinary zero-byte
    recipients do not enter this adapter. -/
def blockVerdictMtxPrecompileSettlement : String :=
  ".Lbv_mtx_precompile_entry:\n" ++
  ".Lbv_mtx_precompile_kernel:\n" ++
  -- The adapter receives the complete context in `bv_mtx_ctx`; the shared
  -- selector and publication helpers consume that same context directly.
  -- Keep the context and sender copies out of this adapter: the former is
  -- already the live MTx record, while `simple_transfer_intrinsic_gas`
  -- refreshes the sender scalar from its +24 field before any consumer.
  "  la t0, bv_mtx_ctx; addi t0, t0, 72\n" ++
  precompileAddressClassifyAsm "bv_mtx_adapter" "t0" "t3" "t1" "t4" ++
  "  beqz t3, .Lbv_mtx_precompile_adapter_fallback\n" ++
  -- Mode 2 means that the precompile selector is entered by the shared
  -- transaction dispatcher.  Lane 1 has no writer: the old direct sentinel
  -- is retired, while the shared publish joins below remain reachable for
  -- lane 2 finalization.
  "  la t0, bv_mtx_precompile_lane; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t0, runtime_tx_prepare_prefix_status; li t1, 3; sd t1, 0(t0)\n" ++
  "  la t0, runtime_tx_post_top_frame_fn; la t1, .Lbv_mtx_precompile_dispatch_hook; sd t1, 0(t0)\n" ++
  "  j .Lbv_mtx_is_contract\n" ++
  ".Lbv_mtx_precompile_adapter_fallback:\n" ++
  "  la t0, bv_mtx_precompile_lane; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_prepare_prefix_status; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_post_top_frame_fn; sd zero, 0(t0)\n" ++
  "  j .Lbv_mtx_is_contract\n" ++
  ".Lbv_mtx_precompile_dispatch_hook:\n" ++
  "  la t2, bv_mtx_ctx; j .Lbv_tx_gas_precharge_pc0_prefix\n"

end EvmAsm.Codegen
