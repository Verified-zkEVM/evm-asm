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
  "  la t0, bv_mtx_ctx; la t1, bv_simple_transfer_tx; li t2, 24\n" ++
  ".Lbv_mtx_precompile_ctx_copy:\n" ++
  "  beqz t2, .Lbv_mtx_precompile_sender_init; ld t3, 0(t0); sd t3, 0(t1); addi t0, t0, 8; addi t1, t1, 8; addi t2, t2, -1; j .Lbv_mtx_precompile_ctx_copy\n" ++
  ".Lbv_mtx_precompile_sender_init:\n" ++
  "  la t0, bv_mtx_sender_addr; la t1, bmvmx_sender_addr; li t2, 20\n" ++
  ".Lbv_mtx_precompile_sender_copy:\n" ++
  "  beqz t2, .Lbv_mtx_precompile_kernel; lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_precompile_sender_copy\n" ++
  ".Lbv_mtx_precompile_kernel:\n" ++
  -- The adapter is reached from the delegation-aware MTx classifier, not
  -- exclusively from active precompile recipients.  Classify the copied
  -- recipient before arming the shared one-shot hook; ordinary recipients
  -- must take the existing contract/EOA path without installing mode 2.
  "  la t0, bv_simple_transfer_tx; addi t0, t0, 72\n" ++
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
  "  la t2, bv_simple_transfer_tx; j .Lbv_tx_gas_precharge_pc0_prefix\n"

end EvmAsm.Codegen
