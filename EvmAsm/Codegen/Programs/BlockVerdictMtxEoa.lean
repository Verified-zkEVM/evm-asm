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
  "  la t0, bv_mtx_precompile_lane; li t1, 1; sd t1, 0(t0); la t2, bv_simple_transfer_tx; j .Lbv_tx_gas_precharge_pc0_prefix\n"

end EvmAsm.Codegen
