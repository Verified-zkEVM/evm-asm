/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxEoa

  Depth-0 precompile arm for the shared message processor (GH #11163).

  Ordinary empty-code recipients and active precompiles both enter
  `dispatch_tx_runtime_code` / `runtime_dispatcher_call`.  After shared
  prep (intrinsic, upfront, move_ether, TL reemit, auth warm) the arm
  below classifies the recipient and either jumps the linked top-level
  kernel tree or falls through to the bytecode loop (empty → STOP).
-/

namespace EvmAsm.Codegen

/-- Shared-body depth-0 precompile arm (execution-specs `process_message`
    after `move_ether`).  Inserted by `emitRuntimeDispatcherCallablePrologue`
    only when the guest links the top-level kernel tree
    (`.Lbv_tx_gas_precharge_pc0_prefix`).  CREATE and system-call modes skip;
    non-empty code skips (bytecode path).  Lane 2 marks the kernel exit joins
    (`.Ldtrc_mtx_precompile_{success,failure}`). -/
def depth0SharedPrecompileArmAsm : String :=
  "  # #11163: depth-0 precompile arm (shared process_message body)\n" ++
  "  la t0, create_frame_flag; ld t0, 0(t0); bnez t0, .Lruntime_dispatcher_regular_loop\n" ++
  "  la t0, system_call_mode; ld t0, 0(t0); bnez t0, .Lruntime_dispatcher_regular_loop\n" ++
  "  ld t0, 496(x20); bnez t0, .Lruntime_dispatcher_regular_loop\n" ++
  "  la t0, bv_mtx_precompile_lane; li t1, 2; sd t1, 0(t0)\n" ++
  "  la t2, bv_mtx_ctx\n" ++
  "  j .Lbv_tx_gas_precharge_pc0_prefix\n"

end EvmAsm.Codegen
