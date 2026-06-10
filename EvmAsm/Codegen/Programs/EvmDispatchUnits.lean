/-
  EvmAsm.Codegen.Programs.EvmDispatchUnits

  Dispatch BuildUnit definitions extracted from Programs/Evm.lean to
  satisfy the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.Evm
import EvmAsm.Codegen.Programs.SystemCallStaging

namespace EvmAsm.Codegen

def tinyInterpDispatchAddUnit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAddBytecode

def tinyInterpDispatchAdd2Unit : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tinyInterpAdd2Bytecode

/-! ## runtime_dispatcher — M8.5 runtime-bytecode dispatcher

    Same `tinyInterpRegistry` and `evmAddEpilogue` as the
    `tiny_interp_dispatch_*` units, but the dispatcher prologue
    reads `x10` from `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010`
    instead of an in-`.data` label. One ELF runs any bytecode; the
    bash test harness packs each per-case bytecode into a
    ziskemu `-i <file>` payload and reuses the same dispatcher
    ELF for every case.

    See `EvmAsm/Codegen/Dispatch.lean` for `buildRuntimeDispatchUnit`
    and the runtime prologue/data-section helpers. -/
def runtimeDispatcherUnit : BuildUnit :=
  buildRuntimeDispatchUnit tinyInterpRegistry evmAddEpilogue

/-! ## runtime_dispatcher_call_probe

    Probe for the callable runtime dispatcher ABI. It runs the same
    runtime-bytecode input format as `runtime_dispatcher`, but calls
    `runtime_dispatcher_call` as a subroutine and writes a return marker
    after the dispatcher returns to its caller. -/
def runtimeDispatcherCallProbeUnit : BuildUnit :=
  buildRuntimeDispatchCallableProbeUnit tinyInterpRegistry evmAddEpilogue

/-! ## runtime_dispatcher_gas_capture_probe

    Probe for the runtime dispatcher gas-result capture path. It runs one
    staged transaction through `runtime_dispatcher_call` and records the
    dispatcher's post-execution gas results (`gas_left`, `refund_counter`,
    `calldata_floor_gas_cost`, and `halt_kind`) into per-transaction arrays
    at index 0 — the arrays consumed by the block-verdict gas-result arena —
    and surfaces them to the stable `OUTPUT+160` diagnostic window. -/
def runtimeDispatcherGasCaptureProbeUnit : BuildUnit :=
  buildRuntimeDispatchGasCaptureProbeUnit tinyInterpRegistry evmAddEpilogue

/-! ## zisk_stage_system_call (8uld3.2.1c)

    End-to-end probe for `stage_system_call`: stage a SYSTEM call to a synthetic
    predeploy that RETURNs 32 known bytes (`PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 32;
    PUSH1 0; RETURN`), run it through the callable runtime dispatcher with
    system_call_mode=1, and assert the depth-0 RETURN was captured (#8681) into
    system_call_returndata. Bundles the dispatcher (tinyInterpRegistry) + the
    staging functions; mirrors `runtimeDispatcherCallProbeUnit`'s structure.
    Output (0xa0010000): +0 returndata_len (expect 32), +8 status (expect 0),
    +16 returndata[31] (expect 0x42), +24 returndata[0] (expect 0x00). -/
def ziskStageSystemCallProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    "  la a0, ssc_probe_target\n  la a1, ssc_probe_code\n  li a2, 10\n  la a3, ssc_probe_exec\n  la a4, ssc_probe_out\n" ++
    "  jal ra, stage_system_call\n" ++
    "  li t0, 0xa0010000\n" ++
    "  sd a1, 0(t0)             # returndata_len\n" ++
    "  sd a2, 8(t0)             # status\n" ++
    "  add t1, a0, 31; lbu t2, 0(t1); sd t2, 16(t0)   # returndata[31]\n" ++
    "  lbu t2, 0(a0); sd t2, 24(t0)                   # returndata[0]\n" ++
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    stageSystemCallFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    -- tinyInterpRegistry's CREATE handler descends via create_frame_descend, which pulls
    -- in the full frame-helper chain (none defined by the plain-STOP callable epilogue for
    -- this registry). Bundle them for a standalone emit (mirrors createRoundtripUnit).
    frameBaseFunction ++ "\n" ++
    frameDepthPushFunction ++ "\n" ++
    frameDepthPopFunction ++ "\n" ++
    frameSaveRegsFunction ++ "\n" ++
    frameLoadRegsFunction ++ "\n" ++
    callFrameEnterFunction ++ "\n" ++
    callFrameSetCallEnvFunction ++ "\n" ++
    callFrameSetCalldataFunction ++ "\n" ++
    callFrameForwardGasFunction ++ "\n" ++
    callFrameDescendFunction ++ "\n" ++
    createFrameDescendFunction ++ "\n" ++
    frameReturnFunction ++ "\n" ++
    recordNonstorageEffectFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    ".balign 8\n" ++
    "scc_system_addr:\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe\n" ++
    ".balign 8\n" ++
    "srpc_env_base:\n  .zero 8\n" ++
    "m29_stage_cur:\n  .zero 8\n" ++
    "m29_stage_count:\n  .zero 8\n" ++
    "m29_stage_table:\n  .zero 8192\n" ++
    ".balign 8\n" ++
    "ssc_probe_target:\n  .byte 0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5, 0x5e, 0x80, 0xd1, 0x9a, 0xd8, 0x35, 0x79, 0xa6, 0x4c, 0x00, 0x70, 0x02\n" ++
    ".balign 8\n" ++
    "ssc_probe_code:\n  .byte 0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3\n" ++   -- PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 32; PUSH1 0; RETURN
    ".balign 8\n" ++
    "ssc_probe_exec:\n  .zero 1024\n" ++
    ".balign 8\n" ++
    "ssc_probe_out:\n  .zero 4096\n" ++
    -- frame-helper data (the bundled create/call descent chain; inert for this no-CREATE
    -- predeploy, but the labels must be defined for a standalone emit — mirrors createRoundtripData).
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x29000 : Nat) ++ "\n"
}

end EvmAsm.Codegen
