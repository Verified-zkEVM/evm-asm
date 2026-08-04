/-
  EvmAsm.Codegen.Programs.EvmDispatchUnits

  Dispatch BuildUnit definitions extracted from Programs/Evm.lean to
  satisfy the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.EvmTinyInterp
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.AccountReadLog
import EvmAsm.Codegen.Programs.StorageReadLog
import EvmAsm.Codegen.Programs.CodeReadLog
import EvmAsm.Codegen.Programs.ReadSetsPromote
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.TxPubkey
import EvmAsm.Codegen.Programs.BlockVerdictCreationStage
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.DispatcherExecStateGas

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


/-! ## zisk_creation_runtime_windows

    Probe for the top-level creation runtime-window integration. It runs the
    supported one-byte STOP initcode shape through
    `block_verdict_creation_runtime`, then verifies the verdict-facing
    windows are populated. It then resets `bvgr_runtime_count` and calls the same
    helper with unsupported non-STOP initcode to pin the conservative
    `runtime_count=0` behavior.

    Output (0xa0010000):
      +0  supported helper status              (expect 0)
      +8  bvgr_runtime_count after supported   (expect 1)
      +16 bv_tx_status_arr[0]                  (expect 1)
      +24 bv_runtime_gas_left                  (expect 53000)
      +32 bv_runtime_refund_counter            (expect 0)
      +40 bv_runtime_calldata_floor            (expect 0)
      +48 bv_tx_log_window start               (expect 0)
      +56 bv_tx_log_window count               (expect 0)
      +64 bv_receipts_completeness_shape       (expect 6)
      +72 bv_receipts_enforce_enabled          (expect 1)
      +80  bvgr_tx_exec_state_gas[0]           (expect 0)
      +88  non-STOP helper status              (expect 4)
      +96  runtime_count after non-STOP        (expect 0)
      +104 bad-context helper status           (expect 1)
      +112 runtime_count after bad context     (expect 0)
      +120 non-creation helper status          (expect 2)
      +128 runtime_count after non-creation    (expect 0)
      +136 null-initcode helper status         (expect 3)
      +144 runtime_count after null initcode   (expect 0)
      +152 long-initcode helper status         (expect 3)
      +160 runtime_count after long initcode   (expect 0)
      +168 exec_nonstorage_effect_count        (expect 1)
      +176 created effect addr[0]              (expect 0xA5)
      +184 created effect post_balance[0]      (expect 0x42)
      +192 created effect post_nonce           (expect 1) -/
def ziskCreationRuntimeWindowsProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    -- Supported one-byte STOP top-level creation context.
    "  la t0, crw_ctx\n" ++
    "  sd zero, 0(t0)\n" ++
    "  li t1, 53000; sd t1, 40(t0)\n" ++
    "  li t1, 1; sd t1, 48(t0)\n" ++
    "  la t1, crw_stop_initcode; sd t1, 56(t0)\n" ++
    "  li t1, 1; sd t1, 64(t0)\n" ++
    "  li t1, 0x42; sd t1, 96(t0)\n" ++
    "  la t0, bv_create_addr; li t1, 0xA5; sb t1, 0(t0)\n" ++
    "  la t0, exec_nonstorage_effect_count; sd zero, 0(t0)\n" ++
    -- Synthetic exec payload: just enough block env for staging.
    "  la t2, crw_exec\n" ++
    "  li t1, 0xC0; sb t1, 32(t2)\n" ++
    "  li t1, 99; sd t1, 404(t2)\n" ++
    "  li t1, 12345; sd t1, 428(t2)\n" ++
    "  li t1, 30000000; sd t1, 412(t2)\n" ++
    "  li t1, 7; sd t1, 440(t2)\n" ++
    "  la a0, crw_ctx; la a1, crw_exec\n" ++
    "  jal ra, block_verdict_creation_runtime\n" ++
    "  li s0, 0xa0010000\n" ++
    "  sd a0, 0(s0)\n" ++
    "  la t0, bvgr_runtime_count; ld t1, 0(t0); sd t1, 8(s0)\n" ++
    "  la t0, bv_tx_status_arr; ld t1, 0(t0); sd t1, 16(s0)\n" ++
    "  la t0, bv_runtime_gas_left; ld t1, 0(t0); sd t1, 24(s0)\n" ++
    "  la t0, bv_runtime_refund_counter; ld t1, 0(t0); sd t1, 32(s0)\n" ++
    "  la t0, bv_runtime_calldata_floor; ld t1, 0(t0); sd t1, 40(s0)\n" ++
    "  la t0, bv_tx_log_window; ld t1, 0(t0); sd t1, 48(s0); ld t1, 8(t0); sd t1, 56(s0)\n" ++
    "  la t0, bv_receipts_completeness_shape; ld t1, 0(t0); sd t1, 64(s0)\n" ++
    "  la t0, bv_receipts_enforce_enabled; ld t1, 0(t0); sd t1, 72(s0)\n" ++
    "  la t0, bvgr_tx_exec_state_gas; ld t1, 0(t0); sd t1, 80(s0)\n" ++
    "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); sd t1, 168(s0)\n" ++
    "  la t0, exec_nonstorage_effect_log; lbu t1, 0(t0); sd t1, 176(s0)\n" ++
    "  lbu t1, 64(t0); sd t1, 184(s0)\n" ++
    "  ld t1, 104(t0); sd t1, 192(s0)\n" ++
    -- Unsupported non-STOP initcode must not populate runtime_count.
    "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n" ++
    "  la t0, crw_ctx; sd zero, 0(t0); li t1, 1; sd t1, 48(t0); la t1, crw_bad_initcode; sd t1, 56(t0); li t1, 1; sd t1, 64(t0)\n" ++
    "  la a0, crw_ctx; la a1, crw_exec\n" ++
    "  jal ra, block_verdict_creation_runtime\n" ++
    "  sd a0, 88(s0)\n" ++
    "  la t0, bvgr_runtime_count; ld t1, 0(t0); sd t1, 96(s0)\n" ++
    -- Bad context status must stay conservative.
    "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n" ++
    "  la t0, crw_ctx; li t1, 9; sd t1, 0(t0); li t1, 1; sd t1, 48(t0); la t1, crw_stop_initcode; sd t1, 56(t0); li t1, 1; sd t1, 64(t0)\n" ++
    "  la a0, crw_ctx; la a1, crw_exec\n" ++
    "  jal ra, block_verdict_creation_runtime\n" ++
    "  sd a0, 104(s0)\n" ++
    "  la t0, bvgr_runtime_count; ld t1, 0(t0); sd t1, 112(s0)\n" ++
    -- Non-creation contexts must not be executed as constructors.
    "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n" ++
    "  la t0, crw_ctx; sd zero, 0(t0); sd zero, 48(t0); la t1, crw_stop_initcode; sd t1, 56(t0); li t1, 1; sd t1, 64(t0)\n" ++
    "  la a0, crw_ctx; la a1, crw_exec\n" ++
    "  jal ra, block_verdict_creation_runtime\n" ++
    "  sd a0, 120(s0)\n" ++
    "  la t0, bvgr_runtime_count; ld t1, 0(t0); sd t1, 128(s0)\n" ++
    -- Missing initcode pointer and too-large initcode stay unsupported shape.
    "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n" ++
    "  la t0, crw_ctx; sd zero, 0(t0); li t1, 1; sd t1, 48(t0); sd zero, 56(t0); li t1, 1; sd t1, 64(t0)\n" ++
    "  la a0, crw_ctx; la a1, crw_exec\n" ++
    "  jal ra, block_verdict_creation_runtime\n" ++
    "  sd a0, 136(s0)\n" ++
    "  la t0, bvgr_runtime_count; ld t1, 0(t0); sd t1, 144(s0)\n" ++
    "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n" ++
    "  la t0, crw_ctx; sd zero, 0(t0); li t1, 1; sd t1, 48(t0); la t1, crw_long_initcode; sd t1, 56(t0); li t1, 2; sd t1, 64(t0)\n" ++
    "  la a0, crw_ctx; la a1, crw_exec\n" ++
    "  jal ra, block_verdict_creation_runtime\n" ++
    "  sd a0, 152(s0)\n" ++
    "  la t0, bvgr_runtime_count; ld t1, 0(t0); sd t1, 160(s0)\n" ++
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    blockVerdictCreationRuntimeFunction ++ "\n" ++
    stageCreationRuntimePayloadFunction ++ "\n" ++
    blockLogWindowSnapshotFunction ++ "\n" ++
    dispatcherCaptureExecStateGasFunction ++ "\n" ++
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 8\n" ++
    "crw_ctx:\n  .zero 192\n" ++
    "crw_exec:\n  .zero 512\n" ++
    "crw_stop_initcode:\n  .byte 0x00\n" ++
    ".balign 8\n" ++
    "crw_bad_initcode:\n  .byte 0x01\n" ++
    ".balign 8\n" ++
    "crw_long_initcode:\n  .byte 0x00, 0x00\n" ++
    ".balign 8\n" ++
    "bv_runtime_payload:\n  .zero 65536\n" ++
    "bv_runtime_gas_left:\n  .zero 8\n" ++
    "bv_runtime_refund_counter:\n  .zero 8\n" ++
    "bv_runtime_calldata_floor:\n  .zero 8\n" ++
    "bv_tx_status_arr:\n  .zero 8192\n" ++
    "bv_tx_is_creation_arr:\n  .zero 8192\n" ++
    "bv_create_addr:\n  .zero 32\n" ++
  -- GH #10944: the top-level CREATE endowment in canonical 32-byte BE, copied from the
  -- context record so the shared `record_message_value_transfer` can take a pointer to it.
  "bvcr_endow_val_be:\n  .zero 32\n" ++
  -- GH #11164: the AUTHENTICATED pre-state balance of the top-level created account, in
  -- canonical 32-byte BE.  Captured from `create_prebalance_acct+8` BEFORE
  -- `runtime_dispatcher_call`, because that buffer is rewritten by
  -- `call_frame_descend`/`create_frame_descend` and so cannot survive the constructor.
  "bvcr_created_pre_bal:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "bv_creation_ctx_ptr:\n  .zero 8\n" ++
    "bv_tx_log_window:\n  .zero 16\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "bv_last_log_start:\n  .zero 8\n" ++
    "bv_last_log_count:\n  .zero 8\n" ++
    "bv_receipts_completeness_shape:\n  .zero 8\n" ++
    "bv_receipts_enforce_enabled:\n  .zero 8\n" ++
    "bvgr_runtime_gas_left_ptr:\n  .zero 8\n" ++
    "bvgr_runtime_refund_counter_ptr:\n  .zero 8\n" ++
    "bvgr_runtime_calldata_floor_ptr:\n  .zero 8\n" ++
    "bvgr_runtime_count:\n  .zero 8\n" ++
    dispatcherExecStateGasArrayDef ++
    ".balign 8\n" ++
    "bv_block_log_count:\n  .zero 8\n" ++
    "bv_block_log_data_used:\n  .zero 8\n" ++
    "bv_block_log_desc_used:\n  .zero 8\n" ++
    "bv_block_log_overflow:\n  .zero 8\n" ++
    ".balign 8\n" ++
    "bv_block_log_descs:\n  .zero " ++ toString bvBlockLogDescBytes ++ "\n" ++
    "bv_block_log_meta:\n  .zero " ++ toString bvBlockLogMetaBytes ++ "\n" ++
    "bv_block_log_data:\n  .zero " ++ toString bvBlockLogDataBytes ++ "\n" ++
    ".balign 8\n" ++
    "srpc_env_base:\n  .zero 8\n" ++
    "m29_stage_cur:\n  .zero 8\n" ++
    "m29_stage_count:\n  .zero 8\n" ++
    "m29_stage_table:\n  .zero 8192\n" ++
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

/-! ## zisk_runtime_access_list_seeded_sload

    Focused nxio8.5.2b probe: arm the pending tx-access-list globals, run the
    same seed hook used by `runtime_dispatcher_call`, then charge the listed
    `(address, slot)` directly. The access list contains one address and slot
    zero, so the charge helper must report warm status 0, leave 5000 gas
    unchanged, and leave exactly one warm-set key. -/
def ziskRuntimeAccessListSeededSloadProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    "  la t0, rtal_probe_gas; li t1, 5000; sd t1, 0(t0)\n" ++
    "  la t0, runtime_tx_access_list_ptr; la t1, rtal_access_list; sd t1, 0(t0)\n" ++
    "  la t0, runtime_tx_access_list_len; li t1, 58; sd t1, 0(t0)\n" ++
    "  la t0, runtime_tx_access_list_seed_fn; la t1, seed_tx_access_list; sd t1, 0(t0)\n" ++
    emitTxAccessListSeedLoop ++ "\n" ++
    "  la a0, rtal_addr_token; la a1, rtal_slot_zero; la a2, rtal_probe_gas\n" ++
    "  jal ra, evm_storage_access_charge_key\n" ++
    "  li t0, 0xa0010000\n" ++
    "  sd a0, 0(t0)\n" ++
    "  la t1, rtal_probe_gas; ld t2, 0(t1); sd t2, 8(t0)\n" ++
    "  la t1, evm_storage_access_count; ld t2, 0(t1); sd t2, 16(t0)\n" ++
    "  la t1, runtime_tx_access_list_ptr; ld t2, 0(t1); sd t2, 24(t0)\n" ++
    "  la t1, runtime_tx_access_list_len; ld t2, 0(t1); sd t2, 32(t0)\n" ++
    "  la t1, runtime_tx_access_list_seed_fn; ld t2, 0(t1); sd t2, 40(t0)\n" ++
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    rlpListNthItemFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    storageAccessSeedFunction ++ "\n" ++
    storageAccessGasFunction ++ "\n" ++
    seedTxAccessListFunction
  dataAsm     :=
    ".section .data\n" ++
    ".balign 8\n" ++
    "runtime_tx_access_list_ptr:\n  .zero 8\n" ++
    "runtime_tx_access_list_len:\n  .zero 8\n" ++
    "runtime_tx_access_list_seed_fn:\n  .zero 8\n" ++
    ".balign 8\n" ++
    "rtal_probe_gas:\n  .zero 8\n" ++
    storageAccessGasData ++
    seedTxAccessListDataSection ++
    ".balign 8\n" ++
    "rtal_addr_token:\n" ++
    "  .byte 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa\n" ++
    "  .byte 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x12, 0x34, 0x56, 0x78\n" ++
    "  .zero 12\n" ++
    ".balign 8\n" ++
    "rtal_slot_zero:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "rtal_access_list:\n" ++
    "  .byte 0xf8, 0x38, 0xf7, 0x94\n" ++
    "  .byte 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa\n" ++
    "  .byte 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x12, 0x34, 0x56, 0x78\n" ++
    "  .byte 0xe1, 0xa0\n" ++
    "  .zero 32\n"
}

/-! ## zisk_ecrecover_precompile_probe (.62.2.5 e2e)

    End-to-end ECRECOVER through the DISPATCHER: arm `ecrecover_backend_ptr`
    with the real staged kernel, then run pack-bytecode input (the check
    script stages a known-vector hash/v/r/s via MSTOREs, CALLs 0x01, and
    MLOADs the output window so the recovered address lands on the stack top
    -> OUTPUT[0..32] via evmAddEpilogue). Validates the HANDLER path (staging,
    gates, recovery, keccak-address returndata, out-window copy), not just the
    kernel. Bundles the frame-helper closure (tinyInterpRegistry's CREATE
    handler needs it, mirrors ziskStageSystemCallProbeUnit) plus the NoU256
    secp256k1 chain (u256_add/sub/lt come from the curve-common-free frame
    bundle below). -/
def ziskEcrecoverPrecompileProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  la t0, ecrecover_backend_ptr\n" ++
    "  la t1, secp256k1_recover_pubkey_staged\n" ++
    "  sd t1, 0(t0)\n" ++
    "  jal ra, runtime_dispatcher_call\n" ++
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256AddBeFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    u256LtBeFunction ++ "\n" ++
    secp256k1CurveCommonFunctionsNoU256 ++ "\n" ++
    secp256k1RecoverRFunction ++ "\n" ++
    secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    "# Standalone precompile probe stubs: the ECRECOVER path never resolves non-precompile account code.\n" ++
    "account_at_header_state_root:\n  li a0, 1\n  ret\n" ++
    "account_extract_nonce:\n  li a0, 1\n  ret\n" ++
    "code_at_header_state_root:\n  li a0, 5\n  ret\n" ++
    "bal_same_block_delegation_code_resolve:\n  li a0, 1\n  ret\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    secp256k1CurveDataSection ++ "\n" ++
    secp256k1RecoverDataSection ++ "\n" ++
    txPubkeyRecoverRawDataSection ++ "\n" ++
    ".balign 8\n" ++
    "callee_balance_count:\n  .zero 8\n" ++
    ".balign 32\n" ++
    "callee_balance_table:\n  .zero " ++ toString (128 * 64) ++ "\n" ++
    ".balign 8\n" ++
    "cd_xfer_gas_precharged:\n  .zero 8\n" ++
    ".balign 32\n" ++
    "cahsr_state_root:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "cahsr_acct_struct:\n  .zero 104\n" ++
    "cahsr_code_offset:\n  .zero 8\n" ++
    "cahsr_code_length:\n  .zero 8\n" ++
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

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
    accountReadRecordFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    stageRuntimePayloadWitnessContextFunction ++ "\n" ++
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    accountReadLogDataSection ++
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
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
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
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

/-! ## zisk_derive_withdrawal_requests (8uld3.2b)

    End-to-end probe for `derive_withdrawal_requests`: stage a synthetic withdrawal
    predeploy that RETURNs a 76-byte withdrawal record (one EIP-7002 request: source 20 +
    pubkey 48 + amount 8), run it through the dispatcher via the system-call harness, and
    assert the captured return_data IS the withdrawal body (len 76, byte-faithful). The
    predeploy is `PUSH1 0xAB; PUSH1 0; MSTORE; PUSH1 76; PUSH1 0; RETURN` so body[31]=0xAB
    (the low byte of the MSTORE'd word) and body[0]=body[75]=0x00. Mirrors
    `ziskStageSystemCallProbeUnit`; bundles `derive_withdrawal_requests` +
    `withdrawal_request_predeploy_addr`.
    Output (0xa0010000): +0 body_len (expect 76), +8 status (expect 0),
    +16 body[31] (expect 0xAB), +24 body[0] (expect 0x00), +32 body[75] (expect 0x00). -/
def ziskDeriveWithdrawalRequestsProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    "  la a0, dwr_probe_code\n  li a1, 10\n  la a2, dwr_probe_exec\n  la a3, dwr_probe_out\n" ++
    "  jal ra, derive_withdrawal_requests\n" ++
    "  li t0, 0xa0010000\n" ++
    "  sd a1, 0(t0)             # withdrawal body len (expect 76)\n" ++
    "  sd a2, 8(t0)             # status (expect 0)\n" ++
    "  add t1, a0, 31; lbu t2, 0(t1); sd t2, 16(t0)   # body[31] (expect 0xAB)\n" ++
    "  lbu t2, 0(a0); sd t2, 24(t0)                   # body[0]  (expect 0x00)\n" ++
    "  add t1, a0, 75; lbu t2, 0(t1); sd t2, 32(t0)   # body[75] (expect 0x00)\n" ++
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    deriveWithdrawalRequestsFunction ++ "\n" ++
    stageSystemCallFunction ++ "\n" ++
    accountReadRecordFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    stageRuntimePayloadWitnessContextFunction ++ "\n" ++
    -- same frame-helper closure the system-call probe bundles (CREATE handler descent chain)
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    accountReadLogDataSection ++
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
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
    withdrawalRequestPredeployAddrData ++
    ".balign 8\n" ++
    "dwr_probe_code:\n  .byte 0x60, 0xab, 0x60, 0x00, 0x52, 0x60, 0x4c, 0x60, 0x00, 0xf3\n" ++   -- PUSH1 0xAB; PUSH1 0; MSTORE; PUSH1 76; PUSH1 0; RETURN
    ".balign 8\n" ++
    "dwr_probe_exec:\n  .zero 1024\n" ++
    ".balign 8\n" ++
    "dwr_probe_out:\n  .zero 4096\n" ++
    -- frame-helper data (inert for this no-CREATE predeploy; labels must exist for a standalone emit)
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

/-! ## zisk_derive_consolidation_requests (8uld3.3)

    End-to-end probe for `derive_consolidation_requests`: stage a synthetic consolidation
    predeploy that RETURNs a 116-byte consolidation record (one EIP-7251 request: source 20 +
    source_pubkey 48 + target_pubkey 48), run it through the dispatcher via the system-call
    harness, and assert the captured return_data IS the consolidation body (len 116,
    byte-faithful). The predeploy is `PUSH1 0xCD; PUSH1 0; MSTORE; PUSH1 116; PUSH1 0; RETURN`
    so body[31]=0xCD (low byte of the MSTORE'd word) and body[0]=body[115]=0x00. Mirrors
    `ziskDeriveWithdrawalRequestsProbeUnit`; bundles `derive_consolidation_requests` +
    `consolidation_request_predeploy_addr`.
    Output (0xa0010000): +0 body_len (expect 116), +8 status (expect 0),
    +16 body[31] (expect 0xCD), +24 body[0] (expect 0x00), +32 body[115] (expect 0x00). -/
def ziskDeriveConsolidationRequestsProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    "  la a0, dcr_probe_code\n  li a1, 10\n  la a2, dcr_probe_exec\n  la a3, dcr_probe_out\n" ++
    "  jal ra, derive_consolidation_requests\n" ++
    "  li t0, 0xa0010000\n" ++
    "  sd a1, 0(t0)             # consolidation body len (expect 116)\n" ++
    "  sd a2, 8(t0)             # status (expect 0)\n" ++
    "  add t1, a0, 31; lbu t2, 0(t1); sd t2, 16(t0)   # body[31] (expect 0xCD)\n" ++
    "  lbu t2, 0(a0); sd t2, 24(t0)                   # body[0]   (expect 0x00)\n" ++
    "  add t1, a0, 115; lbu t2, 0(t1); sd t2, 32(t0)  # body[115] (expect 0x00)\n" ++
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    deriveConsolidationRequestsFunction ++ "\n" ++
    stageSystemCallFunction ++ "\n" ++
    accountReadRecordFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    stageRuntimePayloadWitnessContextFunction ++ "\n" ++
    -- same frame-helper closure the system-call probe bundles (CREATE handler descent chain)
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    accountReadLogDataSection ++
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
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
    consolidationRequestPredeployAddrData ++
    ".balign 8\n" ++
    "dcr_probe_code:\n  .byte 0x60, 0xcd, 0x60, 0x00, 0x52, 0x60, 0x74, 0x60, 0x00, 0xf3\n" ++   -- PUSH1 0xCD; PUSH1 0; MSTORE; PUSH1 116; PUSH1 0; RETURN
    ".balign 8\n" ++
    "dcr_probe_exec:\n  .zero 1024\n" ++
    ".balign 8\n" ++
    "dcr_probe_out:\n  .zero 4096\n" ++
    -- frame-helper data (inert for this no-CREATE predeploy; labels must exist for a standalone emit)
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

/-! ## zisk_derive_requests_hash_e2e (8uld3.2.3 / 8uld3.4 integration)

    End-to-end: derive a withdrawal-request body from a synthetic WITHDRAWAL predeploy via the
    system-call harness, then feed it (deposit/consolidation empty) through the
    execution-derived requests_hash path (`assemble_execution_requests` -> `execution_requests_hash`
    -> `requests_hash_verify`). Proves a system-call-DERIVED body produces a deterministic
    `requests_hash` that `requests_hash_verify` ACCEPTS (match -> 0) and REJECTS when the expected
    (header) hash is corrupted (-> 1) — the soundness shape `block_verdict` will use to stop
    trusting the SSZ-input requests (8uld3.2.3/8uld3.4). Single system call (no reentrancy).
    Output (0xa0010000): +0 wbody_len (expect 76), +8 verify(zero-hash) (expect 1 mismatch),
    +16 verify(correct) (expect 0 match), +24 verify(corrupted) (expect 1 mismatch). -/
def ziskDeriveRequestsHashE2EProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    -- 1. derive a withdrawal body (76B) from the synthetic predeploy
    "  la a0, drhe_probe_code\n  li a1, 10\n  la a2, drhe_probe_exec\n  la a3, drhe_probe_out\n" ++
    "  jal ra, derive_withdrawal_requests\n" ++          -- a0=wbody ptr, a1=len, a2=status
    "  la t0, drhe_wbody_ptr; sd a0, 0(t0); la t0, drhe_wbody_len; sd a1, 0(t0)\n" ++
    "  li t0, 0xa0010000; sd a1, 0(t0)\n" ++             -- +0 wbody_len
    -- 2. verify against an all-zero expected hash -> mismatch (1); leaves the computed hash in rhv_hash
    "  la t0, drhe_exp_hash; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
    "  la t0, drhe_wbody_ptr; ld a2, 0(t0); la t0, drhe_wbody_len; ld a3, 0(t0)\n" ++
    "  li a0, 0; li a1, 0; li a4, 0; li a5, 0\n" ++       -- deposit/consolidation empty
    "  la a6, drhe_exp_hash; la a7, drhe_section\n" ++
    "  jal ra, requests_hash_verify\n" ++
    "  li t0, 0xa0010000; sd a0, 8(t0)\n" ++             -- +8 verify(zero) expect 1
    -- copy the computed hash (rhv_hash) into drhe_exp_hash (the now-correct expected hash)
    "  la t1, rhv_hash; la t2, drhe_exp_hash; li t3, 32\n" ++
    ".Ldrhe_cp:\n" ++
    "  beqz t3, .Ldrhe_cpd; lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Ldrhe_cp\n" ++
    ".Ldrhe_cpd:\n" ++
    -- 3. verify against the correct hash -> match (0)
    "  la t0, drhe_wbody_ptr; ld a2, 0(t0); la t0, drhe_wbody_len; ld a3, 0(t0)\n" ++
    "  li a0, 0; li a1, 0; li a4, 0; li a5, 0; la a6, drhe_exp_hash; la a7, drhe_section\n" ++
    "  jal ra, requests_hash_verify\n" ++
    "  li t0, 0xa0010000; sd a0, 16(t0)\n" ++            -- +16 verify(correct) expect 0
    -- 4. corrupt the expected hash, verify -> mismatch (1)
    "  la t0, drhe_exp_hash; lbu t1, 0(t0); xori t1, t1, 0xff; sb t1, 0(t0)\n" ++
    "  la t0, drhe_wbody_ptr; ld a2, 0(t0); la t0, drhe_wbody_len; ld a3, 0(t0)\n" ++
    "  li a0, 0; li a1, 0; li a4, 0; li a5, 0; la a6, drhe_exp_hash; la a7, drhe_section\n" ++
    "  jal ra, requests_hash_verify\n" ++
    "  li t0, 0xa0010000; sd a0, 24(t0)\n" ++            -- +24 verify(corrupt) expect 1
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    deriveWithdrawalRequestsFunction ++ "\n" ++
    stageSystemCallFunction ++ "\n" ++
    accountReadRecordFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    stageRuntimePayloadWitnessContextFunction ++ "\n" ++
    -- requests_hash machinery (assemble -> sha256 -> verify); zkvm_sha256 is an ecall bridge
    requestsHashVerifyFunction ++ "\n" ++
    assembleExecutionRequestsFunction ++ "\n" ++
    executionRequestsHashFunction ++ "\n" ++
    bgvU32leFunction ++ "\n" ++
    -- NOTE: zkvm_sha256 + its sha256_w_* data are already provided by the dispatcher harness
    -- (tinyInterpRegistry's SHA256 precompile), so we do NOT re-bundle them here (double-def).
    -- frame-helper closure (CREATE handler descent chain), same as the derive probes
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    accountReadLogDataSection ++
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
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
    withdrawalRequestPredeployAddrData ++
    ".balign 8\n" ++
    "drhe_probe_code:\n  .byte 0x60, 0xab, 0x60, 0x00, 0x52, 0x60, 0x4c, 0x60, 0x00, 0xf3\n" ++   -- PUSH1 0xAB; PUSH1 0; MSTORE; PUSH1 76; PUSH1 0; RETURN
    ".balign 8\n" ++
    "drhe_probe_exec:\n  .zero 1024\n" ++
    ".balign 8\n" ++
    "drhe_probe_out:\n  .zero 4096\n" ++
    -- requests-hash scratch + computed/expected hash buffers
    ".balign 8\n" ++
    "drhe_section:\n  .zero 4096\n" ++
    "drhe_wbody_ptr:\n  .zero 8\n" ++
    "drhe_wbody_len:\n  .zero 8\n" ++
    ".balign 32\n" ++
    "drhe_exp_hash:\n  .zero 32\n" ++
    "rhv_hash:\n  .zero 32\n" ++
    -- sha256_w_* (executionRequestsHashShaDataSection) is provided by the harness; only the
    -- requests-hash-specific scratch (erh_digests/erh_blob) is added here.
    executionRequestsHashDataSection ++ "\n" ++
    -- frame-helper data (inert for this no-CREATE predeploy; labels must exist for a standalone emit)
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

/-! ## zisk_derive_block_system_requests (8uld3.2.3/8uld3.4 glue)

    Verify `derive_block_system_requests` runs BOTH system calls sequentially and copies each
    body to a stable buffer (the verdict needs both live at once). Synthetic withdrawal predeploy
    RETURNs 76 bytes (byte[31]=0xAB); consolidation predeploy RETURNs 116 bytes (byte[31]=0xCD).
    Proves two sequential dispatcher runs are independent + the first body survives the second
    call (system_call_returndata is shared, so the copy-out is load-bearing).
    Output (0xa0010000): +0 wlen (expect 76), +8 clen (expect 116), +16 wbody[31] (expect 0xAB),
    +24 cbody[31] (expect 0xCD), +32 status (expect 0). -/
def ziskDeriveBlockSystemRequestsProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    "  la a0, dbsr_w_code\n  li a1, 10\n  la a2, dbsr_c_code\n  li a3, 10\n  la a4, dbsr_probe_exec\n  la a5, dbsr_probe_staging\n" ++
    "  jal ra, derive_block_system_requests\n" ++
    "  li t0, 0xa0010000\n" ++
    "  la t1, dbsr_wlen; ld t2, 0(t1); sd t2, 0(t0)\n" ++          -- +0 wlen (expect 76)
    "  la t1, dbsr_clen; ld t2, 0(t1); sd t2, 8(t0)\n" ++          -- +8 clen (expect 116)
    "  la t1, dbsr_wbody; add t1, t1, 31; lbu t2, 0(t1); sd t2, 16(t0)\n" ++   -- +16 wbody[31] (0xAB)
    "  la t1, dbsr_cbody; add t1, t1, 31; lbu t2, 0(t1); sd t2, 24(t0)\n" ++   -- +24 cbody[31] (0xCD)
    "  sd a0, 32(t0)\n" ++                                         -- +32 status (expect 0)
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    deriveBlockSystemRequestsFunction ++ "\n" ++
    deriveWithdrawalRequestsFunction ++ "\n" ++
    deriveConsolidationRequestsFunction ++ "\n" ++
    stageSystemCallFunction ++ "\n" ++
    accountReadRecordFunction ++ "\n" ++
    readSetsMergeOneFunction ++ "\n" ++
    readSetsIncorporateTxFunction ++ "\n" ++
    readSetsDiscardTxFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    stageRuntimePayloadWitnessContextFunction ++ "\n" ++
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    accountReadLogDataSection ++
    storageReadLogDataSection ++
    codeReadLogDataSection ++
    readSetsBlockDataSection ++
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
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
    withdrawalRequestPredeployAddrData ++
    consolidationRequestPredeployAddrData ++
    deriveBlockSystemRequestsData ++
    ".balign 8\n" ++
    "dbsr_w_code:\n  .byte 0x60, 0xab, 0x60, 0x00, 0x52, 0x60, 0x4c, 0x60, 0x00, 0xf3\n" ++   -- PUSH1 0xAB; MSTORE; RETURN 76
    ".balign 8\n" ++
    "dbsr_c_code:\n  .byte 0x60, 0xcd, 0x60, 0x00, 0x52, 0x60, 0x74, 0x60, 0x00, 0xf3\n" ++   -- PUSH1 0xCD; MSTORE; RETURN 116
    ".balign 8\n" ++
    "dbsr_probe_exec:\n  .zero 1024\n" ++
    ".balign 8\n" ++
    "dbsr_probe_staging:\n  .zero 4096\n" ++
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

/-! ## zisk_sstore_clear_gas_probe (regression pin for the SSTORE-clear charge; was the .57.11.6.5.3 / d' reproducer)

    Dispatches the multi_transaction_gas_accounting tx0 recipient bytecode
    (10× PUSH0; PUSH1 i; SSTORE — clearing slots 0..9, each preloaded to 1)
    with gas=151050, and dumps the post-dispatch env.gasRemaining (env+568) +
    persistent-log count (env+448). SPEC charges 21000 intrinsic + 10×13000
    (cold clean-changing SSTORE-clear: 3000 cold access + 10000 write) + 50 pushes =
    151050 (full) -> gas_left = 0, log count = 10 preload + 10 SSTORE appends =
    20. (The probe originally pinned the d' undercharge — gas_left 25200 —
    This is the sole remaining production consumer of the generic input-driven
    preload path; production callers pass zero. The probe had TWO causes, both fixed: the BAL preload keys were staged BE and
    invisible to the LE exec-log scan, and this probe's own preload mirrored
    that BE staging.) Stages via stage_runtime_payload_code with the 10-slot
    LE preload; bundles the same dispatcher + frame-helper closure as the
    derive probes (so it links standalone, unlike the plain runtime_dispatcher
    unit).
    Output (0xa0010000): +0 gas_left (env+568), +8 persistent_log_count (env+448),
    +16 status (0 ok / 1 staging unsupported). -/
def ziskSstoreClearGasProbeUnit : BuildUnit := {
  body        := []
  prologueAsm :=
    "  li sp, 0xa0050000\n" ++
    -- build ctx (192B): zero, gas@40=151050, recipient@72 = scgp_recip (20B)
    "  la t0, scgp_ctx; mv t1, t0; li t2, 24\n" ++
    ".Lscgp_zc:\n  sd zero, 0(t1); addi t1, t1, 8; addi t2, t2, -1; bnez t2, .Lscgp_zc\n" ++
    "  li t1, 151050; sd t1, 40(t0)\n" ++
    "  addi t1, t0, 72; la t2, scgp_recip; li t3, 20\n" ++
    ".Lscgp_rc:\n  beqz t3, .Lscgp_rcd; lbu t4, 0(t2); sb t4, 0(t1); addi t2, t2, 1; addi t1, t1, 1; addi t3, t3, -1; j .Lscgp_rc\n" ++
    ".Lscgp_rcd:\n" ++
    -- build the 10-slot preload (count*64: key:32, value:32, both in the EVM
    -- stack/exec-log LITTLE-ENDIAN-limb order that stage_runtime_payload_code
    -- copies verbatim — dispatch_tx_runtime_code byte-reverses the BAL's BE keys
    -- BEFORE staging, so the staged format is LE). zero 640B, then set
    -- key[i].byte0=i, value[i].byte0=1 (i.e. key=i, value=1 as LE words). The
    -- original BE staging (key byte31=i) left slots 1..9 invisible to the LE
    -- scan, which is what this probe's old 25200 "expected undercharge" pinned.
    "  la t0, scgp_preload; li t1, 80\n" ++
    ".Lscgp_zp:\n  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lscgp_zp\n" ++
    "  la t0, scgp_preload; li t1, 0\n" ++
    ".Lscgp_bp:\n  li t2, 10; beq t1, t2, .Lscgp_bpd\n" ++
    "  slli t3, t1, 6; add t4, t0, t3; sb t1, 0(t4)\n" ++                          -- key[i] byte0 = i (LE)
    "  addi t5, t4, 32; li t6, 1; sb t6, 0(t5)\n" ++                               -- value[i] byte0 = 1 (LE)
    "  addi t1, t1, 1; j .Lscgp_bp\n" ++
    ".Lscgp_bpd:\n" ++
    -- stage_runtime_payload_code(ctx, out, exec, code, 40, preload, 10)
    "  la a0, scgp_ctx; la a1, scgp_out; la a2, scgp_exec; la a3, scgp_code; li a4, 40; la a5, scgp_preload; li a6, 10\n" ++
    "  jal ra, stage_runtime_payload_code\n" ++
    "  bnez a0, .Lscgp_fail\n" ++
    -- dispatch
    "  la t1, scgp_out; addi t1, t1, 8; la t0, runtime_dispatcher_input_ptr; sd t1, 0(t0)\n" ++
    "  jal ra, runtime_dispatcher_call\n" ++
    "  la t0, runtime_dispatcher_input_ptr; sd zero, 0(t0)\n" ++
    -- dump gas_left + log count
    "  li t0, 0xa0010000; la t1, evm_env\n" ++
    "  ld t2, 568(t1); sd t2, 0(t0)\n" ++          -- +0 gas_left
    "  ld t2, 448(t1); sd t2, 8(t0)\n" ++          -- +8 persistent log count
    "  sd zero, 16(t0)\n" ++                       -- +16 status ok
    "  j .Lscgp_done\n" ++
    ".Lscgp_fail:\n  li t0, 0xa0010000; li t2, 1; sd t2, 16(t0)\n" ++
    ".Lscgp_done:\n" ++
    "  li x17, 93\n  li x10, 0\n  ecall\n" ++
    stageRuntimePayloadCodeFunction ++ "\n" ++
    stageRuntimePayloadWitnessContextFunction ++ "\n" ++
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
    nonstorageEffectLatestBalanceFunction ++ "\n" ++
    nonstorageEffectLatestNonceFunction ++ "\n" ++
    u256SubBeFunction ++ "\n" ++
    witnessCodesLookupByHashFunction ++ "\n" ++
    rlpListCountItemsFunction ++ "\n" ++
    emitRuntimeDispatcherCallablePrologue
  epilogueAsm := emitDispatcherCallableEpilogue tinyInterpRegistry evmAddEpilogue
  dataAsm     :=
    emitRuntimeDispatcherDataSection tinyInterpRegistry ++ "\n" ++
    ".balign 32\n" ++
    "wclh_scratch_hash:\n  .zero 32\n" ++
    ".balign 8\n" ++
    "srpc_env_base:\n  .zero 8\n" ++
    "m29_stage_cur:\n  .zero 8\n" ++
    "m29_stage_count:\n  .zero 8\n" ++
    "m29_stage_table:\n  .zero 8192\n" ++
    ".balign 8\n" ++
    "scgp_ctx:\n  .zero 192\n" ++
    ".balign 8\n" ++
    "scgp_recip:\n  .byte 0x4e, 0xa7, 0x7b, 0x8b, 0x4e, 0xee, 0x51, 0x42, 0x9b, 0x6f, 0xa1, 0xf7, 0xec, 0xbc, 0x41, 0xdb, 0x9c, 0xc1, 0x9e, 0xbc\n" ++
    ".balign 8\n" ++
    "scgp_code:\n  .byte 0x5f, 0x60, 0x00, 0x55, 0x5f, 0x60, 0x01, 0x55, 0x5f, 0x60, 0x02, 0x55, 0x5f, 0x60, 0x03, 0x55, 0x5f, 0x60, 0x04, 0x55, 0x5f, 0x60, 0x05, 0x55, 0x5f, 0x60, 0x06, 0x55, 0x5f, 0x60, 0x07, 0x55, 0x5f, 0x60, 0x08, 0x55, 0x5f, 0x60, 0x09, 0x55\n" ++   -- 10x PUSH0;PUSH1 i;SSTORE (clear slots 0..9)
    ".balign 8\n" ++
    "scgp_preload:\n  .zero 640\n" ++
    ".balign 8\n" ++
    "scgp_exec:\n  .zero 1024\n" ++
    ".balign 8\n" ++
    "scgp_out:\n  .zero 4096\n" ++
    ".balign 8\n" ++
    "evm_call_depth:\n  .zero 8\n" ++
    ".balign 16\n" ++
    "frame_save_area:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "frame_call_ctx:\n  .zero 32800\n" ++
    ".balign 16\n" ++
    "frame_parent_bases:\n  .zero 16400\n" ++
    ".balign 32\n" ++
    "call_frame_arena:\n  .zero " ++ toString (0x39000 : Nat) ++ "\n" ++
    ".balign 8\n" ++
    "rb_running_block_bloom:\n  .zero 256\n" ++
    "rb_running_receipt_bloom:\n  .zero 256\n" ++
    "rb_bloom_checkpoints:\n  .zero 262144\n"
}

end EvmAsm.Codegen
