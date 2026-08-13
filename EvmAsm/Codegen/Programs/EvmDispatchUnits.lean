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

/-! ## zisk_stage_system_call (8uld3.2.1c)

    End-to-end probe for `stage_system_call`: stage a SYSTEM call to a synthetic
    predeploy that RETURNs 32 known bytes (`PUSH1 0x42; PUSH1 0; MSTORE; PUSH1 32;
    PUSH1 0; RETURN`), run it through the callable runtime dispatcher with
    system_call_mode=1, and assert the depth-0 RETURN was captured (#8681) into
    system_call_returndata. Bundles the dispatcher (tinyInterpRegistry) + the
    staging functions; mirrors `runtimeDispatcherCallProbeUnit`'s structure.
    Output (0xa0010000): +0 returndata_len (expect 32), +8 status (expect 0),
    +16 returndata[31] (expect 0x42), +24 returndata[0] (expect 0x00). -/

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

/-! ## zisk_derive_block_system_requests (8uld3.2.3/8uld3.4 glue)

    Verify `derive_block_system_requests` runs BOTH system calls sequentially and copies each
    body to a stable buffer (the verdict needs both live at once). Synthetic withdrawal predeploy
    RETURNs 76 bytes (byte[31]=0xAB); consolidation predeploy RETURNs 116 bytes (byte[31]=0xCD).
    Proves two sequential dispatcher runs are independent + the first body survives the second
    call (system_call_returndata is shared, so the copy-out is load-bearing).
    Output (0xa0010000): +0 wlen (expect 76), +8 clen (expect 116), +16 wbody[31] (expect 0xAB),
    +24 cbody[31] (expect 0xCD), +32 status (expect 0). -/

end EvmAsm.Codegen
