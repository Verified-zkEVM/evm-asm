/- EvmAsm.Codegen.Programs.StatelessGuest

  BuildUnit wrapper for the stateless guest entrypoint.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.StatelessVerdict
/-
  EvmAsm.Codegen.Programs.StatelessGuest

  BuildUnit wiring for the stateless guest body, epilogue, and data section.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.EvmBasic
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.BlockVerdictV2
import EvmAsm.Codegen.Programs.BlockVerdictMtxEoa
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Stateless.Entry

namespace EvmAsm.Codegen

/-! ## stateless_guest body -- PR-K5 keccak hash field

    Replaces the zero-stub `new_payload_request_root` field in
    `Stateless.Entry.run_stateless_guest`'s SSZ output with the
    keccak256 of the entire SSZ-input byte string the host
    streamed in via `ziskemu -i`. Concretely:

    - Body: the unchanged `Stateless.Entry.run_stateless_guest`
      Program. It writes:
        bytes  0..32 : zero hash (placeholder)
        byte      32 : successful_validation (PR4/PR5 derived)
        bytes 33..41 : chain_id (PR3 from-decode)
        bytes 41..48 : zero gap
        bytes 48..56 : header_count diagnostic (PR6 from-decode)
    - Epilogue (raw asm): set up sp, load (data ptr, len) from
      INPUT_ADDR + (16, 8), set output = OUTPUT_ADDR + 0, and
      `jal ra, zkvm_keccak256`. The function overwrites
      OUTPUT[0..32] with keccak256(input bytes), clobbering the
      zero stub.

    The host-side `compute_new_payload_request_root` per the spec
    is SSZ `hash_tree_root` (SHA-256), not Keccak. PR-K5 stamps a
    *content-dependent* hash there so the test harness has a
    non-trivial value to verify and the keccak bridge is wired
    into the encoder pipeline end-to-end. Once PR-S series lands,
    the SHA-256 hash_tree_root replaces this keccak. -/

/-- Stateless guest program with the codegen epilogue and guest data section. -/
def statelessGuestUnit : BuildUnit := {
  -- GH #11186: raised log arenas + lead pad must be the FIRST `.bss` material
  -- in the whole guest `.s`. `epilogueAsm` (via SharedHelpers) emits `widx_*`
  -- zeros that `moveZeroDataToBss` promotes before `dataAsm` runs, so putting
  -- logs in `dataAsm` left them mid-bss and overlapping scheme-A absolute
  -- arenas. `prologueAsm` is emitted right after `textPreamble` and before
  -- body/epilogue, so this block owns `.bss` HEAD at `0xa0b70000`.
  -- Pad `0x14fe880` covers scheme-A absolute pack through page-aligned TSW end
  -- (`0xa2e07000`); main body (`widx_*`, …) follows immediately — no pin to the
  -- legacy `0xa3110000` base (saves ~3 MiB so storage-undo clears ACCOUNT_WRITES).
  prologueAsm :=
    ".section .bss,\"aw\",@nobits\n" ++
    ".balign 8\n" ++
    "evm_event_logs:\n  .zero 11444992\n" ++
    ".balign 8\n" ++
    "evm_log_data:\n  .zero 2095652\n" ++
    ".balign 32\n" ++
    "evm_log_data_meta:\n  .zero 715312\n" ++
    "evm_log_data_used:\n  .zero 8\n" ++
    "evm_log_data_overflow:\n  .zero 8\n" ++
    "bss_lead_pad:\n  .zero 0x14fe880\n" ++
    ".section .text\n"
  body        := EvmAsm.Stateless.run_stateless_guest
  epilogueAsm :=
    statelessGuestEpilogue ++ "\n" ++
    "  j .Lstateless_guest_halt_after_runtime_dispatcher\n" ++
    emitRuntimeDispatcherCallableCoreSharedHelpers
      callFrameGuestRegistry evmAddEpilogue depth0SharedPrecompileArmAsm ++ "\n" ++
    -- 8uld3.2.3.1 (A): EIP-7002/7251 request-derivation leaves. The combined glue
    -- `derive_block_system_requests` is probe-only (#11156): the guest inlines the
    -- same sequence in deferred system-request staging and never jals the wrapper.
    deriveWithdrawalRequestsFunction ++ "\n" ++
    deriveConsolidationRequestsFunction ++ "\n" ++
    deriveBuilderDepositRequestsFunction ++ "\n" ++
    deriveBuilderExitRequestsFunction ++ "\n" ++
    stageSystemCallFunction ++ "\n" ++
    stageSystemCallPayloadFunction ++ "\n" ++
    processBlockStartSystemTransactionsFunction ++ "\n" ++
    -- 8uld3.2.3.2 (B): link the EIP-6110 deposit-request derivation (parse_deposit_requests
    -- scans block receipts for DEPOSIT_CONTRACT_ADDRESS logs -> type-0 deposit bodies, +
    -- extract_deposit_data). Self-contained (no dispatcher deps); the receipts tail
    -- consumes this derived body directly and does not synthesize calldata requests.
    parseDepositRequestsFunction ++ "\n" ++
    extractDepositDataFunction ++ "\n" ++
    materializeLogRecordsFunction ++ "\n" ++
    -- 8uld3.2.3.3.1 (C.1): assemble [deposit, derived-w, derived-c] into the SSZ
    -- execution_requests section that execution_requests_hash then hashes.
    assembleExecutionRequestsFunction ++ "\n" ++
    requestsHashVerifyFunction ++ "\n" ++
    ".Lstateless_guest_halt_after_runtime_dispatcher:\n"
  -- guest scratch + the Step-2 verdict's data (zk3_state / rfu_* are dedup'd out
  -- of the guest section since the appended verdict section provides them). The
  -- runtime dispatcher data also reuses that shared zk3_state scratch.
  dataAsm     :=
    statelessGuestDataSection ++ "\n" ++
    statelessVerdictV2GuestData ++ "\n" ++
    -- 8uld3.2.3.1 (A): harness-specific data not provided by the dispatcher/guest data
    -- (system_call_mode/returndata are in the dispatcher data; m29_*/srpc_env_base/frame data
    -- are already present). scc_ctx/scc_system_addr/ssc_saved_* are inline-only in the probes.
    ".balign 8\n" ++
    "scc_ctx:\n  .zero 192\n" ++
    ".section .data\n" ++
    ".balign 8\n" ++
    "scc_system_addr:\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
    "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe\n" ++
    ".balign 8\n" ++
    "ssc_saved_ra:\n  .zero 8\n" ++
    "ssc_saved_s0:\n  .zero 8\n" ++
    "ssc_calldata_ptr:\n  .zero 8\n" ++
    "ssc_calldata_len:\n  .zero 8\n" ++
    "pbsst_saved_ra:\n  .zero 8\n" ++
    "pbsst_code_ptr:\n  .zero 8\n" ++
    "pbsst_code_len:\n  .zero 8\n" ++
    withdrawalRequestPredeployAddrData ++
    consolidationRequestPredeployAddrData ++
    builderContractAddrData ++
    ".section .bss, \"aw\", @nobits\n" ++
    deriveBlockSystemRequestsData ++ "\n" ++
    -- 8uld3.2.3.2 (B): deposit-derivation data (DEPOSIT_CONTRACT_ADDRESS, deposit event sig,
    -- pdr_out body buffer, pdr_status). None present in the guest/dispatcher data.
    ".section .data\n" ++
    ".balign 8\n" ++
    "pdr_deposit_addr:\n" ++
    "  .byte 0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40\n" ++
    "  .byte 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30\n" ++
    "  .byte 0x3d, 0x77, 0x05, 0xfa\n" ++
    ".balign 8\n" ++
    "pdr_deposit_sig:\n" ++
    "  .byte 0x64, 0x9b, 0xbc, 0x62, 0xd0, 0xe3, 0x13, 0x42\n" ++
    "  .byte 0xaf, 0xea, 0x4e, 0x5c, 0xd8, 0x2d, 0x40, 0x49\n" ++
    "  .byte 0xe7, 0xe1, 0xee, 0x91, 0x2f, 0xc0, 0x88, 0x9a\n" ++
    "  .byte 0xa7, 0x90, 0x80, 0x3b, 0xe3, 0x90, 0x38, 0xc5\n" ++
    ".section .bss, \"aw\", @nobits\n" ++
    ".balign 8\n" ++
    "pdr_out:\n  .zero 2048\n" ++
    "pdr_status:\n  .zero 8\n" ++
    "rhv_hash:\n  .zero 32\n" ++
    emitRuntimeDispatcherDataSectionSharedGuest callFrameGuestRegistry
}

end EvmAsm.Codegen
