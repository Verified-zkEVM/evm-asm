/- EvmAsm.Codegen.Programs.Registry
  Program lookup registry for the codegen tool.
-/
import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.And.Program
import EvmAsm.Evm64.Byte.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.Dup.Program
import EvmAsm.Evm64.Eq.Program
import EvmAsm.Evm64.Gt.Program
import EvmAsm.Evm64.IsZero.Program
import EvmAsm.Evm64.Lt.Program
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
import EvmAsm.Evm64.Multiply.Callable -- EXP's inline mul_callable (Programs/Evm.lean)
import EvmAsm.Evm64.Multiply.Program
import EvmAsm.Evm64.Not.Program
import EvmAsm.Evm64.Or.Program
import EvmAsm.Evm64.Pop.Program
import EvmAsm.Evm64.Push.Program
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SMod.Program
import EvmAsm.Evm64.Sgt.Program
import EvmAsm.Evm64.Shift.Program
import EvmAsm.Evm64.SignExtend.Program
import EvmAsm.Evm64.Slt.Program
import EvmAsm.Evm64.Sub.Program
import EvmAsm.Evm64.Swap.Program
import EvmAsm.Evm64.Xor.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.Evm
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMessageCallGas
import EvmAsm.Codegen.Programs.EvmAccountWitness
import EvmAsm.Codegen.Programs.EIP7708Logs
import EvmAsm.Codegen.Programs.EvmBalance
import EvmAsm.Codegen.Programs.EvmExtcodecopy
import EvmAsm.Codegen.Programs.EvmArithUnits
import EvmAsm.Codegen.Programs.EvmDispatchUnits
import EvmAsm.Codegen.Programs.Clz
import EvmAsm.Codegen.Programs.ExpProperty
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Probes.HashProbes
import EvmAsm.Codegen.Programs.Modexp
import EvmAsm.Codegen.Programs.ModexpBackend
import EvmAsm.Codegen.Programs.PrecompileRuntime
import EvmAsm.Codegen.Programs.PrecompileSharedExecute
import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.Secp256k1Curve
import EvmAsm.Codegen.Programs.Secp256k1Recover
import EvmAsm.Codegen.Programs.Bn254Curve
import EvmAsm.Codegen.Programs.Bls12Field
import EvmAsm.Codegen.Programs.Bls12G1
import EvmAsm.Codegen.Programs.Bls12G2
import EvmAsm.Codegen.Programs.Bls12Pairing
import EvmAsm.Codegen.Programs.Bls12Map
import EvmAsm.Codegen.Programs.Bls12Kzg
import EvmAsm.Codegen.Programs.Blake2f
import EvmAsm.Codegen.Programs.AccountWriteMap
import EvmAsm.Codegen.Programs.AccountWriteMapTail
import EvmAsm.Codegen.Programs.P256Verify
import EvmAsm.Codegen.Programs.Ripemd160
import EvmAsm.Codegen.Programs.Bn254Fp2
import EvmAsm.Codegen.Programs.Bn254Fq12
import EvmAsm.Codegen.Programs.Bn254Pairing
import EvmAsm.Codegen.Programs.Selfdestruct
import EvmAsm.Codegen.Programs.SelfdestructDescriptors
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.MptInsertWalk
import EvmAsm.Codegen.Programs.MptInsert
import EvmAsm.Codegen.Programs.MptInsertWalkDb
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptStateRootIns
import EvmAsm.Codegen.Programs.MptIndexedTrieRoot
import EvmAsm.Codegen.Programs.WithdrawalsRootIndexed
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.ReceiptsRootIndexed
import EvmAsm.Codegen.Programs.ReceiptsConsensus
import EvmAsm.Codegen.Programs.MptDeleteWalkDb
import EvmAsm.Codegen.Programs.MptDeleteAcc
import EvmAsm.Codegen.Programs.WithdrawalsStateRoot
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.BalCodePreimages
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalAccountPath
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.BalAccountApplyPostFields
import EvmAsm.Codegen.Programs.BalAccountChangeValue
import EvmAsm.Codegen.Programs.BalAccountChangeDescriptor
import EvmAsm.Codegen.Programs.BalAccountRecordArray
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.StorageEffectRecords
import EvmAsm.Codegen.Programs.SstoreGasRefund
import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Programs.BlockGasRemaining
import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StorageRoot
import EvmAsm.Codegen.Programs.MptInternal
import EvmAsm.Codegen.Programs.MptNibbles
import EvmAsm.Codegen.Programs.WitnessCodeLookup
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxBlobGas
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.Eip7702Authority
import EvmAsm.Codegen.Programs.TxPubkey
import EvmAsm.Codegen.Programs.VerifyPublicKeysSenders
import EvmAsm.Codegen.Programs.SeedTxAccessList
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
import EvmAsm.Codegen.Programs.TxGasSenderBalLookup
import EvmAsm.Codegen.Programs.TxRefund
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.Block
import EvmAsm.Codegen.Programs.BlockEmpty
import EvmAsm.Codegen.Programs.BlockValidate
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.AccountFields
import EvmAsm.Codegen.Programs.BlockRoots
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderBaseFee
import EvmAsm.Codegen.Programs.ValidateHeaderPair
import EvmAsm.Codegen.Programs.BlockHeaderSszToRlp
import EvmAsm.Codegen.Programs.Step2Verdict
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Codegen.Programs.Chain
import EvmAsm.Codegen.Programs.ChainValidate
import EvmAsm.Codegen.Programs.ChainValidateBlob
import EvmAsm.Codegen.Programs.ChainValidatePostMerge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.BlockHashPredicates
import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Codegen.Programs.HeaderU64
import EvmAsm.Codegen.Programs.Receipt
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.StatePredicates
import EvmAsm.Codegen.Programs.WitnessCodesKeccakAtIndex
import EvmAsm.Codegen.Programs.BlockNumberAtBlockHash
import EvmAsm.Codegen.Programs.BlockHashWindow
import EvmAsm.Codegen.Programs.ExtcodehashAtBlockNumber
import EvmAsm.Codegen.Programs.ExtcodecopyAtBlockNumber
import EvmAsm.Codegen.Programs.SloadAtBlockNumber
import EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockNumber
import EvmAsm.Codegen.Programs.TransactionsRootAtBlockNumber
import EvmAsm.Codegen.Programs.GasLimitAtBlockNumber
import EvmAsm.Codegen.Programs.GasUsedAtBlockNumber
import EvmAsm.Codegen.Programs.ReceiptsRootAtBlockNumber
import EvmAsm.Codegen.Programs.OmmersHashAtBlockNumber
import EvmAsm.Codegen.Programs.ParentBeaconBlockRootAtBlockNumber
import EvmAsm.Codegen.Programs.WithdrawalsRootAtBlockNumber
import EvmAsm.Codegen.Programs.PrevRandaoAtBlockNumber
import EvmAsm.Codegen.Programs.ExcessBlobGasAtBlockNumber
import EvmAsm.Codegen.Programs.BlobGasUsedAtBlockNumber
import EvmAsm.Codegen.Programs.HeaderNonceAtBlockNumber
import EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockNumber
import EvmAsm.Codegen.Programs.BlockHashAtBlockNumber
import EvmAsm.Codegen.Programs.BlockHashAtStateRoot
import EvmAsm.Codegen.Programs.CodeAtStateRoot
import EvmAsm.Codegen.Programs.BlockNumberAtStateRoot
import EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockHash
import EvmAsm.Codegen.Programs.GasLimitAtBlockHash
import EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockHash
import EvmAsm.Codegen.Programs.GasUsedAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodehashAtBlockHash
import EvmAsm.Codegen.Programs.SloadAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodecopyAtBlockHash
import EvmAsm.Codegen.Programs.StorageRootInWitness
import EvmAsm.Codegen.Programs.WitnessStorageKeccakAtIndex
import EvmAsm.Codegen.Programs.WitnessStorageNodeKindDistribution
import EvmAsm.Codegen.Programs.WitnessHeadersAccountAtIndex
import EvmAsm.Codegen.Programs.WitnessNodeKindDistribution
import EvmAsm.Codegen.Programs.WitnessStateKeccakAtIndex
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.RuntimeAccountWitness
import EvmAsm.Codegen.Programs.EvmOpcodesStorageRoot
import EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy
import EvmAsm.Codegen.Programs.AccountFieldGetters
import EvmAsm.Codegen.Programs.WitnessValidation
import EvmAsm.Codegen.Programs.StorageProof
import EvmAsm.Codegen.Programs.Eip4788
import EvmAsm.Codegen.Programs.CodeVerify
import EvmAsm.Codegen.Programs.StorageVerify
import EvmAsm.Codegen.Programs.Eip2935
import EvmAsm.Codegen.Programs.StorageCompose
import EvmAsm.Codegen.Programs.EvmCodes
import EvmAsm.Codegen.Programs.TxRoot
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.Withdrawal
import EvmAsm.Codegen.Programs.WithdrawalPath
import EvmAsm.Codegen.Programs.SszWithdrawal
import EvmAsm.Codegen.Programs.SszWitnessState
import EvmAsm.Codegen.Programs.SszPayloadWithdrawals
import EvmAsm.Codegen.Programs.SszParentHeader
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.EvmBasic
import EvmAsm.Codegen.Programs.EvmRegistry
import EvmAsm.Codegen.Programs.BlockVerdictMtxEoa
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.ExtractDepositData
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Stateless.Entry
import EvmAsm.Codegen.Programs.BlockVerdict
import EvmAsm.Codegen.Programs.BlockVerdictGasResultArena
import EvmAsm.Codegen.Programs.BlockVerdictTxGasLimits
import EvmAsm.Codegen.Programs.BlockVerdictV2
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.OmmersHashAtBlockHash
import EvmAsm.Codegen.Programs.ParentBeaconBlockRootAtBlockHash
import EvmAsm.Codegen.Programs.TransactionsRootAtBlockHash
import EvmAsm.Codegen.Programs.ReceiptsRootAtBlockHash
import EvmAsm.Codegen.Programs.WithdrawalsRootAtBlockHash
import EvmAsm.Codegen.Programs.PrevRandaoAtBlockHash
import EvmAsm.Codegen.Programs.HeaderNonceAtBlockHash
import EvmAsm.Codegen.Programs.ExcessBlobGasAtBlockHash
import EvmAsm.Codegen.Programs.BlobGasUsedAtBlockHash
import EvmAsm.Codegen.Programs.BlobGasPairAtBlockHash
import EvmAsm.Codegen.Programs.PostMergeInvariantsAtBlockHash
import EvmAsm.Codegen.Programs.BlockRootsAtBlockHash
import EvmAsm.Codegen.Programs.NumberTimestampPairAtBlockHash
import EvmAsm.Codegen.Programs.GasPairAtBlockHash
import EvmAsm.Codegen.Programs.RegistryTail
import EvmAsm.Codegen.Programs.RegistryNamesTail
import EvmAsm.Codegen.Programs.CryptoRegistry

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
    -- Keep the existing BSS extent unchanged; the recursive decoder frame lives
    -- in its dedicated fixed NOBITS section, not in `STORAGE_READS_AREA`.
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

/-! ## registry -/

/-- Look up a program by name. Returns `none` for unknown names so the CLI
    can produce a clean error. -/
def lookupProgram : String → Option BuildUnit
  | "smoke"                     => some smokeUnit
  | "evm_add"                   => some evmAddUnit
  | "evm_div_v5"                => some evmDivV5Unit
  | "evm_div_v5_from_input"     => some evmDivV5FromInputUnit
  | "evm_div_v6"                => some evmDivV6Unit
  | "evm_div_v6_from_input"     => some evmDivV6FromInputUnit
  | "evm_mod_v5"                => some evmModV5Unit
  | "evm_mod_v5_from_input"     => some evmModV5FromInputUnit
  | "evm_sdiv_v5"               => some evmSdivV5Unit
  | "evm_sdiv_v5_from_input"    => some evmSdivV5FromInputUnit
  | "evm_smod_v5"               => some evmSmodV5Unit
  | "evm_smod_v5_from_input"    => some evmSmodV5FromInputUnit
  | "input_echo"                => some inputEchoUnit
  | "evm_exp_from_input"        => some evmExpFromInputUnit
  | "evm_add_from_input"        => some evmAddFromInputUnit
  | "tiny_interp_add"           => some tinyInterpAddUnit
  | "tiny_interp_add2"          => some tinyInterpAdd2Unit
  | "tiny_interp_dispatch_add"  => some tinyInterpDispatchAddUnit
  | "tiny_interp_dispatch_add2" => some tinyInterpDispatchAdd2Unit
  | "runtime_dispatcher"        => some runtimeDispatcherUnit
  | "runtime_dispatcher_call_probe" => some runtimeDispatcherCallProbeUnit

  | "zisk_runtime_access_list_seeded_sload" => some ziskRuntimeAccessListSeededSloadProbeUnit
  | "stateless_guest"           => some statelessGuestUnit
  | "account_write_touch_e2e"   => some accountWriteTouchE2eProbeUnit
  | "zisk_keccak_probe"         => some ziskKeccakProbeUnit

  | "runtime_account_witness_extcodehash" => some runtimeAccountWitnessExtcodehashProbeUnit
  | "runtime_account_witness_extcodecopy" => some runtimeAccountWitnessExtcodecopyProbeUnit
  | "runtime_create_initcode_frame" => some runtimeCreateInitcodeFrameProbeUnit
  | "runtime_create_initcode_execute" => some runtimeCreateInitcodeExecuteProbeUnit
  | "runtime_selfdestruct_account_inputs" => some runtimeSelfdestructAccountInputsProbeUnit
  | "runtime_selfdestruct_eip7708_logs" => some runtimeSelfdestructEip7708LogsProbeUnit

  | "zisk_step2_verdict"         => some ziskStep2VerdictProbeUnit
  | "zisk_stateless_verdict"    => some ziskStatelessVerdictProbeUnit
  | "zisk_stateless_verdict_v2" => some ziskStatelessVerdictV2ProbeUnit

  | s                           =>
      match lookupCryptoProgram s with
      | some unit => some unit
      | none => lookupProgramTail s
end EvmAsm.Codegen
