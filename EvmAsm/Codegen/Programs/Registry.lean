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
import EvmAsm.Codegen.Programs.PrecompileBackendProbes
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
import EvmAsm.Codegen.Probes.AuthChainIdEncodingProbe
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
import EvmAsm.Codegen.Programs.BalAccountNthDescriptor
import EvmAsm.Codegen.Programs.BalAccountDescriptorArray
import EvmAsm.Codegen.Programs.BalAccountAccessDescriptors
import EvmAsm.Codegen.Programs.BalAccountRecordArray
import EvmAsm.Codegen.Programs.BalAccountAccessDescriptors
import EvmAsm.Codegen.Programs.BalStorageAccessDescriptors
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
import EvmAsm.Codegen.Programs.ChainAggregator
import EvmAsm.Codegen.Programs.ChainBasefee
import EvmAsm.Codegen.Programs.ChainBlobCount
import EvmAsm.Codegen.Programs.ChainExcessBlobGas
import EvmAsm.Codegen.Programs.ChainTimestamp
import EvmAsm.Codegen.Programs.ChainEndpoints
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
import EvmAsm.Codegen.Programs.ChainWalkOneStepBack
import EvmAsm.Codegen.Programs.ChainWalkNStepsBack
import EvmAsm.Codegen.Programs.StateRootChainWalkBack
import EvmAsm.Codegen.Programs.BlockNumberAtBlockHash
import EvmAsm.Codegen.Programs.BlockHashWindow
import EvmAsm.Codegen.Programs.StateSlotAtBlockNumber
import EvmAsm.Codegen.Programs.StateAccountAtBlockNumber
import EvmAsm.Codegen.Programs.BalanceAtBlockNumber
import EvmAsm.Codegen.Programs.NonceAtBlockNumber
import EvmAsm.Codegen.Programs.CodeHashAtBlockNumber
import EvmAsm.Codegen.Programs.StorageRootAtBlockNumber
import EvmAsm.Codegen.Programs.AccountExistsAtBlockNumber
import EvmAsm.Codegen.Programs.HasCodeOrNonceAtBlockNumber
import EvmAsm.Codegen.Programs.AccountIsEmptyAtBlockNumber
import EvmAsm.Codegen.Programs.ExtcodesizeAtBlockNumber
import EvmAsm.Codegen.Programs.ExtcodehashAtBlockNumber
import EvmAsm.Codegen.Programs.ExtcodecopyAtBlockNumber
import EvmAsm.Codegen.Programs.SloadAtBlockNumber
import EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockNumber
import EvmAsm.Codegen.Programs.TransactionsRootAtBlockNumber
import EvmAsm.Codegen.Programs.TimestampAtBlockNumber
import EvmAsm.Codegen.Programs.GasLimitAtBlockNumber
import EvmAsm.Codegen.Programs.GasUsedAtBlockNumber
import EvmAsm.Codegen.Programs.ReceiptsRootAtBlockNumber
import EvmAsm.Codegen.Programs.OmmersHashAtBlockNumber
import EvmAsm.Codegen.Programs.ParentBeaconBlockRootAtBlockNumber
import EvmAsm.Codegen.Programs.BeneficiaryAtBlockNumber
import EvmAsm.Codegen.Programs.WithdrawalsRootAtBlockNumber
import EvmAsm.Codegen.Programs.DifficultyAtBlockNumber
import EvmAsm.Codegen.Programs.PrevRandaoAtBlockNumber
import EvmAsm.Codegen.Programs.ExcessBlobGasAtBlockNumber
import EvmAsm.Codegen.Programs.BlobGasUsedAtBlockNumber
import EvmAsm.Codegen.Programs.ExtraDataAtBlockNumber
import EvmAsm.Codegen.Programs.ParentHashAtBlockNumber
import EvmAsm.Codegen.Programs.HeaderNonceAtBlockNumber
import EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockNumber
import EvmAsm.Codegen.Programs.BlockHashAtBlockNumber
import EvmAsm.Codegen.Programs.CodeAtBlockNumber
import EvmAsm.Codegen.Programs.BlockHashAtStateRoot
import EvmAsm.Codegen.Programs.AccountStorageWalkable
import EvmAsm.Codegen.Programs.CodeAtStateRoot
import EvmAsm.Codegen.Programs.BlockNumberAtStateRoot
import EvmAsm.Codegen.Programs.StateRootAtBlockNumber
import EvmAsm.Codegen.Programs.CodeHashAtBlockHash
import EvmAsm.Codegen.Programs.WitnessHeadersFindIndexByBlockHash
import EvmAsm.Codegen.Programs.StorageRootAtBlockHash
import EvmAsm.Codegen.Programs.StateAccountAtBlockHash
import EvmAsm.Codegen.Programs.WitnessHeadersBlockHashAtIndex
import EvmAsm.Codegen.Programs.StateSlotAtBlockHash
import EvmAsm.Codegen.Programs.BalanceAtBlockHash
import EvmAsm.Codegen.Programs.NonceAtBlockHash
import EvmAsm.Codegen.Programs.CodeAtBlockHash
import EvmAsm.Codegen.Programs.HasCodeOrNonceAtBlockHash
import EvmAsm.Codegen.Programs.LogsBloomKeccakAtBlockHash
import EvmAsm.Codegen.Programs.GasLimitAtBlockHash
import EvmAsm.Codegen.Programs.BaseFeePerGasAtBlockHash
import EvmAsm.Codegen.Programs.GasUsedAtBlockHash
import EvmAsm.Codegen.Programs.TimestampAtBlockHash
import EvmAsm.Codegen.Programs.BeneficiaryAtBlockHash
import EvmAsm.Codegen.Programs.ParentHashAtBlockHash
import EvmAsm.Codegen.Programs.AccountExistsAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodesizeAtBlockHash
import EvmAsm.Codegen.Programs.AccountIsEmptyAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodehashAtBlockHash
import EvmAsm.Codegen.Programs.SloadAtBlockHash
import EvmAsm.Codegen.Programs.ExtcodecopyAtBlockHash
import EvmAsm.Codegen.Programs.StateProof
import EvmAsm.Codegen.Programs.StateStorageProof
import EvmAsm.Codegen.Programs.StateCodeHashProof
import EvmAsm.Codegen.Programs.StorageRootInWitness
import EvmAsm.Codegen.Programs.WitnessStorageKeccakAtIndex
import EvmAsm.Codegen.Programs.StateAccountSpecDefault
import EvmAsm.Codegen.Programs.StateExtractStorageRoot
import EvmAsm.Codegen.Programs.ChainLinkExtract
import EvmAsm.Codegen.Programs.StateRootInWitness
import EvmAsm.Codegen.Programs.StateExtractBalance
import EvmAsm.Codegen.Programs.StateWalkExtractSlot
import EvmAsm.Codegen.Programs.StateExtractCodeHash
import EvmAsm.Codegen.Programs.StateExtractNonce
import EvmAsm.Codegen.Programs.WitnessHeadersStateRootAtIndex
import EvmAsm.Codegen.Programs.WitnessHeadersAllChainLinksValidate
import EvmAsm.Codegen.Programs.WitnessStorageNodeKindDistribution
import EvmAsm.Codegen.Programs.WitnessHeadersAccountAtIndex
import EvmAsm.Codegen.Programs.WitnessHeadersChainLink
import EvmAsm.Codegen.Programs.StateRootPresentInWitnessState
import EvmAsm.Codegen.Programs.WitnessHeadersSlotAtIndex
import EvmAsm.Codegen.Programs.StateStorageRootProof
import EvmAsm.Codegen.Programs.WitnessNodeKindDistribution
import EvmAsm.Codegen.Programs.StateNonceProof
import EvmAsm.Codegen.Programs.StateBalanceProof
import EvmAsm.Codegen.Programs.WitnessStateKeccakAtIndex
import EvmAsm.Codegen.Programs.ChainLinkParentKeccak
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.RuntimeAccountWitness
import EvmAsm.Codegen.Programs.EvmOpcodesStorageRoot
import EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy
import EvmAsm.Codegen.Programs.AccountFieldGetters
import EvmAsm.Codegen.Programs.WitnessValidation
import EvmAsm.Codegen.Programs.StorageProof
import EvmAsm.Codegen.Programs.Eip4788
import EvmAsm.Codegen.Programs.CodeVerify
import EvmAsm.Codegen.Programs.AccountVerify
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
import EvmAsm.Codegen.Programs.DifficultyAtBlockHash
import EvmAsm.Codegen.Programs.HeaderNonceAtBlockHash
import EvmAsm.Codegen.Programs.ExtraDataAtBlockHash
import EvmAsm.Codegen.Programs.ExcessBlobGasAtBlockHash
import EvmAsm.Codegen.Programs.BlobGasUsedAtBlockHash
import EvmAsm.Codegen.Programs.BlobGasPairAtBlockHash
import EvmAsm.Codegen.Programs.PostMergeInvariantsAtBlockHash
import EvmAsm.Codegen.Programs.BlockRootsAtBlockHash
import EvmAsm.Codegen.Programs.NumberTimestampPairAtBlockHash
import EvmAsm.Codegen.Programs.GasPairAtBlockHash
import EvmAsm.Codegen.Programs.StatelessGuest
import EvmAsm.Codegen.Programs.RegistryTail
import EvmAsm.Codegen.Programs.RegistryMain
import EvmAsm.Codegen.Programs.Imports
import EvmAsm.Codegen.Programs.RegistryNamesTail
import EvmAsm.Codegen.Programs.CryptoRegistry

namespace EvmAsm.Codegen

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
