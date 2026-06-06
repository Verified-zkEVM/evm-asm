/- EvmAsm.Codegen.Programs.RegistryMain
  Front half of the codegen program registry, split from `Programs.lean`.
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
-- EXP wrapper is parametric over caller-saved registers (x6, x16) that mul_callable clobbers; deferred until upstream lands a
-- fully callee-saved variant. import re-added when wiring lands.
-- import EvmAsm.Evm64.Exp.Program
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
import EvmAsm.Codegen.Programs.FileSizeGuard
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.SSZ.HashTreeRoot.Program
import EvmAsm.Codegen.Programs.Evm
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmAccountWitness
import EvmAsm.Codegen.Programs.EIP7708Logs
import EvmAsm.Codegen.Programs.EvmBalance
import EvmAsm.Codegen.Programs.EvmExtcodecopy
import EvmAsm.Codegen.Programs.EvmArithUnits
import EvmAsm.Codegen.Programs.EvmDispatchUnits
import EvmAsm.Codegen.Programs.Clz
import EvmAsm.Codegen.Programs.ExpProperty
import EvmAsm.Codegen.Programs.CryptoRegistry
import EvmAsm.Codegen.Programs.Selfdestruct
import EvmAsm.Codegen.Programs.SelfdestructDescriptors
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.StatelessGuest
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
import EvmAsm.Codegen.Programs.SystemWrites
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
import EvmAsm.Codegen.Programs.BalAccountStateRoot
import EvmAsm.Codegen.Programs.BalAccountRecordArray
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.StorageEffectRecords
import EvmAsm.Codegen.Programs.SstoreGasRefund
import EvmAsm.Codegen.Programs.BlockAccessListHash
import EvmAsm.Codegen.Programs.BlockVerdictModeledSystem
import EvmAsm.Codegen.Programs.BlockGasRemaining
import EvmAsm.Codegen.Programs.BlockVerdictGasGate
import EvmAsm.Codegen.Programs.BlockhashRequiredHeaders
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.StorageRoot
import EvmAsm.Codegen.Programs.MptInternal
import EvmAsm.Codegen.Programs.MptNibbles
import EvmAsm.Codegen.Programs.Ssz
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxDecode
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxGasBalPostVerify
import EvmAsm.Codegen.Programs.TxGasSenderBalLookup
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.Block
import EvmAsm.Codegen.Programs.BlockBody
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
namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! Misc programs moved to submodules:
    - K21..K26 MPT helpers -> Programs/Mpt.lean
    - K34/K35/K36/K37 + K121/K120/K123 rlp/account extractors + legacy decoders -> Programs/Tx.lean
    - K64 blob_gas_used_from_versioned_hashes -> Programs/Tx.lean
    - K138/K139 signature extractors -> Programs/TxSignature.lean -/

/-! More misc programs moved to submodules — see commit history and
    the per-PR header comments inside the destination files for details. -/

/-! ## MPT branch helpers K117 / K118 — moved to `Programs/Mpt.lean` (file-size hard cap). -/

/-! ## stateless_guest body — PR-K5 keccak hash field

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
-- `statelessGuestValidatorPipeline` and `statelessGuestEpilogue`
-- live in `EvmAsm/Codegen/Programs/StatelessGuestEpilogue.lean`
-- (carved out here to satisfy the file-size hard cap; see
-- PR #5870 and PR #5900 for the established submodule pattern).

-- `statelessGuestDataSection` lives in
-- `EvmAsm/Codegen/Programs/StatelessGuestData.lean` (carved
-- out here to satisfy the file-size hard cap; see PR #5870
-- and PR #5900 for the established submodule pattern).

/-! ## registry main -/

/-- Front half of the program lookup. The caller supplies the tail lookup so
    this module can be compiled without importing `Programs.lean`. -/
def lookupProgramMain (lookupProgramTail : String → Option BuildUnit) : String → Option BuildUnit
  | "smoke"                     => some smokeUnit
  | "evm_add"                   => some evmAddUnit
  | "evm_div_v5"                => some evmDivV5Unit
  | "evm_div_v5_from_input"     => some evmDivV5FromInputUnit
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
  | "stateless_guest"           => some statelessGuestUnit
  | "zisk_headers_keccak_chain" => some ziskHeadersKeccakChainProbeUnit
  | "zisk_headers_keccak_array" => some ziskHeadersKeccakArrayProbeUnit
  | "zisk_headers_parent_hash"  => some ziskHeadersParentHashProbeUnit
  | "zisk_header_validate_parent_hash" => some ziskHeaderValidateParentHashProbeUnit
  | "zisk_header_chain_walk_step" => some ziskHeaderChainWalkStepProbeUnit
  | "zisk_account_validate_code_hash" => some ziskAccountValidateCodeHashProbeUnit
  | "zisk_account_storage_root_eq" => some ziskAccountStorageRootEqProbeUnit
  | "zisk_account_code_hash_eq" => some ziskAccountCodeHashEqProbeUnit
  | "zisk_account_nonce_eq" => some ziskAccountNonceEqProbeUnit
  | "zisk_account_is_eip161_empty" => some ziskAccountIsEip161EmptyProbeUnit
  | "zisk_account_extract_storage_root" => some ziskAccountExtractStorageRootProbeUnit
  | "zisk_account_extract_balance" => some ziskAccountExtractBalanceProbeUnit
  | "zisk_account_extract_nonce" => some ziskAccountExtractNonceProbeUnit
  | "zisk_account_extract_code_hash" => some ziskAccountExtractCodeHashProbeUnit
  | "zisk_account_is_empty"     => some ziskAccountIsEmptyProbeUnit
  | "zisk_account_has_empty_code" => some ziskAccountHasEmptyCodeProbeUnit
  | "zisk_account_storage_root_is_empty" => some ziskAccountStorageRootIsEmptyProbeUnit
  | "zisk_address_from_pubkey"  => some ziskAddressFromPubkeyProbeUnit
  | "zisk_address_compute_create2" => some ziskAddressComputeCreate2ProbeUnit
  | "zisk_address_compute_create" => some ziskAddressComputeCreateProbeUnit
  | "zisk_mpt_account_path_nibbles" => some ziskMptAccountPathNibblesProbeUnit
  | "zisk_headers_validate_chain" => some ziskHeadersValidateChainProbeUnit
  | "zisk_witness_lookup_by_hash" => some ziskWitnessLookupByHashProbeUnit
  | "zisk_rlp_list_nth_item"    => some ziskRlpListNthItemProbeUnit
  | "zisk_rlp_list_count_items" => some ziskRlpListCountItemsProbeUnit
  | "zisk_access_list_count"    => some ziskAccessListCountProbeUnit
  | "zisk_blob_gas_used_from_versioned_hashes" => some ziskBlobGasUsedFromVersionedHashesProbeUnit
  | "zisk_mpt_node_kind"        => some ziskMptNodeKindProbeUnit
  | "zisk_mpt_branch_child"     => some ziskMptBranchChildProbeUnit
  | "zisk_hp_decode_nibbles"    => some ziskHpDecodeNibblesProbeUnit
  | "zisk_mpt_walk"             => some ziskMptWalkProbeUnit
  | "zisk_mpt_set_record_walk"  => some ziskMptSetRecordWalkProbeUnit
  | "zisk_mpt_insert_walk"      => some ziskMptInsertWalkProbeUnit
  | "zisk_mpt_insert"           => some ziskMptInsertProbeUnit
  | "zisk_mpt_insert_walk_db"    => some ziskMptInsertWalkDbProbeUnit
  | "zisk_mpt_insert_acc"        => some ziskMptInsertAccProbeUnit
  | "zisk_mpt_state_root_ins"    => some ziskMptStateRootInsProbeUnit
  | "zisk_mpt_indexed_trie_root_small" => some ziskMptIndexedTrieRootSmallProbeUnit
  | "zisk_mpt_delete_walk_db"    => some ziskMptDeleteWalkDbProbeUnit
  | "zisk_mpt_delete_acc"        => some ziskMptDeleteAccProbeUnit
  | "zisk_mpt_set"              => some ziskMptSetProbeUnit
  | "zisk_mpt_set_acc"          => some ziskMptSetAccProbeUnit
  | "zisk_mpt_state_root"       => some ziskMptStateRootProbeUnit
  | "zisk_withdrawals_state_root" => some ziskWithdrawalsStateRootProbeUnit
  | "zisk_account_add_balance"  => some ziskAccountAddBalanceProbeUnit | "zisk_selfdestruct_balance_transfer" => some ziskSelfdestructBalanceTransferProbeUnit
  | "zisk_selfdestruct_delete_descriptor" => some ziskSelfdestructDeleteDescriptorProbeUnit
  | "zisk_selfdestruct_transfer_descriptors" => some ziskSelfdestructTransferDescriptorsProbeUnit
  | "zisk_account_set_uint_field" => some ziskAccountSetUintFieldProbeUnit
  | "zisk_bytes_to_nibbles"     => some ziskBytesToNibblesProbeUnit
  | "zisk_mpt_lookup_by_key"    => some ziskMptLookupByKeyProbeUnit
  | "zisk_account_decode"       => some ziskAccountDecodeProbeUnit
  | "zisk_account_at_address"   => some ziskAccountAtAddressProbeUnit
  | "zisk_state_account_inclusion_proof_verify" => some ziskStateAccountInclusionProofVerifyProbeUnit
  | "zisk_state_slot_inclusion_proof_verify" => some ziskStateSlotInclusionProofVerifyProbeUnit
  | "zisk_state_code_hash_inclusion_proof_verify" => some ziskStateCodeHashInclusionProofVerifyProbeUnit
  | "zisk_code_hash_at_block_hash_address" => some ziskCodeHashAtBlockHashAddressProbeUnit
  | "zisk_nonce_at_block_hash_address" => some ziskNonceAtBlockHashAddressProbeUnit
  | "zisk_code_at_block_hash_address" => some ziskCodeAtBlockHashAddressProbeUnit
  | "zisk_extcodesize_at_block_hash_address" => some ziskExtcodesizeAtBlockHashAddressProbeUnit
  | "zisk_chain_walk_one_step_back_from_block_hash" => some ziskChainWalkOneStepBackFromBlockHashProbeUnit
  | "zisk_chain_walk_n_steps_back_from_block_hash" => some ziskChainWalkNStepsBackFromBlockHashProbeUnit
  | "zisk_state_root_chain_walk_back_n_steps_from_block_hash" => some ziskStateRootChainWalkBackNStepsFromBlockHashProbeUnit
  | "zisk_block_number_at_block_hash" => some ziskBlockNumberAtBlockHashProbeUnit
  | "zisk_has_code_or_nonce_at_block_hash_address" => some ziskHasCodeOrNonceAtBlockHashAddressProbeUnit
  | "zisk_logs_bloom_keccak_at_block_hash" => some ziskLogsBloomKeccakAtBlockHashProbeUnit
  | "zisk_gas_limit_at_block_hash" => some ziskGasLimitAtBlockHashProbeUnit
  | "zisk_base_fee_per_gas_at_block_hash" => some ziskBaseFeePerGasAtBlockHashProbeUnit
  | "zisk_gas_used_at_block_hash" => some ziskGasUsedAtBlockHashProbeUnit
  | "zisk_timestamp_at_block_hash" => some ziskTimestampAtBlockHashProbeUnit
  | "zisk_beneficiary_at_block_hash" => some ziskBeneficiaryAtBlockHashProbeUnit
  | "zisk_parent_hash_at_block_hash" => some ziskParentHashAtBlockHashProbeUnit
  | "zisk_extcodehash_at_block_hash_address" => some ziskExtcodehashAtBlockHashAddressProbeUnit
  | "zisk_extcodecopy_at_block_hash_address" => some ziskExtcodecopyAtBlockHashAddressProbeUnit
  | "zisk_state_slot_at_block_number_address" => some ziskStateSlotAtBlockNumberAddressProbeUnit
  | "zisk_state_account_at_block_number_address" => some ziskStateAccountAtBlockNumberAddressProbeUnit
  | "zisk_balance_at_block_number_address" => some ziskBalanceAtBlockNumberAddressProbeUnit
  | "zisk_nonce_at_block_number_address" => some ziskNonceAtBlockNumberAddressProbeUnit
  | "zisk_code_hash_at_block_number_address" => some ziskCodeHashAtBlockNumberAddressProbeUnit
  | "zisk_storage_root_at_block_number_address" => some ziskStorageRootAtBlockNumberAddressProbeUnit
  | "zisk_account_exists_at_block_number_address" => some ziskAccountExistsAtBlockNumberAddressProbeUnit
  | "zisk_has_code_or_nonce_at_block_number_address" => some ziskHasCodeOrNonceAtBlockNumberAddressProbeUnit
  | "zisk_account_is_empty_at_block_number_address" => some ziskAccountIsEmptyAtBlockNumberAddressProbeUnit
  | "zisk_extcodesize_at_block_number_address" => some ziskExtcodesizeAtBlockNumberAddressProbeUnit
  | "zisk_extcodehash_at_block_number_address" => some ziskExtcodehashAtBlockNumberAddressProbeUnit
  | "zisk_extcodecopy_at_block_number_address" => some ziskExtcodecopyAtBlockNumberAddressProbeUnit
  | "zisk_sload_at_block_number_address" => some ziskSloadAtBlockNumberAddressProbeUnit
  | "zisk_logs_bloom_keccak_at_block_number" => some ziskLogsBloomKeccakAtBlockNumberProbeUnit
  | "zisk_transactions_root_at_block_number" => some ziskTransactionsRootAtBlockNumberProbeUnit
  | "zisk_timestamp_at_block_number" => some ziskTimestampAtBlockNumberProbeUnit
  | "zisk_gas_limit_at_block_number" => some ziskGasLimitAtBlockNumberProbeUnit
  | "zisk_gas_used_at_block_number" => some ziskGasUsedAtBlockNumberProbeUnit
  | "zisk_receipts_root_at_block_number" => some ziskReceiptsRootAtBlockNumberProbeUnit
  | "zisk_ommers_hash_at_block_number" => some ziskOmmersHashAtBlockNumberProbeUnit
  | "zisk_parent_beacon_block_root_at_block_number" => some ziskParentBeaconBlockRootAtBlockNumberProbeUnit
  | "zisk_beneficiary_at_block_number" => some ziskBeneficiaryAtBlockNumberProbeUnit
  | "zisk_withdrawals_root_at_block_number" => some ziskWithdrawalsRootAtBlockNumberProbeUnit
  | "zisk_difficulty_at_block_number" => some ziskDifficultyAtBlockNumberProbeUnit
  | "zisk_prev_randao_at_block_number" => some ziskPrevRandaoAtBlockNumberProbeUnit
  | "zisk_excess_blob_gas_at_block_number" => some ziskExcessBlobGasAtBlockNumberProbeUnit
  | "zisk_blob_gas_used_at_block_number" => some ziskBlobGasUsedAtBlockNumberProbeUnit
  | "zisk_extra_data_at_block_number" => some ziskExtraDataAtBlockNumberProbeUnit
  | "zisk_parent_hash_at_block_number" => some ziskParentHashAtBlockNumberProbeUnit
  | "zisk_header_nonce_at_block_number" => some ziskHeaderNonceAtBlockNumberProbeUnit
  | "zisk_base_fee_per_gas_at_block_number" => some ziskBaseFeePerGasAtBlockNumberProbeUnit
  | "zisk_block_hash_at_block_number" => some ziskBlockHashAtBlockNumberProbeUnit
  | "zisk_code_at_block_number_address" => some ziskCodeAtBlockNumberAddressProbeUnit
  | "zisk_block_hash_at_state_root" => some ziskBlockHashAtStateRootProbeUnit
  | "zisk_account_storage_walkable_at_state_root" => some ziskAccountStorageWalkableAtStateRootProbeUnit
  | "zisk_code_at_state_root_address" => some ziskCodeAtStateRootAddressProbeUnit
  | "zisk_block_number_at_state_root" => some ziskBlockNumberAtStateRootProbeUnit
  | "zisk_state_root_at_block_number" => some ziskStateRootAtBlockNumberProbeUnit
  | "zisk_account_exists_at_block_hash_address" => some ziskAccountExistsAtBlockHashAddressProbeUnit
  | "zisk_account_is_empty_at_block_hash_address" => some ziskAccountIsEmptyAtBlockHashAddressProbeUnit
  | "zisk_sload_at_block_hash_address" => some ziskSloadAtBlockHashAddressProbeUnit
  | "zisk_storage_root_present_in_witness_storage" => some ziskStorageRootPresentInWitnessStorageProbeUnit
  | "zisk_witness_storage_keccak_at_index" => some ziskWitnessStorageKeccakAtIndexProbeUnit
  | "zisk_witness_lookup_by_hash_indexed" => some ziskWitnessLookupByHashIndexedProbeUnit
  | "zisk_witness_codes_keccak_at_index" => some ziskWitnessCodesKeccakAtIndexProbeUnit
  | "zisk_state_account_with_spec_default" => some ziskStateAccountWithSpecDefaultProbeUnit
  | "zisk_state_extract_storage_root_for_address" => some ziskStateExtractStorageRootForAddressProbeUnit
  | "zisk_chain_link_verify_and_extract_parent_state_root" => some ziskChainLinkVerifyAndExtractParentStateRootProbeUnit
  | "zisk_parent_state_root_present_in_witness_state" => some ziskParentStateRootPresentInWitnessStateProbeUnit
  | "zisk_state_extract_balance_for_address" => some ziskStateExtractBalanceForAddressProbeUnit
  | "zisk_state_walk_extract_slot_value" => some ziskStateWalkExtractSlotValueProbeUnit
  | "zisk_state_extract_code_hash_for_address" => some ziskStateExtractCodeHashForAddressProbeUnit
  | "zisk_state_extract_nonce_for_address" => some ziskStateExtractNonceForAddressProbeUnit
  | "zisk_witness_headers_state_root_at_index" => some ziskWitnessHeadersStateRootAtIndexProbeUnit
  | "zisk_witness_headers_all_chain_links_validate" => some ziskWitnessHeadersAllChainLinksValidateProbeUnit
  | "zisk_witness_storage_node_kind_distribution" => some ziskWitnessStorageNodeKindDistributionProbeUnit
  | "zisk_witness_headers_account_at_index_address" => some ziskWitnessHeadersAccountAtIndexAddressProbeUnit
  | "zisk_witness_headers_chain_link_at_index" => some ziskWitnessHeadersChainLinkAtIndexProbeUnit
  | "zisk_state_root_present_in_witness_state" => some ziskStateRootPresentInWitnessStateProbeUnit
  | "zisk_witness_headers_slot_at_index_address" => some ziskWitnessHeadersSlotAtIndexAddressProbeUnit
  | "zisk_witness_headers_find_index_by_block_hash" => some ziskWitnessHeadersFindIndexByBlockHashProbeUnit
  | "zisk_storage_root_at_block_hash_address" => some ziskStorageRootAtBlockHashAddressProbeUnit
  | "zisk_state_account_at_block_hash_address" => some ziskStateAccountAtBlockHashAddressProbeUnit
  | "zisk_witness_headers_block_hash_at_index" => some ziskWitnessHeadersBlockHashAtIndexProbeUnit
  | "zisk_state_slot_at_block_hash_address" => some ziskStateSlotAtBlockHashAddressProbeUnit
  | "zisk_state_storage_root_inclusion_proof_verify" => some ziskStateStorageRootInclusionProofVerifyProbeUnit
  | "zisk_witness_state_node_kind_distribution" => some ziskWitnessStateNodeKindDistributionProbeUnit
  | "zisk_state_nonce_inclusion_proof_verify" => some ziskStateNonceInclusionProofVerifyProbeUnit
  | "zisk_state_balance_inclusion_proof_verify" => some ziskStateBalanceInclusionProofVerifyProbeUnit
  | "zisk_witness_state_keccak_at_index" => some ziskWitnessStateKeccakAtIndexProbeUnit
  | "zisk_parent_keccak_matches_child_parent_hash" => some ziskParentKeccakMatchesChildParentHashProbeUnit
  | "zisk_balance_at_block_hash_address" => some ziskBalanceAtBlockHashAddressProbeUnit
  | "zisk_ommers_hash_at_block_hash" => some ziskOmmersHashAtBlockHashProbeUnit
  | "zisk_parent_beacon_block_root_at_block_hash" => some ziskParentBeaconBlockRootAtBlockHashProbeUnit
  | "zisk_transactions_root_at_block_hash" => some ziskTransactionsRootAtBlockHashProbeUnit
  | "zisk_receipts_root_at_block_hash" => some ziskReceiptsRootAtBlockHashProbeUnit
  | "zisk_withdrawals_root_at_block_hash" => some ziskWithdrawalsRootAtBlockHashProbeUnit
  | "zisk_prev_randao_at_block_hash" => some ziskPrevRandaoAtBlockHashProbeUnit
  | "zisk_difficulty_at_block_hash" => some ziskDifficultyAtBlockHashProbeUnit
  | "zisk_slot_at_index"        => some ziskSlotAtIndexProbeUnit
  | "zisk_rlp_encode_uint_be"   => some ziskRlpEncodeUintBeProbeUnit
  | "zisk_rlp_encode_bytes"     => some ziskRlpEncodeBytesProbeUnit
  | "zisk_rlp_item_span"        => some ziskRlpItemSpanProbeUnit
  | "zisk_rlp_encode_list_prefix" => some ziskRlpEncodeListPrefixProbeUnit
  | "zisk_withdrawal_rlp_encode" => some ziskWithdrawalRlpEncodeProbeUnit
  | "zisk_withdrawal_to_path_delta" => some ziskWithdrawalToPathDeltaProbeUnit
  | "zisk_ssz_withdrawal_to_rlp" => some ziskSszWithdrawalToRlpProbeUnit
  | "zisk_extract_witness_state_section" => some ziskExtractWitnessStateSectionProbeUnit
  | "zisk_extract_payload_and_withdrawals" => some ziskExtractPayloadAndWithdrawalsProbeUnit
  | "zisk_extract_parent_header_and_state_root" => some ziskExtractParentHeaderProbeUnit
  | "zisk_withdrawal_compute_hash" => some ziskWithdrawalComputeHashProbeUnit
  | "zisk_account_encode"       => some ziskAccountEncodeProbeUnit
  | "zisk_hp_encode_nibbles"    => some ziskHpEncodeNibblesProbeUnit
  | "zisk_state_root_single_account" => some ziskStateRootSingleAccountProbeUnit
  | "zisk_storage_root_recompute_single_slot" => some ziskStorageRootRecomputeSingleSlotProbeUnit
  | "zisk_validate_witness_state_contains_root" => some ziskValidateWitnessStateContainsRootProbeUnit
  | "zisk_witness_state_validate_node_kinds" => some ziskWitnessStateValidateNodeKindsProbeUnit
  | "zisk_witness_codes_validate_lengths" => some ziskWitnessCodesValidateLengthsProbeUnit
  | "zisk_witness_storage_validate_node_kinds" => some ziskWitnessStorageValidateNodeKindsProbeUnit
  | "zisk_account_at_header_state_root" => some ziskAccountAtHeaderStateRootProbeUnit
  | "zisk_verify_account_struct_matches" => some ziskVerifyAccountStructMatchesProbeUnit
  | "zisk_slot_at_header_state_root" => some ziskSlotAtHeaderStateRootProbeUnit
  | "zisk_verify_slot_value_matches" => some ziskVerifySlotValueMatchesProbeUnit
  | "zisk_storage_slot_inclusion_proof_verify" => some ziskStorageSlotInclusionProofVerifyProbeUnit
  | "zisk_code_at_header_state_root" => some ziskCodeAtHeaderStateRootProbeUnit
  | "zisk_verify_code_hash_matches" => some ziskVerifyCodeHashMatchesProbeUnit
  | "zisk_extcodesize_at_header_state_root" => some ziskExtcodesizeAtHeaderStateRootProbeUnit
  | "zisk_extcodehash_at_header_state_root" => some ziskExtcodehashAtHeaderStateRootProbeUnit
  | "runtime_account_witness_extcodehash" => some runtimeAccountWitnessExtcodehashProbeUnit
  | "runtime_account_witness_extcodecopy" => some runtimeAccountWitnessExtcodecopyProbeUnit
  | "zisk_balance_at_header_state_root" => some ziskBalanceAtHeaderStateRootProbeUnit
  | "zisk_nonce_at_header_state_root" => some ziskNonceAtHeaderStateRootProbeUnit
  | "zisk_storage_root_at_header_state_root" => some ziskStorageRootAtHeaderStateRootProbeUnit
  | "zisk_code_hash_at_header_state_root" => some ziskCodeHashAtHeaderStateRootProbeUnit
  | "zisk_sload_at_header_state_root" => some ziskSloadAtHeaderStateRootProbeUnit
  | "zisk_extcodecopy_at_header_state_root" => some ziskExtcodecopyAtHeaderStateRootProbeUnit
  | "zisk_account_exists_at_header_state_root" => some ziskAccountExistsAtHeaderStateRootProbeUnit
  | "zisk_account_is_empty_at_header_state_root" => some ziskAccountIsEmptyAtHeaderStateRootProbeUnit
  | "zisk_validate_storage_root_in_witness_storage" => some ziskValidateStorageRootInWitnessStorageProbeUnit
  | "zisk_has_code_or_nonce_at_header_state_root" => some ziskHasCodeOrNonceAtHeaderStateRootProbeUnit
  | "zisk_rlp_field_to_u64"     => some ziskRlpFieldToU64ProbeUnit
  | "zisk_rlp_field_to_u256_be" => some ziskRlpFieldToU256BeProbeUnit
  | "zisk_tx_legacy_decode"     => some ziskTxLegacyDecodeProbeUnit
  | "zisk_tx_eip1559_decode"    => some ziskTxEip1559DecodeProbeUnit
  | "zisk_derive_chain_id_from_v" => some ziskDeriveChainIdFromVProbeUnit
  | "zisk_tx_legacy_extract_signature" => some ziskTxLegacyExtractSignatureProbeUnit
  | "zisk_tx_eip1559_extract_signature" => some ziskTxEip1559ExtractSignatureProbeUnit
  | "zisk_tx_eip2930_extract_signature" => some ziskTxEip2930ExtractSignatureProbeUnit
  | "zisk_tx_eip4844_extract_signature" => some ziskTxEip4844ExtractSignatureProbeUnit
  | "zisk_tx_eip7702_extract_signature" => some ziskTxEip7702ExtractSignatureProbeUnit
  | "zisk_eip7702_authorization_extract_signature" => some ziskEip7702AuthorizationExtractSignatureProbeUnit
  | "zisk_rlp_list_truncate_to_n_fields" => some ziskRlpListTruncateToNFieldsProbeUnit
  | "zisk_tx_signing_hash" => some ziskTxSigningHashProbeUnit
  | "zisk_tx_signing_hash_legacy_eip155" => some ziskTxSigningHashLegacyEip155ProbeUnit
  | "zisk_eip7702_authorization_signing_hash" => some ziskEip7702AuthorizationSigningHashProbeUnit
  | "zisk_header_minimal_decode" => some ziskHeaderMinimalDecodeProbeUnit
  | "zisk_header_extended_decode" => some ziskHeaderExtendedDecodeProbeUnit
  | "zisk_coinbase_extract_from_header" => some ziskCoinbaseExtractFromHeaderProbeUnit
  | "zisk_header_extract_blob_gas_pair" => some ziskHeaderExtractBlobGasPairProbeUnit
  | "zisk_block_validate_blob_gas_max_cap" => some ziskBlockValidateBlobGasMaxCapProbeUnit
  | "zisk_header_extract_block_roots" => some ziskHeaderExtractBlockRootsProbeUnit
  | "zisk_validate_header_basic" => some ziskValidateHeaderBasicProbeUnit
  | "zisk_check_gas_limit"      => some ziskCheckGasLimitProbeUnit
  | "zisk_tx_validate_against_block" => some ziskTxValidateAgainstBlockProbeUnit
  | "zisk_calc_excess_blob_gas" => some ziskCalcExcessBlobGasProbeUnit
  | "zisk_header_validate_post_merge" => some ziskHeaderValidatePostMergeProbeUnit
  | "zisk_header_validate_extra_data_length" => some ziskHeaderValidateExtraDataLengthProbeUnit
  | "zisk_u256_add_be"          => some ziskU256AddBeProbeUnit
  | "zisk_u256_lt_be"           => some ziskU256LtBeProbeUnit
  | "zisk_u256_sub_be"          => some ziskU256SubBeProbeUnit
  | "zisk_u256_eq"              => some ziskU256EqProbeUnit
  | "zisk_u256_mul_u64_be"      => some ziskU256MulU64BeProbeUnit | "zisk_account_charge_gas_pre_exec" => some ziskAccountChargeGasPreExecProbeUnit
  | "zisk_tx_upfront_precharge" => some ziskTxUpfrontPrechargeProbeUnit
  | "zisk_account_refund_gas_post_exec" => some ziskAccountRefundGasPostExecProbeUnit | "zisk_tx_post_exec_gas_settlement" => some ziskTxPostExecGasSettlementProbeUnit
  | "zisk_eip1559_calc_base_fee_per_gas" => some ziskEip1559CalcBaseFeePerGasProbeUnit
  | "zisk_header_validate_base_fee" => some ziskHeaderValidateBaseFeeProbeUnit
  | "zisk_validate_header_full" => some ziskValidateHeaderFullProbeUnit
  | "zisk_validate_header_rlp_pair" => some ziskValidateHeaderRlpPairProbeUnit
  | "zisk_block_header_ssz_to_rlp" => some ziskBlockHeaderSszToRlpProbeUnit
  | "zisk_step2_verdict"         => some ziskStep2VerdictProbeUnit
  | "zisk_stateless_verdict"    => some ziskStatelessVerdictProbeUnit
  | "zisk_stateless_verdict_v2" => some ziskStatelessVerdictV2ProbeUnit
  | "zisk_u256_from_u64_be"     => some ziskU256FromU64BeProbeUnit
  | "zisk_u256_to_u64_be"       => some ziskU256ToU64BeProbeUnit
  | "zisk_u256_is_zero"         => some ziskU256IsZeroProbeUnit
  | "zisk_u256_min"             => some ziskU256MinProbeUnit
  | "zisk_u256_max"             => some ziskU256MaxProbeUnit
  | "zisk_u256_div_u64_be"      => some ziskU256DivU64BeProbeUnit
  | "zisk_runtime_access_account_gas" => some ziskRuntimeAccessAccountGasProbeUnit
  | "zisk_runtime_access_seed_initial" => some ziskRuntimeAccessSeedInitialProbeUnit
  | "zisk_priority_fee_per_gas_eip1559" => some ziskPriorityFeePerGasEip1559ProbeUnit
  | "zisk_effective_gas_price_eip1559" => some ziskEffectiveGasPriceEip1559ProbeUnit
  | "zisk_tx_cost_compute"      => some ziskTxCostComputeProbeUnit
  | "zisk_validate_transaction_balance" => some ziskValidateTransactionBalanceProbeUnit
  | "zisk_tx_type_dispatch"     => some ziskTxTypeDispatchProbeUnit
  | "zisk_tx_extract_nonce_and_gas" => some ziskTxExtractNonceAndGasProbeUnit
  | "zisk_tx_extract_to_address" => some ziskTxExtractToAddressProbeUnit
  | "zisk_tx_extract_value"     => some ziskTxExtractValueProbeUnit
  | "zisk_tx_extract_data_section" => some ziskTxExtractDataSectionProbeUnit
  | "zisk_tx_extract_gas_pricing"  => some ziskTxExtractGasPricingProbeUnit
  | "zisk_tx_effective_gas_pricing" => some ziskTxEffectiveGasPricingProbeUnit
  | "zisk_tx_eip2930_decode"    => some ziskTxEip2930DecodeProbeUnit
  | "zisk_tx_eip7702_decode"    => some ziskTxEip7702DecodeProbeUnit
  | "zisk_tx_eip4844_decode"    => some ziskTxEip4844DecodeProbeUnit
  | "zisk_tx_eip4844_compute_blob_gas" => some ziskTxEip4844ComputeBlobGasProbeUnit
  | "zisk_tx_calculate_total_blob_gas" => some ziskTxCalculateTotalBlobGasProbeUnit
  | "zisk_block_body_blob_gas_total" => some ziskBlockBodyBlobGasTotalProbeUnit
  | "zisk_block_validate_blob_gas_consistency" => some ziskBlockValidateBlobGasConsistencyProbeUnit
  | "zisk_tx_decode_dispatch"   => some ziskTxDecodeDispatchProbeUnit
  | "zisk_intrinsic_gas_legacy" => some ziskIntrinsicGasLegacyProbeUnit
  | "zisk_tx_validate_intrinsic_gas_legacy" => some ziskTxValidateIntrinsicGasLegacyProbeUnit
  | "zisk_validate_transaction_basic" => some ziskValidateTransactionBasicProbeUnit
  | "zisk_validate_transaction_full" => some ziskValidateTransactionFullProbeUnit
  | "zisk_withdrawal_decode"    => some ziskWithdrawalDecodeProbeUnit
  | "zisk_block_body_decode"    => some ziskBlockBodyDecodeProbeUnit
  | "zisk_block_validate_ommers_empty" => some ziskBlockValidateOmmersEmptyProbeUnit
  | "zisk_process_withdrawal"   => some ziskProcessWithdrawalProbeUnit
  | "zisk_process_withdrawals_block" => some ziskProcessWithdrawalsBlockProbeUnit
  | "zisk_withdrawals_sum_amounts" => some ziskWithdrawalsSumAmountsProbeUnit
  | "zisk_block_withdrawals_total" => some ziskBlockWithdrawalsTotalProbeUnit
  | "zisk_block_count_withdrawals" => some ziskBlockCountWithdrawalsProbeUnit
  | "zisk_block_count_transactions" => some ziskBlockCountTransactionsProbeUnit
  | "zisk_block_summary"        => some ziskBlockSummaryProbeUnit
  | "zisk_block_compute_tx_hashes" => some ziskBlockComputeTxHashesProbeUnit
  | "zisk_bloom_add_value" => some ziskBloomAddValueProbeUnit
  | "zisk_log_bloom_add" => some ziskLogBloomAddProbeUnit
  | "zisk_logs_list_bloom_add" => some ziskLogsListBloomAddProbeUnit
  | "zisk_captured_logs_bloom_add" => some ziskCapturedLogsBloomAddProbeUnit
  | "zisk_eip7708_synthetic_logs" => some ziskEip7708SyntheticLogsProbeUnit
  | "zisk_bloom_or_into" => some ziskBloomOrIntoProbeUnit
  | "zisk_receipt_extract_logs_bloom" => some ziskReceiptExtractLogsBloomProbeUnit
  | "zisk_header_extract_logs_bloom" => some ziskHeaderExtractLogsBloomProbeUnit
  | s                           =>
      match lookupCryptoProgram s with
      | some unit => some unit
      | none => lookupProgramTail s
