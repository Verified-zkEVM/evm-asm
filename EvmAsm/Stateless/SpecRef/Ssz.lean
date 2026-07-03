/-
  EvmAsm.Stateless.SpecRef.Ssz

  Port of `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`@tests-zkevm@v0.4.0`): the SSZ container schemas mirroring the domain
  dataclasses, plus the 34 to/from-SSZ conversion functions.

  Each Python `class SszX(Container)` becomes an `SszType` descriptor
  (`sszXType`); each `_x_to_ssz` becomes `xToSsz : … → SszValue`; each
  `_ssz_to_x` becomes `sszToX : SszValue → Except SpecError …`. The generic
  `encode_bytes` / `decode_bytes` / `hash_tree_root` live in `SszCodec.lean`.

  Field ORDER in every `SszType.container`/`SszValue.container` matches the
  Python class field order exactly (SSZ is order-sensitive), so the
  positional `getField` accessors in the `sszToX` direction line up with
  the class attributes.
-/

import EvmAsm.Stateless.SpecRef.SszCodec

namespace EvmAsm.Stateless.SpecRef

/-! ## SSZ max-length constants (`stateless_ssz.py:41`–`61`) -/

def MAX_EXTRA_DATA_BYTES : Nat := 32
def MAX_BYTES_PER_TRANSACTION : Nat := 2 ^ 30
def MAX_TRANSACTIONS_PER_PAYLOAD : Nat := 2 ^ 20
def MAX_WITHDRAWALS_PER_PAYLOAD : Nat := 2 ^ 4
def MAX_BLOB_COMMITMENTS_PER_BLOCK : Nat := 4096
def MAX_DEPOSIT_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 13
def MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 4
def MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD : Nat := 2 ^ 1
def MAX_BLOCK_ACCESS_LIST_BYTES : Nat := 2 ^ 24
def MAX_WITNESS_NODES : Nat := 2 ^ 20
def MAX_WITNESS_CODES : Nat := 2 ^ 16
def MAX_WITNESS_HEADERS : Nat := 256
def MAX_BYTES_PER_WITNESS_NODE : Nat := 2 ^ 20
def MAX_BYTES_PER_CODE : Nat := 2 ^ 24
def MAX_BYTES_PER_HEADER : Nat := 2 ^ 10
def MAX_OPTIONAL_FORK_ACTIVATION_VALUES : Nat := 1
def MAX_BLOB_SCHEDULES_PER_FORK : Nat := 1
def MAX_PUBLIC_KEYS : Nat := 2 ^ 20
def PUBLIC_KEY_BYTES : Nat := 65

/-- `STATELESS_INPUT_SCHEMA_ID` (`stateless_ssz.py:64`). -/
def STATELESS_INPUT_SCHEMA_ID : Nat := 0x0001
/-- `STATELESS_INPUT_SCHEMA_ID_SIZE` (`stateless_ssz.py:65`). -/
def STATELESS_INPUT_SCHEMA_ID_SIZE : Nat := 2

/-! ## SSZ type descriptors (mirror the `Container` classes) -/

/-- `Bytes32` / `ByteVector[32]`. -/
def bytes32Type : SszType := .byteVector 32
/-- `uint64`. -/
def u64Type : SszType := .uint 8
/-- `uint256`. -/
def u256Type : SszType := .uint 32

/-- `SszWithdrawal` (`stateless_ssz.py:80`). -/
def sszWithdrawalType : SszType :=
  .container [u64Type, u64Type, .byteVector 20, u64Type]

/-- `SszExecutionPayload` (`stateless_ssz.py:89`). -/
def sszExecutionPayloadType : SszType :=
  .container [bytes32Type, .byteVector 20, bytes32Type, bytes32Type,
    .byteVector 256, bytes32Type, u64Type, u64Type, u64Type, u64Type,
    .byteList MAX_EXTRA_DATA_BYTES, u256Type, bytes32Type,
    .list (.byteList MAX_BYTES_PER_TRANSACTION) MAX_TRANSACTIONS_PER_PAYLOAD,
    .list sszWithdrawalType MAX_WITHDRAWALS_PER_PAYLOAD,
    u64Type, u64Type, .byteList MAX_BLOCK_ACCESS_LIST_BYTES, u64Type]

/-- `SszDepositRequest` (`stateless_ssz.py:115`). -/
def sszDepositRequestType : SszType :=
  .container [.byteVector 48, bytes32Type, u64Type, .byteVector 96, u64Type]

/-- `SszWithdrawalRequest` (`stateless_ssz.py:125`). -/
def sszWithdrawalRequestType : SszType :=
  .container [.byteVector 20, .byteVector 48, u64Type]

/-- `SszConsolidationRequest` (`stateless_ssz.py:133`). -/
def sszConsolidationRequestType : SszType :=
  .container [.byteVector 20, .byteVector 48, .byteVector 48]

/-- `SszExecutionRequests` (`stateless_ssz.py:141`). -/
def sszExecutionRequestsType : SszType :=
  .container [.list sszDepositRequestType MAX_DEPOSIT_REQUESTS_PER_PAYLOAD,
    .list sszWithdrawalRequestType MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD,
    .list sszConsolidationRequestType MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD]

/-- `SszNewPayloadRequest` (`stateless_ssz.py:153`). -/
def sszNewPayloadRequestType : SszType :=
  .container [sszExecutionPayloadType,
    .list bytes32Type MAX_BLOB_COMMITMENTS_PER_BLOCK,
    bytes32Type, sszExecutionRequestsType]

/-- `SszExecutionWitness` (`stateless_ssz.py:162`). -/
def sszExecutionWitnessType : SszType :=
  .container [.list (.byteList MAX_BYTES_PER_WITNESS_NODE) MAX_WITNESS_NODES,
    .list (.byteList MAX_BYTES_PER_CODE) MAX_WITNESS_CODES,
    .list (.byteList MAX_BYTES_PER_HEADER) MAX_WITNESS_HEADERS]

/-- `SszOptionalForkActivationValue = List[uint64, 1]` (`stateless_ssz.py:75`). -/
def sszOptionalForkActivationValueType : SszType :=
  .list u64Type MAX_OPTIONAL_FORK_ACTIVATION_VALUES

/-- `SszForkActivation` (`stateless_ssz.py:170`). -/
def sszForkActivationType : SszType :=
  .container [sszOptionalForkActivationValueType, sszOptionalForkActivationValueType]

/-- `SszBlobSchedule` (`stateless_ssz.py:177`). -/
def sszBlobScheduleType : SszType :=
  .container [u64Type, u64Type, u64Type]

/-- `SszOptionalBlobSchedule = List[SszBlobSchedule, 1]` (`stateless_ssz.py:185`). -/
def sszOptionalBlobScheduleType : SszType :=
  .list sszBlobScheduleType MAX_BLOB_SCHEDULES_PER_FORK

/-- `SszForkConfig` (`stateless_ssz.py:190`). -/
def sszForkConfigType : SszType :=
  .container [u64Type, sszForkActivationType, sszOptionalBlobScheduleType]

/-- `SszChainConfig` (`stateless_ssz.py:198`). -/
def sszChainConfigType : SszType :=
  .container [u64Type, sszForkConfigType]

/-- `SszStatelessInput` (`stateless_ssz.py:205`). -/
def sszStatelessInputType : SszType :=
  .container [sszNewPayloadRequestType, sszExecutionWitnessType, sszChainConfigType,
    .list (.byteVector PUBLIC_KEY_BYTES) MAX_PUBLIC_KEYS]

/-- `SszStatelessValidationResult` (`stateless_ssz.py:214`). -/
def sszStatelessValidationResultType : SszType :=
  .container [bytes32Type, .bool, sszChainConfigType]

/-! ## Accessors for the `ssz_to_*` direction -/

def asContainerV : SszValue → Except SpecError (List SszValue)
  | .container fs => .ok fs
  | _ => .error (.sszError "expected container")

def asUintV : SszValue → Except SpecError Nat
  | .uint _ v => .ok v
  | _ => .error (.sszError "expected uint")

def asBoolV : SszValue → Except SpecError Bool
  | .bool b => .ok b
  | _ => .error (.sszError "expected bool")

def asBytesV : SszValue → Except SpecError Bytes
  | .byteVector d => .ok d
  | .byteList _ d => .ok d
  | _ => .error (.sszError "expected bytes")

def asListV : SszValue → Except SpecError (List SszValue)
  | .list _ _ es => .ok es
  | _ => .error (.sszError "expected list")

def getField (fs : List SszValue) (i : Nat) : Except SpecError SszValue :=
  match fs[i]? with
  | some v => .ok v
  | none => .error (.sszError s!"missing field {i}")

/-! ## `_protocol_fork_to_ssz` / `_ssz_to_protocol_fork`
    (`stateless_ssz.py:228`, `:234`) -/

def protocolForkToSsz (fork : ProtocolFork) : SszValue :=
  .uint 8 (protocolForks.findIdx (· == fork))

def sszToProtocolFork (ssz : Nat) : Except SpecError ProtocolFork :=
  match protocolForks[ssz]? with
  | some f => .ok f
  | none => .error (.unknownProtocolFork ssz)

/-! ## `_withdrawal_to_ssz` / `_ssz_to_withdrawal` (`:242`, `:252`) -/

def withdrawalToSsz (w : Withdrawal) : SszValue :=
  .container [.uint 8 w.index, .uint 8 w.validatorIndex,
    .byteVector w.address, .uint 8 w.amount]

def sszToWithdrawal (sv : SszValue) : Except SpecError Withdrawal := do
  let fs ← asContainerV sv
  let index ← asUintV (← getField fs 0)
  let validatorIndex ← asUintV (← getField fs 1)
  let address ← asBytesV (← getField fs 2)
  let amount ← asUintV (← getField fs 3)
  pure { index, validatorIndex, address, amount }

/-! ## `_payload_to_ssz` / `_ssz_to_payload` (`:262`, `:299`) -/

def payloadToSsz (p : ExecutionPayload) : SszValue :=
  .container [.byteVector p.parentHash, .byteVector p.feeRecipient,
    .byteVector p.stateRoot, .byteVector p.receiptsRoot, .byteVector p.logsBloom,
    .byteVector p.prevRandao, .uint 8 p.blockNumber, .uint 8 p.gasLimit,
    .uint 8 p.gasUsed, .uint 8 p.timestamp,
    .byteList MAX_EXTRA_DATA_BYTES p.extraData, .uint 32 p.baseFeePerGas,
    .byteVector p.blockHash,
    .list MAX_TRANSACTIONS_PER_PAYLOAD none
      (p.transactions.map (fun t => .byteList MAX_BYTES_PER_TRANSACTION t)),
    .list MAX_WITHDRAWALS_PER_PAYLOAD none (p.withdrawals.map withdrawalToSsz),
    .uint 8 p.blobGasUsed, .uint 8 p.excessBlobGas,
    .byteList MAX_BLOCK_ACCESS_LIST_BYTES p.blockAccessList, .uint 8 p.slotNumber]

def sszToPayload (sv : SszValue) : Except SpecError ExecutionPayload := do
  let fs ← asContainerV sv
  let parentHash ← asBytesV (← getField fs 0)
  let feeRecipient ← asBytesV (← getField fs 1)
  let stateRoot ← asBytesV (← getField fs 2)
  let receiptsRoot ← asBytesV (← getField fs 3)
  let logsBloom ← asBytesV (← getField fs 4)
  let prevRandao ← asBytesV (← getField fs 5)
  let blockNumber ← asUintV (← getField fs 6)
  let gasLimit ← asUintV (← getField fs 7)
  let gasUsed ← asUintV (← getField fs 8)
  let timestamp ← asUintV (← getField fs 9)
  let extraData ← asBytesV (← getField fs 10)
  let baseFeePerGas ← asUintV (← getField fs 11)
  let blockHash ← asBytesV (← getField fs 12)
  let transactions ← (← asListV (← getField fs 13)).mapM asBytesV
  let withdrawals ← (← asListV (← getField fs 14)).mapM sszToWithdrawal
  let blobGasUsed ← asUintV (← getField fs 15)
  let excessBlobGas ← asUintV (← getField fs 16)
  let blockAccessList ← asBytesV (← getField fs 17)
  let slotNumber ← asUintV (← getField fs 18)
  let payload : ExecutionPayload :=
    { parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao,
      blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash,
      transactions, withdrawals, blobGasUsed, excessBlobGas, blockAccessList, slotNumber }
  pure payload

/-! ## Request conversions (`:326`, `:337`, `:348`, `:359`, `:370`, `:381`) -/

def depositRequestToSsz (d : DepositRequest) : SszValue :=
  .container [.byteVector d.pubkey, .byteVector d.withdrawalCredentials,
    .uint 8 d.amount, .byteVector d.signature, .uint 8 d.index]

def sszToDepositRequest (sv : SszValue) : Except SpecError DepositRequest := do
  let fs ← asContainerV sv
  let pubkey ← asBytesV (← getField fs 0)
  let withdrawalCredentials ← asBytesV (← getField fs 1)
  let amount ← asUintV (← getField fs 2)
  let signature ← asBytesV (← getField fs 3)
  let index ← asUintV (← getField fs 4)
  pure { pubkey, withdrawalCredentials, amount, signature, index }

def withdrawalRequestToSsz (w : WithdrawalRequest) : SszValue :=
  .container [.byteVector w.sourceAddress, .byteVector w.validatorPubkey, .uint 8 w.amount]

def sszToWithdrawalRequest (sv : SszValue) : Except SpecError WithdrawalRequest := do
  let fs ← asContainerV sv
  let sourceAddress ← asBytesV (← getField fs 0)
  let validatorPubkey ← asBytesV (← getField fs 1)
  let amount ← asUintV (← getField fs 2)
  pure { sourceAddress, validatorPubkey, amount }

def consolidationRequestToSsz (c : ConsolidationRequest) : SszValue :=
  .container [.byteVector c.sourceAddress, .byteVector c.sourcePubkey, .byteVector c.targetPubkey]

def sszToConsolidationRequest (sv : SszValue) : Except SpecError ConsolidationRequest := do
  let fs ← asContainerV sv
  let sourceAddress ← asBytesV (← getField fs 0)
  let sourcePubkey ← asBytesV (← getField fs 1)
  let targetPubkey ← asBytesV (← getField fs 2)
  pure { sourceAddress, sourcePubkey, targetPubkey }

/-! ## `_execution_requests_to_ssz` / `_ssz_to_execution_requests` (`:392`, `:409`) -/

def executionRequestsToSsz (er : ExecutionRequests) : SszValue :=
  .container [
    .list MAX_DEPOSIT_REQUESTS_PER_PAYLOAD none (er.deposits.map depositRequestToSsz),
    .list MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD none (er.withdrawals.map withdrawalRequestToSsz),
    .list MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD none
      (er.consolidations.map consolidationRequestToSsz)]

def sszToExecutionRequests (sv : SszValue) : Except SpecError ExecutionRequests := do
  let fs ← asContainerV sv
  let deposits ← (← asListV (← getField fs 0)).mapM sszToDepositRequest
  let withdrawals ← (← asListV (← getField fs 1)).mapM sszToWithdrawalRequest
  let consolidations ← (← asListV (← getField fs 2)).mapM sszToConsolidationRequest
  pure { deposits, withdrawals, consolidations }

/-! ## `_new_payload_request_to_ssz` / `_ssz_to_new_payload_request` (`:424`, `:438`) -/

def newPayloadRequestToSsz (npr : NewPayloadRequest) : SszValue :=
  .container [payloadToSsz npr.executionPayload,
    .list MAX_BLOB_COMMITMENTS_PER_BLOCK none
      (npr.versionedHashes.map (fun vh => .byteVector vh)),
    .byteVector npr.parentBeaconBlockRoot,
    executionRequestsToSsz npr.executionRequests]

def sszToNewPayloadRequest (sv : SszValue) : Except SpecError NewPayloadRequest := do
  let fs ← asContainerV sv
  let executionPayload ← sszToPayload (← getField fs 0)
  let versionedHashes ← (← asListV (← getField fs 1)).mapM asBytesV
  let parentBeaconBlockRoot ← asBytesV (← getField fs 2)
  let executionRequests ← sszToExecutionRequests (← getField fs 3)
  pure { executionPayload, versionedHashes, parentBeaconBlockRoot, executionRequests }

/-! ## `_witness_to_ssz` / `_ssz_to_witness` (`:452`, `:469`) -/

def witnessToSsz (w : ExecutionWitness) : SszValue :=
  .container [
    .list MAX_WITNESS_NODES none (w.state.map (fun s => .byteList MAX_BYTES_PER_WITNESS_NODE s)),
    .list MAX_WITNESS_CODES none (w.codes.map (fun c => .byteList MAX_BYTES_PER_CODE c)),
    .list MAX_WITNESS_HEADERS none (w.headers.map (fun h => .byteList MAX_BYTES_PER_HEADER h))]

def sszToWitness (sv : SszValue) : Except SpecError ExecutionWitness := do
  let fs ← asContainerV sv
  let state ← (← asListV (← getField fs 0)).mapM asBytesV
  let codes ← (← asListV (← getField fs 1)).mapM asBytesV
  let headers ← (← asListV (← getField fs 2)).mapM asBytesV
  pure { state, codes, headers }

/-! ## `_optional_u64_to_ssz` / `_ssz_to_optional_u64` (`:480`, `:489`) -/

def optionalU64ToSsz (value : Option U64) : SszValue :=
  match value with
  | none => .list MAX_OPTIONAL_FORK_ACTIVATION_VALUES (some 8) []
  | some v => .list MAX_OPTIONAL_FORK_ACTIVATION_VALUES (some 8) [.uint 8 v]

def sszToOptionalU64 (sv : SszValue) : Except SpecError (Option U64) := do
  let es ← asListV sv
  match es with
  | [] => pure none
  | v :: _ => pure (some (← asUintV v))

/-! ## `_fork_activation_to_ssz` / `_ssz_to_fork_activation` (`:498`, `:508`) -/

def forkActivationToSsz (a : ForkActivation) : SszValue :=
  .container [optionalU64ToSsz a.blockNumber, optionalU64ToSsz a.timestamp]

def sszToForkActivation (sv : SszValue) : Except SpecError ForkActivation := do
  let fs ← asContainerV sv
  let blockNumber ← sszToOptionalU64 (← getField fs 0)
  let timestamp ← sszToOptionalU64 (← getField fs 1)
  pure { blockNumber, timestamp }

/-! ## `_blob_schedule_to_ssz` / `_ssz_to_blob_schedule` (`:518`, `:531`) -/

def blobScheduleToSsz (b : BlobSchedule) : SszValue :=
  .container [.uint 8 b.target, .uint 8 b.max, .uint 8 b.baseFeeUpdateFraction]

def sszToBlobSchedule (sv : SszValue) : Except SpecError BlobSchedule := do
  let fs ← asContainerV sv
  let target ← asUintV (← getField fs 0)
  let max ← asUintV (← getField fs 1)
  let baseFeeUpdateFraction ← asUintV (← getField fs 2)
  pure { target, max, baseFeeUpdateFraction }

/-! ## `_optional_blob_schedule_to_ssz` / `_ssz_to_optional_blob_schedule`
    (`:544`, `:553`) -/

def optionalBlobScheduleToSsz (b : Option BlobSchedule) : SszValue :=
  match b with
  | none => .list MAX_BLOB_SCHEDULES_PER_FORK none []
  | some bs => .list MAX_BLOB_SCHEDULES_PER_FORK none [blobScheduleToSsz bs]

def sszToOptionalBlobSchedule (sv : SszValue) : Except SpecError (Option BlobSchedule) := do
  let es ← asListV sv
  match es with
  | [] => pure none
  | v :: _ => pure (some (← sszToBlobSchedule v))

/-! ## `_fork_config_to_ssz` / `_ssz_to_fork_config` (`:562`, `:575`) -/

def forkConfigToSsz (fc : ForkConfig) : SszValue :=
  .container [protocolForkToSsz fc.fork, forkActivationToSsz fc.activation,
    optionalBlobScheduleToSsz fc.blobSchedule]

def sszToForkConfig (sv : SszValue) : Except SpecError ForkConfig := do
  let fs ← asContainerV sv
  let fork ← sszToProtocolFork (← asUintV (← getField fs 0))
  let activation ← sszToForkActivation (← getField fs 1)
  let blobSchedule ← sszToOptionalBlobSchedule (← getField fs 2)
  pure { fork, activation, blobSchedule }

/-! ## `_chain_config_to_ssz` / `_ssz_to_chain_config` (`:588`, `:598`) -/

def chainConfigToSsz (cc : ChainConfig) : SszValue :=
  .container [.uint 8 cc.chainId, forkConfigToSsz cc.activeFork]

def sszToChainConfig (sv : SszValue) : Except SpecError ChainConfig := do
  let fs ← asContainerV sv
  let chainId ← asUintV (← getField fs 0)
  let activeFork ← sszToForkConfig (← getField fs 1)
  pure { chainId, activeFork }

/-! ## `stateless_input_to_ssz` / `ssz_to_stateless_input` (`:608`, `:630`) -/

def statelessInputToSsz (si : StatelessInput) : Except SpecError SszValue := do
  for pk in si.publicKeys do
    if pk.length ≠ PUBLIC_KEY_BYTES then
      throw (.publicKeyWrongLength pk.length)
  pure (.container [newPayloadRequestToSsz si.newPayloadRequest,
    witnessToSsz si.witness, chainConfigToSsz si.chainConfig,
    .list MAX_PUBLIC_KEYS none (si.publicKeys.map (fun pk => .byteVector pk))])

def sszToStatelessInput (sv : SszValue) : Except SpecError StatelessInput := do
  let fs ← asContainerV sv
  let newPayloadRequest ← sszToNewPayloadRequest (← getField fs 0)
  let witness ← sszToWitness (← getField fs 1)
  let chainConfig ← sszToChainConfig (← getField fs 2)
  let publicKeys ← (← asListV (← getField fs 3)).mapM asBytesV
  pure { newPayloadRequest, witness, chainConfig, publicKeys }

/-! ## `validation_result_to_ssz` / `ssz_to_validation_result` (`:644`, `:655`) -/

def validationResultToSsz (vr : StatelessValidationResult) : SszValue :=
  .container [.byteVector vr.newPayloadRequestRoot, .bool vr.successfulValidation,
    chainConfigToSsz vr.chainConfig]

def sszToValidationResult (sv : SszValue) : Except SpecError StatelessValidationResult := do
  let fs ← asContainerV sv
  let newPayloadRequestRoot ← asBytesV (← getField fs 0)
  let successfulValidation ← asBoolV (← getField fs 1)
  let chainConfig ← sszToChainConfig (← getField fs 2)
  pure { newPayloadRequestRoot, successfulValidation, chainConfig }

/-! ## Sanity: SSZ container round-trips (serialize → deserialize → domain) -/

/-- A `ChainConfig` exercising an empty and a present optional (`none`
    block_number, `some` timestamp) and a present blob schedule. -/
def sanityChainConfig : ChainConfig :=
  { chainId := 1
    activeFork :=
      { fork := .Amsterdam
        activation := { blockNumber := none, timestamp := some 100 }
        blobSchedule := some { target := 14, max := 21, baseFeeUpdateFraction := 11684671 } } }

-- Round-trip a `ChainConfig` through SSZ bytes and back.
#guard
  (do
    let bytes := (chainConfigToSsz sanityChainConfig).serialize
    let sv ← deserialize sszChainConfigType bytes
    sszToChainConfig sv).toOption == some sanityChainConfig

/-- A `StatelessValidationResult` (fixed + bool + nested container). -/
def sanityResult : StatelessValidationResult :=
  { newPayloadRequestRoot := List.replicate 32 (0x11 : Byte)
    successfulValidation := true
    chainConfig := sanityChainConfig }

-- Round-trip a `StatelessValidationResult`.
#guard
  (do
    let bytes := (validationResultToSsz sanityResult).serialize
    let sv ← deserialize sszStatelessValidationResultType bytes
    sszToValidationResult sv).toOption == some sanityResult

end EvmAsm.Stateless.SpecRef
