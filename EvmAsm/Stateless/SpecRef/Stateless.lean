/-
  EvmAsm.Stateless.SpecRef.Stateless

  Port of `execution-specs/src/ethereum/forks/amsterdam/stateless.py`
  (`@tests-zkevm@v0.4.0`): the seven functions of the stateless validation
  shell.

  * `compute_new_payload_request_root` (`stateless.py:231`)
  * `_decode_header`                   (`stateless.py:246`)
  * `validate_headers`                 (`stateless.py:257`)
  * `_is_activation_active`            (`stateless.py:280`)
  * `_expected_amsterdam_blob_schedule`(`stateless.py:305`)
  * `validate_chain_config`            (`stateless.py:316`)
  * `verify_stateless_new_payload`     (`stateless.py:344`)

  ## The execution seam

  `verify_stateless_new_payload` calls `execute_new_payload_request`
  (`stateless.py:378`) — full statefull block re-execution
  (`execution_engine.new_payload`). That is NOT ported here (it is the
  whole EVM). We cut at exactly that call: everything on the
  validation/deserialization/hashing side is real; the execution engine is
  an explicit parameter `execute : ExecutionSeam` taking the precise inputs
  the Python call passes (`NewPayloadRequest`, the witness-backed pre-state,
  the `ChainContext`, and the transaction public keys) and returning
  `Except SpecError Unit` (`ok` ≙ Python returning normally, `error` ≙ any
  raised exception). Bead `evm-asm-4ch8f.8` decides how this seam is
  instantiated against the RV64 guest. `executeAlwaysOk` is a placeholder
  so the shell is `#eval`-runnable end-to-end.
-/

import EvmAsm.Stateless.SpecRef.Ssz
import EvmAsm.Stateless.SpecRef.SeamShell

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.EL.RLP (RLPItem decodeFully)

/-! ## `compute_new_payload_request_root` (`stateless.py:231`) -/

/-- Compute the request root for a stateless input via SSZ hash tree root. -/
def compute_new_payload_request_root (si : StatelessInput) : Hash32 :=
  (newPayloadRequestToSsz si.newPayloadRequest).hashTreeRoot

/-! ## `_decode_header` (`stateless.py:246`)

`rlp.decode_to(Header, …)` is type-directed; we decode to a generic RLP
list and discriminate the current fork (amsterdam, 23 fields) from the
previous fork (bpo5, 21 fields) by RLP list length. See
docs/4ch8f-specref-port.md for the one modeling simplification here (we do
not re-impose `rlp.decode_to`'s per-field byte-length checks; the field
count is the fork discriminant). -/

private def rlpBytes? : RLPItem → Option Bytes
  | .bytes b => some b
  | _ => none

/-- Build a `Header` from its decoded RLP field bytes. Fields 21–22
    (`block_access_list_hash`, `slot_number`) are amsterdam-only and default
    to `[]`/`0` for the previous fork. -/
private def mkHeader (isCurrent : Bool) (bs : List Bytes) : Header :=
  let getB := fun i => bs.getD i []
  let getN := fun i => bytesBEtoNat (bs.getD i [])
  { isCurrentFork := isCurrent
    parentHash := getB 0, ommersHash := getB 1, coinbase := getB 2,
    stateRoot := getB 3, transactionsRoot := getB 4, receiptRoot := getB 5,
    bloom := getB 6, difficulty := getN 7, number := getN 8, gasLimit := getN 9,
    gasUsed := getN 10, timestamp := getN 11, extraData := getB 12,
    prevRandao := getB 13, nonce := getB 14, baseFeePerGas := getN 15,
    withdrawalsRoot := getB 16, blobGasUsed := getN 17, excessBlobGas := getN 18,
    parentBeaconBlockRoot := getB 19, requestsHash := getB 20,
    blockAccessListHash := getB 21, slotNumber := getN 22 }

/-- Decode an RLP-encoded header, current fork (23 fields) first, else the
    previous fork (21 fields). -/
def _decode_header (header_bytes : Bytes) : Except SpecError Header :=
  match decodeFully header_bytes with
  | some (.list items) =>
      match items.mapM rlpBytes? with
      | none => .error .headerDecodeError
      | some bs =>
          if bs.length = 23 then .ok (mkHeader true bs)
          else if bs.length = 21 then .ok (mkHeader false bs)
          else .error .headerDecodeError
  | _ => .error .headerDecodeError

/-! ## `validate_headers` (`stateless.py:257`) -/

/-- Validate that a sequence of encoded headers forms a contiguous chain.
    Each header's `parent_hash` must match the hash of the preceding header.
    Returns the decoded headers and their block hashes. -/
def validate_headers (encoded_headers : List Bytes) :
    Except SpecError (List Header × List Hash32) := do
  if encoded_headers.length > 256 then
    throw (.tooManyHeaders encoded_headers.length)
  let headers ← encoded_headers.mapM _decode_header
  let block_hashes : List Hash32 := encoded_headers.map keccak256
  -- headers[i].parent_hash == block_hashes[i-1] for i in 1..len
  let contiguous := (headers.drop 1).zip block_hashes
    |>.all (fun p => p.1.parentHash == p.2)
  if contiguous then pure (headers, block_hashes)
  else throw .headersNotContiguous

/-! ## `_is_activation_active` (`stateless.py:280`) -/

/-- Whether an activation point is active for the payload. -/
def _is_activation_active (activation : ForkActivation) (ep : ExecutionPayload) :
    Except SpecError Bool := do
  if activation.blockNumber.isNone ∧ activation.timestamp.isNone then
    throw .forkActivationMissing
  if let some bn := activation.blockNumber then
    if ep.blockNumber < bn then return false
  if let some ts := activation.timestamp then
    if ep.timestamp < ts then return false
  return true

/-! ## `_expected_amsterdam_blob_schedule` (`stateless.py:305`) -/

/-- The blob schedule compiled into the Amsterdam guest. -/
def _expected_amsterdam_blob_schedule : BlobSchedule :=
  { target := blobScheduleTarget
    max := blobScheduleMax
    baseFeeUpdateFraction := blobBaseFeeUpdateFraction }

/-! ## `validate_chain_config` (`stateless.py:316`) -/

/-- Validate and return the target payload's active fork config. -/
def validate_chain_config (chain_config : ChainConfig) (npr : NewPayloadRequest) :
    Except SpecError ForkConfig := do
  let active_fork := chain_config.activeFork
  let execution_payload := npr.executionPayload
  if !(← _is_activation_active active_fork.activation execution_payload) then
    throw .inactiveForkConfig
  if active_fork.fork ≠ ProtocolFork.Amsterdam then
    throw (.unsupportedForkConfig "Amsterdam guest cannot execute configured fork")
  if active_fork.blobSchedule ≠ some _expected_amsterdam_blob_schedule then
    throw (.unsupportedForkConfig "blob_schedule does not match Amsterdam")
  pure active_fork

/-! ## The execution seam

The seam interface (`ChainContext`, `ExecutionSeamInput`,
`ExecutionSeam`, `executeAlwaysOk`) lives in `Seam.lean`; the default
below is the `s1d19.3` partial seam `executeSeamShell`
(`SeamShell.lean`): the `execute_new_payload_request` pre-checks +
`execute_block`'s pre-execution frame + root-anchored witness
authentication, with `apply_body` still stubbed to accept
(sound-for-accepts, scope doc §3). -/

/-! ## `verify_stateless_new_payload` (`stateless.py:344`) -/

/-- Statelessly validate the execution payload. Every exception the Python
    `try` would catch is folded into `successful_validation = false`. -/
def verify_stateless_new_payload (si : StatelessInput)
    (execute : ExecutionSeam := executeSeamShell) : StatelessValidationResult :=
  let new_payload_request_root := compute_new_payload_request_root si
  let witness := si.witness
  let attempt : Except SpecError Unit := do
    let _ ← validate_chain_config si.chainConfig si.newPayloadRequest
    let (decoded_headers, block_hashes) ← validate_headers witness.headers
    let parent_header ← match decoded_headers.getLast? with
      | some h => pure h
      | none => throw (.executionRejected "no witness headers")  -- decoded_headers[-1]
    let chain_context : ChainContext :=
      { chainId := si.chainConfig.chainId
        blockHashes := block_hashes
        parentHeader := parent_header }
    let pre_state : WitnessPreState :=
      { nodeDb := build_node_db witness.state
        stateRoot := parent_header.stateRoot
        codeDb := build_code_db witness.codes }
    execute { newPayloadRequest := si.newPayloadRequest
              preState := pre_state
              chainContext := chain_context
              transactionPublicKeys := si.publicKeys }
  { newPayloadRequestRoot := new_payload_request_root
    successfulValidation := (match attempt with | .ok _ => true | .error _ => false)
    chainConfig := si.chainConfig }

/-! ## Sanity checks -/

-- A blob schedule matching the expected Amsterdam schedule is accepted.
def sanityForkConfig : ForkConfig :=
  { fork := .Amsterdam
    activation := { blockNumber := none, timestamp := some 100 }
    blobSchedule := some _expected_amsterdam_blob_schedule }

-- Build a minimal RLP header with `n` fields, field 0 = parent_hash,
-- field 3 = state_root, all others empty.
def mkTestHeaderBytes (n : Nat) (parentHash stateRoot : Bytes) : Bytes :=
  let fields : List RLPItem := (List.range n).map (fun i =>
    if i = 0 then .bytes parentHash
    else if i = 3 then .bytes stateRoot
    else .bytes [])
  EvmAsm.EL.RLP.encode (.list fields)

-- Amsterdam header (23 fields) decodes with isCurrentFork = true.
#guard
  match _decode_header (mkTestHeaderBytes 23 (List.replicate 32 0x01) (List.replicate 32 0x02)) with
  | .ok h => h.isCurrentFork && h.parentHash == List.replicate 32 0x01
             && h.stateRoot == List.replicate 32 0x02
  | .error _ => false

-- Previous-fork header (21 fields) decodes with isCurrentFork = false.
#guard
  match _decode_header (mkTestHeaderBytes 21 (List.replicate 32 0x03) (List.replicate 32 0x04)) with
  | .ok h => (!h.isCurrentFork) && h.parentHash == List.replicate 32 0x03
  | .error _ => false

-- A header with a bad field count is rejected.
#guard match _decode_header (mkTestHeaderBytes 20 [] []) with
  | .error .headerDecodeError => true | _ => false

-- Two contiguous headers validate; a non-contiguous pair does not.
#guard
  let h0 := mkTestHeaderBytes 23 (List.replicate 32 0x00) (List.replicate 32 0x00)
  let h0hash := keccak256 h0
  let h1 := mkTestHeaderBytes 23 h0hash (List.replicate 32 0x05)
  match validate_headers [h0, h1] with
  | .ok (hs, hashes) => hs.length == 2 && hashes.length == 2
  | .error _ => false

#guard
  let h0 := mkTestHeaderBytes 23 (List.replicate 32 0x00) (List.replicate 32 0x00)
  let h1 := mkTestHeaderBytes 23 (List.replicate 32 0xEE) (List.replicate 32 0x05)  -- wrong parent
  match validate_headers [h0, h1] with
  | .error .headersNotContiguous => true | _ => false

-- Activation: active when payload meets the timestamp; missing both fails.
#guard
  let ep : ExecutionPayload := (Inhabited.default : ExecutionPayload)
  match _is_activation_active { blockNumber := none, timestamp := some 0 } ep with
  | .ok b => b | _ => false

#guard
  match _is_activation_active { blockNumber := none, timestamp := none }
      (Inhabited.default : ExecutionPayload) with
  | .error .forkActivationMissing => true | _ => false

end EvmAsm.Stateless.SpecRef
