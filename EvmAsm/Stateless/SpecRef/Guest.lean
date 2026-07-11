/-
  EvmAsm.Stateless.SpecRef.Guest

  Port of `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`
  (`@tests-zkevm@v0.5.0`): the top-level guest shell.

  * `serialize_stateless_output`  (`stateless_guest.py:21`)
  * `deserialize_stateless_input` (`stateless_guest.py:29`)
  * `run_stateless_guest`         (`stateless_guest.py:47`)

  `run_stateless_guest` threads the execution seam (`Seam.lean`); the
  default is the `s1d19.3` partial seam `executeSeamShell`
  (`SeamShell.lean`), keeping the whole pipeline `#eval`-runnable.
-/

import EvmAsm.Stateless.SpecRef.Stateless

namespace EvmAsm.Stateless.SpecRef

/-! ## `serialize_stateless_output` (`stateless_guest.py:21`) -/

/-- Serialize a `StatelessValidationResult` to SSZ bytes. -/
def serialize_stateless_output (output : StatelessValidationResult) : Bytes :=
  (validationResultToSsz output).serialize

/-! ## `deserialize_stateless_input` (`stateless_guest.py:29`) -/

/-- Deserialize a `StatelessInput` from schema-prefixed SSZ bytes. -/
def deserialize_stateless_input (data : Bytes) : Except SpecError StatelessInput := do
  if data.length < STATELESS_INPUT_SCHEMA_ID_SIZE then
    throw .missingSchemaId
  let schema_id := bytesBEtoNat (data.take STATELESS_INPUT_SCHEMA_ID_SIZE)
  if schema_id ≠ STATELESS_INPUT_SCHEMA_ID then
    throw (.unsupportedSchemaId schema_id)
  let ssz_obj ← deserialize sszStatelessInputType (data.drop STATELESS_INPUT_SCHEMA_ID_SIZE)
  sszToStatelessInput ssz_obj

/-! ## `_default_failed_stateless_output` (`stateless_guest.py:54`) -/

/-- The sentinel output returned when the guest input cannot be decoded.
    This is deliberately distinct from validation failure after decoding: the
    latter preserves the input's request root and chain config. -/
def _default_failed_stateless_output : StatelessValidationResult :=
  { newPayloadRequestRoot := List.replicate 32 0
    successfulValidation := false
    chainConfig :=
      { chainId := 0
        activeFork :=
          { fork := .Frontier
            activation := { blockNumber := none, timestamp := none }
            blobSchedule := none } } }

/-! ## `run_stateless_guest` (`stateless_guest.py:79`) -/

/-- Run the stateless guest on serialized input, returning serialized output.
    The execution engine is the seam parameter (default: the partial seam
    `executeSeamShell`, `s1d19.3`).
    Deserialization failures produce the Python v0.5.0 sentinel output. -/
def run_stateless_guest (input_bytes : Bytes)
    (execute : ExecutionSeam := executeSeamShell) : Bytes :=
  match deserialize_stateless_input input_bytes with
  | .error _ => serialize_stateless_output _default_failed_stateless_output
  | .ok stateless_input =>
      serialize_stateless_output (verify_stateless_new_payload stateless_input execute)

/-! ## Sanity checks -/

private def z (n : Nat) : Bytes := List.replicate n (0 : Byte)

/-- A minimal, correctly-sized `ExecutionPayload` (all fixed byte fields at
    their declared widths so SSZ decode round-trips). -/
def sanityPayload : ExecutionPayload :=
  { parentHash := z 32, feeRecipient := z 20, stateRoot := z 32, receiptsRoot := z 32,
    logsBloom := z 256, prevRandao := z 32, blockNumber := 0, gasLimit := 0, gasUsed := 0,
    timestamp := 0, extraData := [], baseFeePerGas := 0, blockHash := z 32,
    transactions := [], withdrawals := [], blobGasUsed := 0, excessBlobGas := 0,
    blockAccessList := [], slotNumber := 0 }

/-- A "happy path" chain config: Amsterdam, activation satisfied by a
    zero-timestamp payload, and the expected blob schedule. -/
def sanityHappyChainConfig : ChainConfig :=
  { chainId := 1
    activeFork :=
      { fork := .Amsterdam
        activation := { blockNumber := none, timestamp := some 0 }
        blobSchedule := some _expected_amsterdam_blob_schedule } }

/-- A single amsterdam witness header (23 RLP fields). A one-element chain is
    vacuously contiguous, so `validate_headers` succeeds and its `state_root`
    seeds the pre-state. -/
def sanityHeader : Bytes := mkTestHeaderBytes 23 (z 32) (z 32)

def sanityInput : StatelessInput :=
  { newPayloadRequest :=
      { executionPayload := sanityPayload
        versionedHashes := []
        parentBeaconBlockRoot := z 32
        executionRequests := { deposits := [], withdrawals := [], consolidations := [] } }
    witness := { state := [], codes := [], headers := [sanityHeader] }
    chainConfig := sanityHappyChainConfig
    publicKeys := [] }

/-- Schema-prefixed SSZ encoding of `sanityInput`. -/
def sanityInputBytes : Except SpecError Bytes := do
  let ssz ← statelessInputToSsz sanityInput
  pure (natToBytesBE STATELESS_INPUT_SCHEMA_ID_SIZE STATELESS_INPUT_SCHEMA_ID ++ ssz.serialize)

-- End-to-end: schema-prefixed bytes deserialize back to `sanityInput`.
#guard
  (do
    let bytes ← sanityInputBytes
    deserialize_stateless_input bytes).toOption == some sanityInput

-- Wrong schema id is rejected.
#guard
  match deserialize_stateless_input (natToBytesBE 2 0x0002 ++ z 8) with
  | .error (.unsupportedSchemaId 2) => true | _ => false

-- Input shorter than the schema id is rejected.
#guard
  match deserialize_stateless_input [0x00] with
  | .error .missingSchemaId => true | _ => false

-- Full pipeline with the seam forced to `executeAlwaysOk`: SSZ output
-- decodes, successful_validation is true, and the NPR root matches.
#guard
  match sanityInputBytes with
  | .ok out =>
      match deserialize sszStatelessValidationResultType
          (run_stateless_guest out (execute := executeAlwaysOk)) with
      | .ok sv =>
          match sszToValidationResult sv with
          | .ok r => r.successfulValidation
                     && r.newPayloadRequestRoot == compute_new_payload_request_root sanityInput
          | .error _ => false
      | .error _ => false
  | .error _ => false

-- Under the default (s1d19.3 partial) seam the synthetic sanity input is
-- rejected — its block hash is not the keccak of the implied header —
-- but the shell still runs end-to-end and reports the same NPR root.
#guard
  match sanityInputBytes with
  | .ok out =>
      match deserialize sszStatelessValidationResultType (run_stateless_guest out) with
      | .ok sv =>
          match sszToValidationResult sv with
          | .ok r => !r.successfulValidation
                     && r.newPayloadRequestRoot == compute_new_payload_request_root sanityInput
          | .error _ => false
      | .error _ => false
  | .error _ => false

-- Invalid input takes the v0.5.0 failed-output path rather than exposing a
-- deserialization exception to the caller.
#guard
  match deserialize sszStatelessValidationResultType (run_stateless_guest [0x00]) with
  | .ok sv =>
      match sszToValidationResult sv with
      | .ok r => !r.successfulValidation
                 && r.newPayloadRequestRoot == z 32
                 && r.chainConfig.chainId == 0
                 && r.chainConfig.activeFork.fork == .Frontier
      | .error _ => false
  | .error _ => false

end EvmAsm.Stateless.SpecRef
