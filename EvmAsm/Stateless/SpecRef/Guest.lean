/-
  EvmAsm.Stateless.SpecRef.Guest

  Port of `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`
  (`@tests-zkevm@v0.4.0`): the top-level guest shell.

  * `serialize_stateless_output`  (`stateless_guest.py:21`)
  * `deserialize_stateless_input` (`stateless_guest.py:29`)
  * `run_stateless_guest`         (`stateless_guest.py:47`)

  `run_stateless_guest` threads the execution seam (`Stateless.lean`) so the
  whole pipeline is `#eval`-runnable with the `executeAlwaysOk` placeholder.
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

/-! ## `run_stateless_guest` (`stateless_guest.py:47`) -/

/-- Run the stateless guest on serialized input, returning serialized output.
    The execution engine is the seam parameter (default: `executeAlwaysOk`).
    Deserialization failures propagate (Python does not catch them). -/
def run_stateless_guest (input_bytes : Bytes)
    (execute : ExecutionSeam := executeAlwaysOk) : Except SpecError Bytes := do
  let stateless_input ← deserialize_stateless_input input_bytes
  let stateless_output := verify_stateless_new_payload stateless_input execute
  pure (serialize_stateless_output stateless_output)

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

-- Full pipeline: run the guest and get SSZ output bytes whose decoded
-- successful_validation is true (placeholder seam) and whose NPR root matches.
#guard
  match (do
      let bytes ← sanityInputBytes
      run_stateless_guest bytes) with
  | .ok out =>
      match deserialize sszStatelessValidationResultType out with
      | .ok sv =>
          match sszToValidationResult sv with
          | .ok r => r.successfulValidation
                     && r.newPayloadRequestRoot == compute_new_payload_request_root sanityInput
          | .error _ => false
      | .error _ => false
  | .error _ => false

end EvmAsm.Stateless.SpecRef
