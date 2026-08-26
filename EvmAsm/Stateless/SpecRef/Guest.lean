/-
  EvmAsm.Stateless.SpecRef.Guest

  Port of `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`
  (`@tests-zkevm@v0.6.0`, `40f956fab`): the top-level guest shell.

  * `serialize_stateless_output`  (`stateless_guest.py:27`)
  * `deserialize_stateless_input` (`stateless_guest.py:35`)
  * `run_stateless_guest`         (`stateless_guest.py:72`)

  `run_stateless_guest` threads the execution seam (`Seam.lean`); the
  default is the full seam `elExecute` (`PrecompilesTable.lean`),
  keeping the whole pipeline `#eval`-runnable.
-/

module

public import EvmAsm.Stateless.SpecRef.Stateless
meta import EvmAsm.Stateless.SpecRef.Stateless

@[expose] public section

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

/-! ## `_default_failed_stateless_output` (`stateless_guest.py:53`) -/

/-- The sentinel output returned when the guest input cannot be decoded.
    This is deliberately distinct from validation failure after decoding: the
    latter preserves the input's request root and chain config. -/
def _default_failed_stateless_output : StatelessValidationResult :=
  { newPayloadRequestRoot := List.replicate 32 0
    successfulValidation := false
    chainConfig :=
      { chainId := 0
        activeFork :=
          { activation := { blockNumber := none, timestamp := none } } } }

/-! ## `run_stateless_guest` (`stateless_guest.py:79`) -/

/-- Run the stateless guest on serialized input, returning serialized output.
    The execution engine is the seam parameter (default: the full
    seam `elExecute`, `s1d19.5`).
    Deserialization failures produce the Python sentinel output. -/
def run_stateless_guest (input_bytes : Bytes)
    (execute : ExecutionSeam := elExecute) : Bytes :=
  match deserialize_stateless_input input_bytes with
  | .error _ => serialize_stateless_output _default_failed_stateless_output
  | .ok stateless_input =>
      serialize_stateless_output (verify_stateless_new_payload stateless_input execute)

/-- Bytes entry for `diagnose_stateless_gas_dims` (tooling / #11808). -/
def diagnose_stateless_gas_dims_bytes (input_bytes : Bytes)
    (pre : PrecompileMap := specRefPrecompilesFull) :
    Except String StatelessGasDims :=
  match deserialize_stateless_input input_bytes with
  | .error e => .error s!"deserialize_stateless_input: {repr e}"
  | .ok si =>
      match diagnose_stateless_gas_dims si pre with
      | .ok d => .ok d
      | .error e => .error s!"diagnose_stateless_gas_dims: {repr e}"

/-! ## Reject-path theorems

    The EEST family `eip8025_optional_proofs/stateless_input_bytes/
    invalid_stateless_input_bytes_are_rejected.json` (pinned tag
    `tests-zkevm@v0.6.2`) samples the reject path at eight malformed-input
    shapes; the theorems below state the underlying guarantees once, for
    all inputs. Note that a blanket "trailing bytes are rejected" is NOT a
    theorem of this codec: the final SSZ field of `sszStatelessInputType`
    is `.list (.byteVector PUBLIC_KEY_BYTES) MAX_PUBLIC_KEYS`, so appending
    exactly `PUBLIC_KEY_BYTES` bytes decodes as one extra public key. The
    fixtures reject because their mutations are not so aligned. -/

/-- Any input shorter than the schema id is rejected with `.missingSchemaId`. -/
theorem deserialize_stateless_input_short {bs : Bytes}
    (h : bs.length < STATELESS_INPUT_SCHEMA_ID_SIZE) :
    deserialize_stateless_input bs = .error .missingSchemaId := by
  unfold deserialize_stateless_input
  simp only [h, if_true]
  rfl

/-- Any input whose schema-id prefix is not `STATELESS_INPUT_SCHEMA_ID` is
    rejected with `.unsupportedSchemaId` carrying that prefix. -/
theorem deserialize_stateless_input_wrong_schema {bs : Bytes}
    (hlen : STATELESS_INPUT_SCHEMA_ID_SIZE ≤ bs.length)
    (hid : bytesBEtoNat (bs.take STATELESS_INPUT_SCHEMA_ID_SIZE)
      ≠ STATELESS_INPUT_SCHEMA_ID) :
    deserialize_stateless_input bs
      = .error (.unsupportedSchemaId
          (bytesBEtoNat (bs.take STATELESS_INPUT_SCHEMA_ID_SIZE))) := by
  unfold deserialize_stateless_input
  simp only [Nat.not_lt.mpr hlen, hid, reduceIte, ne_eq, not_false_eq_true,
    if_neg]
  rfl

/-- On any deserialization failure the guest emits exactly the sentinel
    bytes — never an exception, never a partial output. -/
theorem run_stateless_guest_error {bs : Bytes} {e : SpecError}
    (execute : ExecutionSeam)
    (h : deserialize_stateless_input bs = .error e) :
    run_stateless_guest bs execute
      = serialize_stateless_output _default_failed_stateless_output := by
  unfold run_stateless_guest
  rw [h]

/-- The sentinel bytes decode back to `_default_failed_stateless_output`:
    the reject path always produces a well-formed, decodable result. -/
theorem failed_output_decodes :
    (deserialize sszStatelessValidationResultType
        (serialize_stateless_output _default_failed_stateless_output)).bind
      sszToValidationResult = .ok _default_failed_stateless_output := by
  decide

/-- Reject-branch robustness: whenever the input fails to deserialize, the
    guest's output decodes to the sentinel result. -/
theorem run_stateless_guest_error_decodes {bs : Bytes} {e : SpecError}
    (execute : ExecutionSeam)
    (h : deserialize_stateless_input bs = .error e) :
    (deserialize sszStatelessValidationResultType
        (run_stateless_guest bs execute)).bind sszToValidationResult
      = .ok _default_failed_stateless_output := by
  rw [run_stateless_guest_error execute h]
  exact failed_output_decodes

/-- Pure value-side inverse: `sszToValidationResult` undoes
    `validationResultToSsz` exactly (no byte codec involved). -/
theorem sszToValidationResult_validationResultToSsz
    (vr : StatelessValidationResult) :
    sszToValidationResult (validationResultToSsz vr) = .ok vr := by
  obtain ⟨root, succ, ⟨cid, ⟨⟨bn, ts⟩⟩⟩⟩ := vr
  cases bn <;> cases ts <;> rfl

/-- **Total robustness**: for every input byte string and every execution
    seam, the guest's output decodes to a well-formed
    `StatelessValidationResult` — the reject branch yields the sentinel and
    the accept branch a result whose 32-byte root comes from
    `hashTreeRoot_length`. No hypotheses on `bs`. -/
theorem run_stateless_guest_total (bs : Bytes) (execute : ExecutionSeam) :
    ∃ v vr, deserialize sszStatelessValidationResultType
        (run_stateless_guest bs execute) = .ok v
      ∧ sszToValidationResult v = .ok vr := by
  cases h : deserialize_stateless_input bs with
  | error e =>
      refine ⟨validationResultToSsz _default_failed_stateless_output,
        _default_failed_stateless_output, ?_,
        sszToValidationResult_validationResultToSsz _⟩
      rw [run_stateless_guest_error execute h]
      have hroot :
          _default_failed_stateless_output.newPayloadRequestRoot.length = 32 := by
        simp [_default_failed_stateless_output]
      have hrt := validationResult_roundtrip 58 _default_failed_stateless_output hroot
      simpa [deserialize, serialize_stateless_output, SszValue.serialize, sszFuel,
        _default_failed_stateless_output, truncConfig, truncActivation] using hrt
  | ok si =>
      have hout : run_stateless_guest bs execute
          = serialize_stateless_output (verify_stateless_new_payload si execute) := by
        unfold run_stateless_guest
        rw [h]
      have hroot : (verify_stateless_new_payload si execute).newPayloadRequestRoot.length
          = 32 := by
        simp only [verify_stateless_new_payload, compute_new_payload_request_root]
        exact hashTreeRoot_length _
      refine ⟨validationResultToSsz
        { newPayloadRequestRoot :=
            (verify_stateless_new_payload si execute).newPayloadRequestRoot
          successfulValidation :=
            (verify_stateless_new_payload si execute).successfulValidation
          chainConfig := truncConfig (verify_stateless_new_payload si execute).chainConfig },
        _, ?_, sszToValidationResult_validationResultToSsz _⟩
      rw [hout]
      have hrt := validationResult_roundtrip 58 (verify_stateless_new_payload si execute) hroot
      simpa [deserialize, serialize_stateless_output, SszValue.serialize, sszFuel] using hrt

/-! ## Sanity checks -/

def z (n : Nat) : Bytes := List.replicate n (0 : Byte)

/-- A minimal, correctly-sized `ExecutionPayload` (all fixed byte fields at
    their declared widths so SSZ decode round-trips). -/
def sanityPayload : ExecutionPayload :=
  { parentHash := z 32, feeRecipient := z 20, stateRoot := z 32, receiptsRoot := z 32,
    logsBloom := z 256, prevRandao := z 32, blockNumber := 0, gasLimit := 0, gasUsed := 0,
    timestamp := 0, extraData := [], baseFeePerGas := 0, blockHash := z 32,
    transactions := [], withdrawals := [], blobGasUsed := 0, excessBlobGas := 0,
    blockAccessList := [], slotNumber := 0 }

/-- A "happy path" chain config: activation satisfied by a
    zero-timestamp payload. -/
def sanityHappyChainConfig : ChainConfig :=
  { chainId := 1
    activeFork :=
      { activation := { blockNumber := none, timestamp := some 0 } } }

/-- A single amsterdam witness header (23 RLP fields). A one-element chain is
    vacuously contiguous, so `validate_headers` succeeds and its `state_root`
    seeds the pre-state. -/
def sanityHeader : Bytes := mkTestHeaderBytes 23 (z 32) (z 32)

def sanityInput : StatelessInput :=
  { newPayloadRequest :=
      { executionPayload := sanityPayload
        versionedHashes := []
        parentBeaconBlockRoot := z 32
        executionRequests := {
          deposits := [], withdrawals := [], consolidations := [],
          builderDeposits := [], builderExits := [] } }
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

-- Invalid input takes the failed-output path rather than exposing a
-- deserialization exception to the caller.
#guard
  match deserialize sszStatelessValidationResultType (run_stateless_guest [0x00]) with
  | .ok sv =>
      match sszToValidationResult sv with
      | .ok r => !r.successfulValidation
                 && r.newPayloadRequestRoot == z 32
                 && r.chainConfig.chainId == 0
      | .error _ => false
  | .error _ => false

/-! ## EEST malformed-input shapes

    One check per case of the EEST fixture family
    `eip8025_optional_proofs/stateless_input_bytes/
    invalid_stateless_input_bytes_are_rejected.json` (tag
    `tests-zkevm@v0.6.2`). The fixture inputs are mechanical edits of one
    valid base input; here the same edits are applied to
    `sanityInputBytes`, so the shapes are pinned without embedding fixture
    literals. Rejection *reasons* are matched by constructor only (the
    conformance harness never compares them). -/

/-- The valid schema-prefixed sanity bytes. The `.getD []` default is
    self-checking: were `sanityInputBytes` an `.error`, the schema-shape
    guards below would observe the wrong constructor and fail. -/
private def sanityB : Bytes := sanityInputBytes.toOption.getD []

-- EEST `empty_input_bytes`: empty input ⇒ missing schema id.
#guard deserialize_stateless_input [] matches .error .missingSchemaId

-- EEST `incomplete_schema_id`: one byte ⇒ missing schema id.
#guard deserialize_stateless_input [0x15] matches .error .missingSchemaId

-- EEST `missing_ssz_body`: schema id with empty body ⇒ SSZ error.
#guard deserialize_stateless_input [0x15, 0x01] matches .error (.sszError _)

-- EEST `invalid_first_ssz_offset`: first offset word pointed into the
-- fixed section ⇒ SSZ error before validation can run.
#guard deserialize_stateless_input
    (sanityB.take 2 ++ [0x01, 0x00, 0x00, 0x00] ++ sanityB.drop 6)
  matches .error (.sszError _)

-- EEST `unsupported_schema_fork`: fork index 0x16 ⇒ unsupported schema id.
#guard deserialize_stateless_input ([0x16, 0x01] ++ sanityB.drop 2)
  matches .error (.unsupportedSchemaId 0x1601)

-- EEST `unsupported_schema_revision`: revision 0x02 ⇒ unsupported schema id.
#guard deserialize_stateless_input ([0x15, 0x02] ++ sanityB.drop 2)
  matches .error (.unsupportedSchemaId 0x1502)

-- EEST `truncated_ssz_body`: last byte dropped ⇒ rejected.
#guard deserialize_stateless_input sanityB.dropLast matches .error _

-- EEST `trailing_garbage`: one trailing byte ⇒ rejected (lands in the
-- trailing fixed-element public-key list, misaligning its element size).
#guard deserialize_stateless_input (sanityB ++ [0x00]) matches .error (.sszError _)

-- Byte-for-byte pin of the fixture family's shared `statelessOutputBytes`
-- (61 bytes): zero root, `successful_validation = 0`, then the SSZ offsets
-- and zero chain config of `_default_failed_stateless_output`.
#guard serialize_stateless_output _default_failed_stateless_output ==
  (z 32 ++ [0x00] ++ natToBytesLE 4 0x25 ++ z 8
    ++ natToBytesLE 4 0x0c ++ natToBytesLE 4 0x04
    ++ natToBytesLE 4 0x08 ++ natToBytesLE 4 0x08)

-- Reject path end-to-end: a malformed input yields exactly the sentinel bytes.
#guard run_stateless_guest [0x15]
  == serialize_stateless_output _default_failed_stateless_output

end EvmAsm.Stateless.SpecRef
