/-
  EvmAsm.EL.Secp256r1VerifyPrecompileDispatch

  Pure EVM P256VERIFY precompile framing. The secp256r1 scalar, public-key,
  curve-membership, and signature checks are supplied by the accelerator
  boundary; this module fixes the execution-specs-visible target, gas,
  length, field slicing, and common precompile result shape.
-/

import EvmAsm.EL.Secp256r1VerifyPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Secp256r1VerifyPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev AcceleratorInput := Secp256r1VerifyInputBridge.AcceleratorInput
abbrev AcceleratorResult := Secp256r1VerifyResultBridge.AcceleratorResult

/-- EIP-7951 P256VERIFY payload length: msg || r || s || qx || qy. -/
def inputLength : Nat := 160

def msgOffset : Nat := 0
def sigOffset : Nat := 32
def pubkeyOffset : Nat := 96

/-- Total byte-length validation from execution-specs `if len(data) != 160`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length == inputLength

/-- Safe byte projection; callers pair it with `validInputLength`. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Message-hash bytes from the execution-specs payload slice `data[0:32]`. -/
def messageHashBytes (payload : List Byte) : Secp256r1VerifyInputBridge.MessageHashBytes :=
  fun i => payloadByte payload (msgOffset + i.val)

/-- Signature bytes from the execution-specs payload slices `data[32:96]` (`r || s`). -/
def signatureBytes (payload : List Byte) : Secp256r1VerifyInputBridge.SignatureBytes :=
  fun i => payloadByte payload (sigOffset + i.val)

/-- Public-key bytes from the execution-specs payload slices `data[96:160]` (`qx || qy`). -/
def publicKeyBytes (payload : List Byte) : Secp256r1VerifyInputBridge.PublicKeyBytes :=
  fun i => payloadByte payload (pubkeyOffset + i.val)

/-- Accelerator input extracted from EVM call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { msg := messageHashBytes payload
    sig := signatureBytes payload
    pubkey := publicKeyBytes payload }

/-- Fixed EIP-7951 P256VERIFY precompile gas cost. -/
def gasCost (_payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .p256Verify inputLength |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/-- Execution-specs P256 invalid-length/invalid-signature result: success with no returndata. -/
def emptySuccess (gasRemaining : Nat) : EvmAsm.Evm64.PrecompileResult :=
  EvmAsm.Evm64.PrecompileResult.ok ([] : List Byte) gasRemaining

/--
Pure P256VERIFY precompile dispatch.

The execution-specs order is: fixed 6,900 gas charge, exact 160-byte length
check, accelerator validation, and 32-byte `1` output only for a verified
signature. Bad length and invalid signatures return successful empty output
after gas charge.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .p256Verify then
    let cost := gasCost input.input
    if _h_gas : cost <= input.gas then
      if _h_len : validInputLength input.input then
        let accInput := acceleratorInput input.input
        let request := Secp256r1VerifyEcallBridge.requestFromInput accInput
        let result := Secp256r1VerifyEcallBridge.executeSecp256r1VerifyEcall accelerator request
        match result.status with
        | .eok =>
            if result.output.verified then
              Secp256r1VerifyPrecompileResultBridge.fromVerifyResult
                (input.gas - cost) result
            else
              emptySuccess (input.gas - cost)
        | .efail =>
            Secp256r1VerifyPrecompileResultBridge.fromVerifyResult
              (input.gas - cost) result
      else
        emptySuccess (input.gas - cost)
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_fixed (payload : List Byte) :
    gasCost payload = 6900 := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem validInputLength_iff (payload : List Byte) :
    validInputLength payload = true <-> payload.length = inputLength := by
  simp [validInputLength]

theorem acceleratorInput_msg (payload : List Byte) :
    (acceleratorInput payload).msg = messageHashBytes payload := rfl

theorem acceleratorInput_sig (payload : List Byte) :
    (acceleratorInput payload).sig = signatureBytes payload := rfl

theorem acceleratorInput_pubkey (payload : List Byte) :
    (acceleratorInput payload).pubkey = publicKeyBytes payload := rfl

theorem dispatch_non_p256Verify
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .p256Verify) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .p256Verify)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_not]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .p256Verify)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = emptySuccess (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas, h_len]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .p256Verify)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok)
    (h_verified : (accelerator (acceleratorInput input.input)).output.verified = true) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Secp256r1VerifyPrecompileResultBridge.verifyOutputBytes true)
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas, h_len,
    Secp256r1VerifyEcallBridge.requestFromInput,
    Secp256r1VerifyEcallBridge.executeSecp256r1VerifyEcall,
    Secp256r1VerifyPrecompileResultBridge.fromVerifyResult,
    Secp256r1VerifyPrecompileResultBridge.outputBytesFromResult,
    h_status, h_verified]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .p256Verify)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok)
    (h_verified : (accelerator (acceleratorInput input.input)).output.verified = true) :
    (dispatch accelerator input).output.length = 32 := by
  rw [dispatch_success accelerator h_target h_gas h_len h_status h_verified]
  simp [Secp256r1VerifyPrecompileResultBridge.verifyOutputBytes_length]

theorem dispatch_unverified_empty_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .p256Verify)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok)
    (h_verified : (accelerator (acceleratorInput input.input)).output.verified = false) :
    dispatch accelerator input = emptySuccess (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas, h_len,
    Secp256r1VerifyEcallBridge.requestFromInput,
    Secp256r1VerifyEcallBridge.executeSecp256r1VerifyEcall,
    h_status, h_verified]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .p256Verify)
    (h_gas : gasCost input.input <= input.gas)
    (h_len : validInputLength input.input = true)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas, h_len,
    Secp256r1VerifyEcallBridge.requestFromInput,
    Secp256r1VerifyEcallBridge.executeSecp256r1VerifyEcall,
    Secp256r1VerifyPrecompileResultBridge.fromVerifyResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .p256Verify
  · simp only [h_target, ↓reduceDIte]
    by_cases h_gas : gasCost input.input <= input.gas
    · simp only [h_gas, ↓reduceDIte]
      by_cases h_len : validInputLength input.input
      · simp only [h_len, ↓reduceDIte]
        cases h_status : (Secp256r1VerifyEcallBridge.executeSecp256r1VerifyEcall accelerator
          (Secp256r1VerifyEcallBridge.requestFromInput
            (acceleratorInput input.input))).status
        · cases h_verified : (Secp256r1VerifyEcallBridge.executeSecp256r1VerifyEcall accelerator
              (Secp256r1VerifyEcallBridge.requestFromInput
                (acceleratorInput input.input))).output.verified <;>
            simp [Secp256r1VerifyPrecompileResultBridge.fromVerifyResult,
              emptySuccess, h_status,
              EvmAsm.Evm64.PrecompileResult.ok]
        · simp [Secp256r1VerifyPrecompileResultBridge.fromVerifyResult,
            h_status, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_len, emptySuccess, EvmAsm.Evm64.PrecompileResult.ok]
    · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Secp256r1VerifyPrecompileDispatch

end EvmAsm.EL
