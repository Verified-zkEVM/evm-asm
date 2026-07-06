/-
  EvmAsm.EL.KzgPointEvalPrecompileDispatch

  Pure EVM KZG point-evaluation precompile framing. The versioned-hash
  validation and proof verification are supplied at explicit boundaries; this
  module fixes the execution-specs-visible target, length, gas, input slicing,
  and common precompile result shape.
-/

import EvmAsm.EL.KzgPointEvalPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace KzgPointEvalPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev Bytes32 := KzgPointEvalInputBridge.Bytes32
abbrev AcceleratorInput := KzgPointEvalInputBridge.AcceleratorInput
abbrev AcceleratorResult := KzgPointEvalResultBridge.AcceleratorResult

/-- EIP-4844 point-evaluation payload length: versioned_hash || z || y || commitment || proof. -/
def inputLength : Nat := 192

def versionedHashOffset : Nat := 0
def zOffset : Nat := 32
def yOffset : Nat := 64
def commitmentOffset : Nat := 96
def proofOffset : Nat := 144

/-- Total byte-length validation from execution-specs `if len(data) != 192`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length == inputLength

/-- Safe byte projection; callers pair it with `validInputLength`. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- The versioned hash is the first 32 bytes of the KZG point-evaluation payload. -/
def versionedHash (payload : List Byte) : Bytes32 :=
  fun i => payloadByte payload (versionedHashOffset + i.val)

/-- Commitment bytes from the execution-specs payload slice `data[96:144]`. -/
def commitmentBytes (payload : List Byte) : KzgPointEvalInputBridge.Bytes48 :=
  fun i => payloadByte payload (commitmentOffset + i.val)

/-- Field element `z` from the execution-specs payload slice `data[32:64]`. -/
def zBytes (payload : List Byte) : Bytes32 :=
  fun i => payloadByte payload (zOffset + i.val)

/-- Field element `y` from the execution-specs payload slice `data[64:96]`. -/
def yBytes (payload : List Byte) : Bytes32 :=
  fun i => payloadByte payload (yOffset + i.val)

/-- Proof bytes from the execution-specs payload slice `data[144:192]`. -/
def proofBytes (payload : List Byte) : KzgPointEvalInputBridge.Bytes48 :=
  fun i => payloadByte payload (proofOffset + i.val)

/-- Accelerator input extracted from EVM call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { commitment := commitmentBytes payload
    z := zBytes payload
    y := yBytes payload
    proof := proofBytes payload }

/-- Fixed EIP-4844 point-evaluation precompile gas cost. -/
def gasCost (_payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .pointEvaluation inputLength |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure KZG point-evaluation precompile dispatch.

The execution-specs order is: exact 192-byte length check, fixed 50,000 gas
charge, versioned-hash validation, accelerator proof verification, and finally
64-byte success output only when the proof verifies.
-/
def dispatch
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .pointEvaluation then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        let accInput := acceleratorInput input.input
        if _h_hash : versionedHashIsValid (versionedHash input.input) accInput then
          let request := KzgPointEvalEcallBridge.requestFromInput accInput
          let result := KzgPointEvalEcallBridge.executeKzgPointEvalEcall accelerator request
          KzgPointEvalPrecompileResultBridge.fromPointEvalResult (input.gas - cost) result
        else
          EvmAsm.Evm64.PrecompileResult.fail (input.gas - cost)
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_fixed (payload : List Byte) :
    gasCost payload = 50000 := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem validInputLength_iff (payload : List Byte) :
    validInputLength payload = true <-> payload.length = inputLength := by
  simp [validInputLength]

theorem versionedHash_apply (payload : List Byte) (i : Fin 32) :
    versionedHash payload i = payload.getD i.val 0 := by
  simp [versionedHash, payloadByte, versionedHashOffset]

theorem acceleratorInput_commitment (payload : List Byte) :
    (acceleratorInput payload).commitment = commitmentBytes payload := rfl

theorem acceleratorInput_z (payload : List Byte) :
    (acceleratorInput payload).z = zBytes payload := rfl

theorem acceleratorInput_y (payload : List Byte) :
    (acceleratorInput payload).y = yBytes payload := rfl

theorem acceleratorInput_proof (payload : List Byte) :
    (acceleratorInput payload).proof = proofBytes payload := rfl

theorem dispatch_non_pointEvaluation
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .pointEvaluation) :
    dispatch versionedHashIsValid accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .pointEvaluation)
    (h_len : validInputLength input.input = false) :
    dispatch versionedHashIsValid accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .pointEvaluation)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch versionedHashIsValid accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_invalid_versioned_hash
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .pointEvaluation)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_hash : versionedHashIsValid (versionedHash input.input) (acceleratorInput input.input) = false) :
    dispatch versionedHashIsValid accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_hash]

theorem dispatch_success
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .pointEvaluation)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_hash : versionedHashIsValid (versionedHash input.input) (acceleratorInput input.input) = true)
    (h_status : (accelerator (acceleratorInput input.input)).status = EvmAsm.Accelerators.ZkvmStatus.eok)
    (h_verified : (accelerator (acceleratorInput input.input)).output.verified = true) :
    dispatch versionedHashIsValid accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        KzgPointEvalPrecompileResultBridge.successOutputBytes
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_hash,
    KzgPointEvalEcallBridge.requestFromInput,
    KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    KzgPointEvalPrecompileResultBridge.fromPointEvalResult,
    h_status, h_verified]

theorem dispatch_success_output_length
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .pointEvaluation)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_hash : versionedHashIsValid (versionedHash input.input) (acceleratorInput input.input) = true)
    (h_status : (accelerator (acceleratorInput input.input)).status = EvmAsm.Accelerators.ZkvmStatus.eok)
    (h_verified : (accelerator (acceleratorInput input.input)).output.verified = true) :
    (dispatch versionedHashIsValid accelerator input).output.length = 64 := by
  rw [dispatch_success versionedHashIsValid accelerator h_target h_len h_gas h_hash h_status h_verified]
  simp [KzgPointEvalPrecompileResultBridge.successOutputBytes_length]

theorem dispatch_unverified_failure
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .pointEvaluation)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_hash : versionedHashIsValid (versionedHash input.input) (acceleratorInput input.input) = true)
    (h_status : (accelerator (acceleratorInput input.input)).status = EvmAsm.Accelerators.ZkvmStatus.eok)
    (h_verified : (accelerator (acceleratorInput input.input)).output.verified = false) :
    dispatch versionedHashIsValid accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_hash,
    KzgPointEvalEcallBridge.requestFromInput,
    KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    KzgPointEvalPrecompileResultBridge.fromPointEvalResult,
    h_status, h_verified]

theorem dispatch_efail_failure
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .pointEvaluation)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_hash : versionedHashIsValid (versionedHash input.input) (acceleratorInput input.input) = true)
    (h_status : (accelerator (acceleratorInput input.input)).status = EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch versionedHashIsValid accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_hash,
    KzgPointEvalEcallBridge.requestFromInput,
    KzgPointEvalEcallBridge.executeKzgPointEvalEcall,
    KzgPointEvalPrecompileResultBridge.fromPointEvalResult,
    h_status]

theorem dispatch_preservesGasBound
    (versionedHashIsValid : Bytes32 -> AcceleratorInput -> Bool)
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch versionedHashIsValid accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .pointEvaluation
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        by_cases h_hash : versionedHashIsValid (versionedHash input.input)
            (acceleratorInput input.input)
        · simp only [h_hash, ↓reduceDIte]
          cases h_status : (KzgPointEvalEcallBridge.executeKzgPointEvalEcall accelerator
            (KzgPointEvalEcallBridge.requestFromInput
              (acceleratorInput input.input))).status
          · cases h_verified : (KzgPointEvalEcallBridge.executeKzgPointEvalEcall accelerator
                (KzgPointEvalEcallBridge.requestFromInput
                  (acceleratorInput input.input))).output.verified <;>
              simp [KzgPointEvalPrecompileResultBridge.fromPointEvalResult, h_status,
                h_verified, EvmAsm.Evm64.PrecompileResult.ok,
                EvmAsm.Evm64.PrecompileResult.fail]
          · simp [KzgPointEvalPrecompileResultBridge.fromPointEvalResult, h_status,
              EvmAsm.Evm64.PrecompileResult.fail]
        · simp [h_hash, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end KzgPointEvalPrecompileDispatch

end EvmAsm.EL
