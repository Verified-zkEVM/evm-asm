/-
  EvmAsm.EL.ModexpPrecompileDispatch

  Pure EVM MODEXP precompile framing for Osaka. Modular exponentiation itself
  is supplied by the accelerator boundary; this module fixes the
  execution-specs-visible target, length caps, gas calculation, input slicing,
  and common precompile result shape.
-/

import EvmAsm.EL.ModexpPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace ModexpPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev AcceleratorInput := ModexpInputBridge.AcceleratorInput
abbrev AcceleratorResult := ModexpResultBridge.AcceleratorResult

/-- Osaka/EIP-7823 maximum byte length for base, exponent, and modulus. -/
def maxComponentLength : Nat := 1024

/-- MODEXP call-data header size: base length, exponent length, modulus length. -/
def headerLength : Nat := 96

/-- Safe EVM `buffer_read(data, start, size)` with zero padding. -/
def bufferRead (payload : List Byte) (start size : Nat) : List Byte :=
  (List.range size).map fun i => payload.getD (start + i) 0

/-- Decode a big-endian unsigned integer from a byte list. -/
def natFromBytesBE (bytes : List Byte) : Nat :=
  EvmAsm.EL.RLP.Nat.fromBytesBE bytes

/-- Read one 32-byte big-endian MODEXP length field. -/
def readLength (payload : List Byte) (offset : Nat) : Nat :=
  natFromBytesBE (bufferRead payload offset 32)

def baseLength (payload : List Byte) : Nat :=
  readLength payload 0

def exponentLength (payload : List Byte) : Nat :=
  readLength payload 32

def modulusLength (payload : List Byte) : Nat :=
  readLength payload 64

def exponentStart (payload : List Byte) : Nat :=
  headerLength + baseLength payload

def modulusStart (payload : List Byte) : Nat :=
  exponentStart payload + exponentLength payload

def exponentHead (payload : List Byte) : Nat :=
  natFromBytesBE (bufferRead payload (exponentStart payload) (min 32 (exponentLength payload)))

/-- EIP-2565/Osaka multiplication complexity. -/
def complexity (baseLen modulusLen : Nat) : Nat :=
  let maxLen := max baseLen modulusLen
  let words := (maxLen + 7) / 8
  if maxLen > 32 then 2 * words * words else 16

/-- EIP-2565/Osaka adjusted exponent iteration count. -/
def iterations (exponentLen exponentHead : Nat) : Nat :=
  let count :=
    if exponentLen <= 32 && exponentHead == 0 then
      0
    else if exponentLen <= 32 then
      exponentHead.log2
    else
      16 * (exponentLen - 32) + exponentHead.log2
  max count 1

/-- Osaka MODEXP gas cost from execution-specs `modexp.gas_cost`. -/
def modexpGasCost (baseLen modulusLen exponentLen exponentHead : Nat) : Nat :=
  max 500 (complexity baseLen modulusLen * iterations exponentLen exponentHead)

def gasCost (payload : List Byte) : Nat :=
  modexpGasCost (baseLength payload) (modulusLength payload)
    (exponentLength payload) (exponentHead payload)

/-- Osaka/EIP-7823 pre-gas component-length cap. -/
def componentLengthsValid (payload : List Byte) : Bool :=
  baseLength payload <= maxComponentLength &&
  exponentLength payload <= maxComponentLength &&
  modulusLength payload <= maxComponentLength

/-- Accelerator input extracted from MODEXP call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { base := bufferRead payload headerLength (baseLength payload)
    exp := bufferRead payload (exponentStart payload) (exponentLength payload)
    modulus := bufferRead payload (modulusStart payload) (modulusLength payload) }

def zeroBaseAndModulus (payload : List Byte) : Bool :=
  baseLength payload == 0 && modulusLength payload == 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure MODEXP precompile dispatch.

Osaka rejects component lengths above 1024 before charging gas. Otherwise it
charges the decoded MODEXP gas, returns empty output for the zero-base and
zero-modulus shortcut, or delegates the modular exponentiation to the
accelerator boundary.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .modexp then
    if _h_len : componentLengthsValid input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        if _h_zero : zeroBaseAndModulus input.input then
          EvmAsm.Evm64.PrecompileResult.ok [] (input.gas - cost)
        else
          let request := ModexpEcallBridge.requestFromInput (acceleratorInput input.input)
          let result := ModexpEcallBridge.executeModexpEcall accelerator request
          ModexpPrecompileResultBridge.fromModexpResult (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem bufferRead_length (payload : List Byte) (start size : Nat) :
    (bufferRead payload start size).length = size := by
  simp [bufferRead]

theorem bufferRead_zero (payload : List Byte) (start : Nat) :
    bufferRead payload start 0 = [] := rfl

theorem acceleratorInput_base_length (payload : List Byte) :
    (acceleratorInput payload).base.length = baseLength payload := by
  simp [acceleratorInput, bufferRead_length]

theorem acceleratorInput_exp_length (payload : List Byte) :
    (acceleratorInput payload).exp.length = exponentLength payload := by
  simp [acceleratorInput, bufferRead_length]

theorem acceleratorInput_modulus_length (payload : List Byte) :
    (acceleratorInput payload).modulus.length = modulusLength payload := by
  simp [acceleratorInput, bufferRead_length]

theorem modexpGasCost_minimum (baseLen modulusLen exponentLen exponentHead : Nat) :
    500 <= modexpGasCost baseLen modulusLen exponentLen exponentHead := by
  simp [modexpGasCost]

theorem gasCost_minimum (payload : List Byte) :
    500 <= gasCost payload := by
  simp [gasCost, modexpGasCost_minimum]

theorem dispatch_non_modexp
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .modexp) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_component_lengths
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .modexp)
    (h_len : componentLengthsValid input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .modexp)
    (h_len : componentLengthsValid input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_zero_base_zero_modulus
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .modexp)
    (h_len : componentLengthsValid input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_zero : zeroBaseAndModulus input.input = true) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok [] (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_zero]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .modexp)
    (h_len : componentLengthsValid input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_zero : zeroBaseAndModulus input.input = false)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (ModexpPrecompileResultBridge.outputBytesFromResult
          (ModexpEcallBridge.executeModexpEcall accelerator
            (ModexpEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_zero,
    ModexpEcallBridge.requestFromInput,
    ModexpEcallBridge.executeModexpEcall,
    ModexpPrecompileResultBridge.fromModexpResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .modexp)
    (h_len : componentLengthsValid input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_zero : zeroBaseAndModulus input.input = false)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length =
      (accelerator (acceleratorInput input.input)).output.bytes.length := by
  rw [dispatch_success accelerator h_target h_len h_gas h_zero h_status]
  simp [ModexpPrecompileResultBridge.outputBytesFromResult_length,
    ModexpEcallBridge.executeModexpEcall,
    ModexpEcallBridge.requestFromInput]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .modexp)
    (h_len : componentLengthsValid input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_zero : zeroBaseAndModulus input.input = false)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas, h_zero,
    ModexpEcallBridge.requestFromInput,
    ModexpEcallBridge.executeModexpEcall,
    ModexpPrecompileResultBridge.fromModexpResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .modexp
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : componentLengthsValid input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        by_cases h_zero : zeroBaseAndModulus input.input
        · simp [h_zero, EvmAsm.Evm64.PrecompileResult.ok]
        · simp only [h_zero]
          cases h_status : (ModexpEcallBridge.executeModexpEcall accelerator
            (ModexpEcallBridge.requestFromInput
              (acceleratorInput input.input))).status <;>
            simp [ModexpPrecompileResultBridge.fromModexpResult, h_status,
              EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end ModexpPrecompileDispatch

end EvmAsm.EL
