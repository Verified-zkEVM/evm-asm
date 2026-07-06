/-
  EvmAsm.EL.Bls12MapFpToG1PrecompileDispatch

  Pure EVM BLS12-381 map-Fp-to-G1 precompile framing. Field validation and
  map-to-curve arithmetic are supplied by the accelerator boundary; this module
  fixes the execution-specs-visible target, exact length, fixed gas, input
  slicing, and common precompile result shape.
-/

import EvmAsm.EL.Bls12MapPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12MapFpToG1PrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev AcceleratorInput := Bls12MapFpToG1InputBridge.AcceleratorInput
abbrev AcceleratorResult := Bls12MapFpToG1ResultBridge.AcceleratorResult

/-- BLS12 map-Fp-to-G1 consumes exactly one 64-byte Fp element. -/
def inputLength : Nat := 64

/-- The accelerator bridge stores BLS12-381 Fp elements as 48-byte payloads. -/
def acceleratorFieldLength : Nat := 48

/-- Safe byte projection. Invalid short inputs are rejected before this is used. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Offset of a compact 48-byte Fp payload inside a 64-byte EVM Fp field. -/
def compactFpOffset (i : Nat) : Nat :=
  16 + i

/-- Execution-specs length check: `if len(data) != 64`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length == inputLength

/-- Field element bytes passed to the accelerator boundary. -/
def fieldElementBytes (payload : List Byte) : Bls12MapFpToG1InputBridge.FpBytes :=
  fun i => payloadByte payload (compactFpOffset i.val)

/-- Accelerator input extracted from EVM call data. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { fieldElement := fieldElementBytes payload }

/-- Fixed Osaka BLS12 map-Fp-to-G1 precompile gas cost. -/
def gasCost (_payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .bls12MapFpToG1 inputLength |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BLS12 map-Fp-to-G1 precompile dispatch.

Execution-specs rejects bad length before charging gas. Valid-length inputs
charge fixed gas and then the accelerator boundary handles field-modulus
validation and map-to-curve arithmetic.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bls12MapFpToG1 then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        let request := Bls12MapFpToG1EcallBridge.requestFromInput (acceleratorInput input.input)
        let result := Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall accelerator request
        Bls12MapPrecompileResultBridge.fromMapFpToG1Result (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_fixed (payload : List Byte) :
    gasCost payload = 5500 := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem validInputLength_iff (payload : List Byte) :
    validInputLength payload = true <-> payload.length = inputLength := by
  simp [validInputLength]

theorem fieldElementBytes_apply (payload : List Byte) (i : Fin 48) :
    fieldElementBytes payload i = payload.getD (compactFpOffset i.val) 0 := by
  simp [fieldElementBytes, payloadByte]

theorem acceleratorInput_fieldElement (payload : List Byte) :
    (acceleratorInput payload).fieldElement = fieldElementBytes payload := rfl

theorem dispatch_non_bls12MapFpToG1
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bls12MapFpToG1) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFpToG1)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFpToG1)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFpToG1)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bls12MapPrecompileResultBridge.mapFpToG1OutputBytes
          (Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall accelerator
            (Bls12MapFpToG1EcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12MapFpToG1EcallBridge.requestFromInput,
    Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
    Bls12MapPrecompileResultBridge.fromMapFpToG1Result,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFpToG1)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 128 := by
  rw [dispatch_success accelerator h_target h_len h_gas h_status]
  simp [Bls12MapPrecompileResultBridge.mapFpToG1OutputBytes_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFpToG1)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12MapFpToG1EcallBridge.requestFromInput,
    Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall,
    Bls12MapPrecompileResultBridge.fromMapFpToG1Result,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bls12MapFpToG1
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        cases h_status : (Bls12MapFpToG1EcallBridge.executeBls12MapFpToG1Ecall accelerator
          (Bls12MapFpToG1EcallBridge.requestFromInput
            (acceleratorInput input.input))).status <;>
          simp [Bls12MapPrecompileResultBridge.fromMapFpToG1Result, h_status,
            EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bls12MapFpToG1PrecompileDispatch

end EvmAsm.EL
