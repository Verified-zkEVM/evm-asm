/-
  EvmAsm.EL.Bls12MapFp2ToG2PrecompileDispatch

  Pure EVM BLS12-381 map-Fp2-to-G2 precompile framing. Field validation and
  map-to-curve arithmetic are supplied by the accelerator boundary; this module
  fixes the execution-specs-visible target, exact length, fixed gas, input
  slicing, and common precompile result shape.
-/

import EvmAsm.EL.Bls12MapPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12MapFp2ToG2PrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev AcceleratorInput := Bls12MapFp2ToG2InputBridge.AcceleratorInput
abbrev AcceleratorResult := Bls12MapFp2ToG2ResultBridge.AcceleratorResult

/-- BLS12 map-Fp2-to-G2 consumes exactly one 128-byte Fp2 element. -/
def inputLength : Nat := 128

/-- The accelerator bridge stores BLS12-381 Fp2 elements as 96-byte payloads. -/
def acceleratorFieldLength : Nat := 96

/-- Safe byte projection. Invalid short inputs are rejected before this is used. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Offset of a compact 96-byte Fp2 payload inside a 128-byte EVM Fp2 field. -/
def compactFp2Offset (i : Nat) : Nat :=
  if i < 48 then 16 + i else 32 + i

/-- Execution-specs length check: `if len(data) != 128`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length == inputLength

/-- Fp2 element bytes passed to the accelerator boundary. -/
def fp2Bytes (payload : List Byte) : Bls12MapFp2ToG2InputBridge.Fp2Bytes :=
  fun i => payloadByte payload (compactFp2Offset i.val)

/-- Accelerator input extracted from EVM call data. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { fp2 := fp2Bytes payload }

/-- Fixed Osaka BLS12 map-Fp2-to-G2 precompile gas cost. -/
def gasCost (_payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .bls12MapFp2ToG2 inputLength |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BLS12 map-Fp2-to-G2 precompile dispatch.

Execution-specs rejects bad length before charging gas. Valid-length inputs
charge fixed gas and then the accelerator boundary handles field validation and
map-to-curve arithmetic.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bls12MapFp2ToG2 then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        let request := Bls12MapFp2ToG2EcallBridge.requestFromInput (acceleratorInput input.input)
        let result := Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall accelerator request
        Bls12MapPrecompileResultBridge.fromMapFp2ToG2Result (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_fixed (payload : List Byte) :
    gasCost payload = 23800 := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem validInputLength_iff (payload : List Byte) :
    validInputLength payload = true <-> payload.length = inputLength := by
  simp [validInputLength]

theorem fp2Bytes_apply (payload : List Byte) (i : Fin 96) :
    fp2Bytes payload i = payload.getD (compactFp2Offset i.val) 0 := by
  simp [fp2Bytes, payloadByte]

theorem acceleratorInput_fp2 (payload : List Byte) :
    (acceleratorInput payload).fp2 = fp2Bytes payload := rfl

theorem dispatch_non_bls12MapFp2ToG2
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bls12MapFp2ToG2) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFp2ToG2)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFp2ToG2)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFp2ToG2)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bls12MapPrecompileResultBridge.mapFp2ToG2OutputBytes
          (Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall accelerator
            (Bls12MapFp2ToG2EcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12MapFp2ToG2EcallBridge.requestFromInput,
    Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
    Bls12MapPrecompileResultBridge.fromMapFp2ToG2Result,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFp2ToG2)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 256 := by
  rw [dispatch_success accelerator h_target h_len h_gas h_status]
  simp [Bls12MapPrecompileResultBridge.mapFp2ToG2OutputBytes_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12MapFp2ToG2)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12MapFp2ToG2EcallBridge.requestFromInput,
    Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall,
    Bls12MapPrecompileResultBridge.fromMapFp2ToG2Result,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bls12MapFp2ToG2
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        cases h_status : (Bls12MapFp2ToG2EcallBridge.executeBls12MapFp2ToG2Ecall accelerator
          (Bls12MapFp2ToG2EcallBridge.requestFromInput
            (acceleratorInput input.input))).status <;>
          simp [Bls12MapPrecompileResultBridge.fromMapFp2ToG2Result, h_status,
            EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bls12MapFp2ToG2PrecompileDispatch

end EvmAsm.EL
