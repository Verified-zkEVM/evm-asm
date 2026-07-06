/-
  EvmAsm.EL.Bls12G2AddPrecompileDispatch

  Pure EVM BLS12-381 G2 addition precompile framing. Point validation and
  curve addition are supplied by the accelerator boundary; this module fixes
  the execution-specs-visible target, exact length, fixed gas, input slicing,
  and common precompile result shape.
-/

import EvmAsm.EL.Bls12G2PrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12G2AddPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev AcceleratorInput := Bls12G2AddInputBridge.AcceleratorInput
abbrev AcceleratorResult := Bls12G2AddResultBridge.AcceleratorResult

/-- BLS12 G2 ADD consumes exactly two 256-byte EVM G2 point encodings. -/
def inputLength : Nat := 512

/-- Each execution-specs G2 point window is 256 bytes: four padded Fp coordinates. -/
def evmPointLength : Nat := 256

/-- The accelerator bridge stores BLS12-381 G2 points as four 48-byte Fp components. -/
def acceleratorPointLength : Nat := 192

def p1Offset : Nat := 0
def p2Offset : Nat := 256

/-- Safe byte projection. Invalid short inputs are rejected before this is used. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- Offset of a compact 192-byte G2 coordinate byte inside a 256-byte EVM G2 point. -/
def compactG2Offset (i : Nat) : Nat :=
  if i < 48 then
    16 + i
  else if i < 96 then
    32 + i
  else if i < 144 then
    48 + i
  else
    64 + i

/-- Execution-specs length check: `if len(data) != 512`. -/
def validInputLength (payload : List Byte) : Bool :=
  payload.length == inputLength

/-- First accelerator G2 point, projected from the first EVM point window. -/
def p1Bytes (payload : List Byte) : Bls12G2AddInputBridge.G2PointBytes :=
  fun i => payloadByte payload (p1Offset + compactG2Offset i.val)

/-- Second accelerator G2 point, projected from the second EVM point window. -/
def p2Bytes (payload : List Byte) : Bls12G2AddInputBridge.G2PointBytes :=
  fun i => payloadByte payload (p2Offset + compactG2Offset i.val)

/-- Accelerator input extracted from EVM call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { p1 := p1Bytes payload
    p2 := p2Bytes payload }

/-- Fixed Osaka BLS12 G2 ADD precompile gas cost. -/
def gasCost (_payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .bls12G2Add inputLength |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BLS12 G2 ADD precompile dispatch.

Execution-specs rejects bad length before charging gas. Valid-length inputs
charge fixed gas and then the accelerator boundary handles point decoding,
subgroup checks, infinity handling, and addition.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bls12G2Add then
    if _h_len : validInputLength input.input then
      let cost := gasCost input.input
      if _h_gas : cost <= input.gas then
        let request := Bls12G2AddEcallBridge.requestFromInput (acceleratorInput input.input)
        let result := Bls12G2AddEcallBridge.executeBls12G2AddEcall accelerator request
        Bls12G2PrecompileResultBridge.fromAddResult (input.gas - cost) result
      else
        EvmAsm.Evm64.PrecompileResult.fail input.gas
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_fixed (payload : List Byte) :
    gasCost payload = 600 := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem validInputLength_iff (payload : List Byte) :
    validInputLength payload = true <-> payload.length = inputLength := by
  simp [validInputLength]

theorem p1Bytes_apply (payload : List Byte) (i : Fin 192) :
    p1Bytes payload i = payload.getD (compactG2Offset i.val) 0 := by
  simp [p1Bytes, payloadByte, p1Offset]

theorem p2Bytes_apply (payload : List Byte) (i : Fin 192) :
    p2Bytes payload i = payload.getD (256 + compactG2Offset i.val) 0 := by
  simp [p2Bytes, payloadByte, p2Offset]

theorem acceleratorInput_p1 (payload : List Byte) :
    (acceleratorInput payload).p1 = p1Bytes payload := rfl

theorem acceleratorInput_p2 (payload : List Byte) :
    (acceleratorInput payload).p2 = p2Bytes payload := rfl

theorem dispatch_non_bls12G2Add
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bls12G2Add) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_invalid_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Add)
    (h_len : validInputLength input.input = false) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target, h_len]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Add)
    (h_len : validInputLength input.input = true)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_len, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Add)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bls12G2PrecompileResultBridge.addOutputBytes
          (Bls12G2AddEcallBridge.executeBls12G2AddEcall accelerator
            (Bls12G2AddEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12G2AddEcallBridge.requestFromInput,
    Bls12G2AddEcallBridge.executeBls12G2AddEcall,
    Bls12G2PrecompileResultBridge.fromAddResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Add)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 256 := by
  rw [dispatch_success accelerator h_target h_len h_gas h_status]
  simp [Bls12G2PrecompileResultBridge.addOutputBytes_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bls12G2Add)
    (h_len : validInputLength input.input = true)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_len, h_gas,
    Bls12G2AddEcallBridge.requestFromInput,
    Bls12G2AddEcallBridge.executeBls12G2AddEcall,
    Bls12G2PrecompileResultBridge.fromAddResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bls12G2Add
  · simp only [h_target, ↓reduceDIte]
    by_cases h_len : validInputLength input.input
    · simp only [h_len, ↓reduceDIte]
      by_cases h_gas : gasCost input.input <= input.gas
      · simp only [h_gas, ↓reduceDIte]
        cases h_status : (Bls12G2AddEcallBridge.executeBls12G2AddEcall accelerator
          (Bls12G2AddEcallBridge.requestFromInput
            (acceleratorInput input.input))).status <;>
          simp [Bls12G2PrecompileResultBridge.fromAddResult, h_status,
            EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
      · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_len, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bls12G2AddPrecompileDispatch

end EvmAsm.EL
