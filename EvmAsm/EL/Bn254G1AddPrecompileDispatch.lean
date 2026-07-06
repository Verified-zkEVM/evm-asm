/-
  EvmAsm.EL.Bn254G1AddPrecompileDispatch

  Pure EVM BN254 G1 addition precompile framing. Point decoding and addition
  are supplied by the accelerator boundary; this module fixes the
  execution-specs-visible target, fixed gas, call-data slicing, and common
  precompile result shape.
-/

import EvmAsm.EL.Bn254PrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bn254G1AddPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev AcceleratorInput := Bn254G1AddInputBridge.AcceleratorInput
abbrev AcceleratorOutput := Bn254G1AddResultBridge.AcceleratorOutput
abbrev AcceleratorResult := Bn254G1AddEcallBridge.Bn254G1AddResult

/-- BN254 ADD reads two 64-byte G1 points with EVM `buffer_read` zero padding. -/
def inputWindowLength : Nat := 128

def p1Offset : Nat := 0
def p2Offset : Nat := 64

/-- Safe byte projection; short calldata is zero-padded like execution-specs `buffer_read`. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- First G1 point from the execution-specs payload window `data[0:64]`. -/
def p1Bytes (payload : List Byte) : Bn254G1AddInputBridge.PointBytes :=
  fun i => payloadByte payload (p1Offset + i.val)

/-- Second G1 point from the execution-specs payload window `data[64:128]`. -/
def p2Bytes (payload : List Byte) : Bn254G1AddInputBridge.PointBytes :=
  fun i => payloadByte payload (p2Offset + i.val)

/-- Accelerator input extracted from EVM call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { p1 := p1Bytes payload
    p2 := p2Bytes payload }

/-- Current Istanbul-and-later BN254 ADD gas cost. -/
def gasCost (_payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .bn254Add inputWindowLength |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BN254 G1 ADD precompile dispatch.

Execution-specs charges fixed ECADD gas, reads two 64-byte G1 points with
zero-padding, then treats invalid point decoding as an exceptional failure. The
accelerator boundary supplies point validation and addition.
-/
def dispatch
    (accelerator : AcceleratorInput -> EvmAsm.Accelerators.ZkvmStatus × AcceleratorOutput)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bn254Add then
    let cost := gasCost input.input
    if _h_gas : cost <= input.gas then
      let request := Bn254G1AddEcallBridge.requestFromInput (acceleratorInput input.input)
      let result := Bn254G1AddEcallBridge.executeBn254G1AddEcall accelerator request
      Bn254PrecompileResultBridge.fromAddResult (input.gas - cost) result
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_fixed (payload : List Byte) :
    gasCost payload = 150 := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem p1Bytes_apply (payload : List Byte) (i : Fin 64) :
    p1Bytes payload i = payload.getD i.val 0 := by
  simp [p1Bytes, payloadByte, p1Offset]

theorem p2Bytes_apply (payload : List Byte) (i : Fin 64) :
    p2Bytes payload i = payload.getD (64 + i.val) 0 := by
  simp [p2Bytes, payloadByte, p2Offset]

theorem acceleratorInput_p1 (payload : List Byte) :
    (acceleratorInput payload).p1 = p1Bytes payload := rfl

theorem acceleratorInput_p2 (payload : List Byte) :
    (acceleratorInput payload).p2 = p2Bytes payload := rfl

theorem dispatch_non_bn254Add
    (accelerator : AcceleratorInput -> EvmAsm.Accelerators.ZkvmStatus × AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bn254Add) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> EvmAsm.Accelerators.ZkvmStatus × AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Add)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> EvmAsm.Accelerators.ZkvmStatus × AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Add)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).1 =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bn254PrecompileResultBridge.addOutputBytes
          (Bn254G1AddEcallBridge.executeBn254G1AddEcall accelerator
            (Bn254G1AddEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas,
    Bn254G1AddEcallBridge.requestFromInput,
    Bn254G1AddEcallBridge.executeBn254G1AddEcall,
    Bn254PrecompileResultBridge.fromAddResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> EvmAsm.Accelerators.ZkvmStatus × AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Add)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).1 =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 64 := by
  rw [dispatch_success accelerator h_target h_gas h_status]
  simp [Bn254PrecompileResultBridge.addOutputBytes_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> EvmAsm.Accelerators.ZkvmStatus × AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Add)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).1 =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas,
    Bn254G1AddEcallBridge.requestFromInput,
    Bn254G1AddEcallBridge.executeBn254G1AddEcall,
    Bn254PrecompileResultBridge.fromAddResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> EvmAsm.Accelerators.ZkvmStatus × AcceleratorOutput)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bn254Add
  · simp only [h_target, ↓reduceDIte]
    by_cases h_gas : gasCost input.input <= input.gas
    · simp only [h_gas, ↓reduceDIte]
      cases h_status : (Bn254G1AddEcallBridge.executeBn254G1AddEcall accelerator
        (Bn254G1AddEcallBridge.requestFromInput
          (acceleratorInput input.input))).status <;>
        simp [Bn254PrecompileResultBridge.fromAddResult, h_status,
          EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bn254G1AddPrecompileDispatch

end EvmAsm.EL
