/-
  EvmAsm.EL.Bn254G1MulPrecompileDispatch

  Pure EVM BN254 G1 scalar-multiplication precompile framing. Point decoding
  and multiplication are supplied by the accelerator boundary; this module
  fixes the execution-specs-visible target, fixed gas, call-data slicing, and
  common precompile result shape.
-/

import EvmAsm.EL.Bn254PrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bn254G1MulPrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte
abbrev AcceleratorInput := Bn254G1MulInputBridge.AcceleratorInput
abbrev AcceleratorResult := Bn254G1MulResultBridge.AcceleratorResult

/-- BN254 MUL reads one 64-byte G1 point and one 32-byte scalar with zero padding. -/
def inputWindowLength : Nat := 96

def pointOffset : Nat := 0
def scalarOffset : Nat := 64

/-- Safe byte projection; short calldata is zero-padded like execution-specs `buffer_read`. -/
def payloadByte (payload : List Byte) (i : Nat) : Byte :=
  payload.getD i 0

/-- G1 point from the execution-specs payload window `data[0:64]`. -/
def pointBytes (payload : List Byte) : Bn254G1MulInputBridge.G1PointBytes :=
  fun i => payloadByte payload (pointOffset + i.val)

/-- Scalar from the execution-specs payload window `data[64:96]`. -/
def scalarBytes (payload : List Byte) : Bn254G1MulInputBridge.ScalarBytes :=
  fun i => payloadByte payload (scalarOffset + i.val)

/-- Accelerator input extracted from EVM call data in execution-specs order. -/
def acceleratorInput (payload : List Byte) : AcceleratorInput :=
  { point := pointBytes payload
    scalar := scalarBytes payload }

/-- Current Istanbul-and-later BN254 MUL gas cost. -/
def gasCost (_payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .bn254Mul inputWindowLength |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure BN254 G1 MUL precompile dispatch.

Execution-specs charges fixed ECMUL gas, reads one 64-byte G1 point and one
32-byte scalar with zero-padding, then treats invalid point decoding as an
exceptional failure. The accelerator boundary supplies point validation and
multiplication.
-/
def dispatch
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .bn254Mul then
    let cost := gasCost input.input
    if _h_gas : cost <= input.gas then
      let request := Bn254G1MulEcallBridge.requestFromInput (acceleratorInput input.input)
      let result := Bn254G1MulEcallBridge.executeBn254G1MulEcall accelerator request
      Bn254PrecompileResultBridge.fromMulResult (input.gas - cost) result
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_fixed (payload : List Byte) :
    gasCost payload = 6000 := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem pointBytes_apply (payload : List Byte) (i : Fin 64) :
    pointBytes payload i = payload.getD i.val 0 := by
  simp [pointBytes, payloadByte, pointOffset]

theorem scalarBytes_apply (payload : List Byte) (i : Fin 32) :
    scalarBytes payload i = payload.getD (64 + i.val) 0 := by
  simp [scalarBytes, payloadByte, scalarOffset]

theorem acceleratorInput_point (payload : List Byte) :
    (acceleratorInput payload).point = pointBytes payload := rfl

theorem acceleratorInput_scalar (payload : List Byte) :
    (acceleratorInput payload).scalar = scalarBytes payload := rfl

theorem dispatch_non_bn254Mul
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .bn254Mul) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_out_of_gas
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Mul)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_not]

theorem dispatch_success
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Mul)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Bn254PrecompileResultBridge.mulOutputBytes
          (Bn254G1MulEcallBridge.executeBn254G1MulEcall accelerator
            (Bn254G1MulEcallBridge.requestFromInput (acceleratorInput input.input))))
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas,
    Bn254G1MulEcallBridge.requestFromInput,
    Bn254G1MulEcallBridge.executeBn254G1MulEcall,
    Bn254PrecompileResultBridge.fromMulResult,
    h_status]

theorem dispatch_success_output_length
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Mul)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 64 := by
  rw [dispatch_success accelerator h_target h_gas h_status]
  simp [Bn254PrecompileResultBridge.mulOutputBytes_length]

theorem dispatch_efail_failure
    (accelerator : AcceleratorInput -> AcceleratorResult)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .bn254Mul)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).status =
      EvmAsm.Accelerators.ZkvmStatus.efail) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.fail (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas,
    Bn254G1MulEcallBridge.requestFromInput,
    Bn254G1MulEcallBridge.executeBn254G1MulEcall,
    Bn254PrecompileResultBridge.fromMulResult,
    h_status]

theorem dispatch_preservesGasBound
    (accelerator : AcceleratorInput -> AcceleratorResult)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .bn254Mul
  · simp only [h_target, ↓reduceDIte]
    by_cases h_gas : gasCost input.input <= input.gas
    · simp only [h_gas, ↓reduceDIte]
      cases h_status : (Bn254G1MulEcallBridge.executeBn254G1MulEcall accelerator
        (Bn254G1MulEcallBridge.requestFromInput
          (acceleratorInput input.input))).status <;>
        simp [Bn254PrecompileResultBridge.fromMulResult, h_status,
          EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Bn254G1MulPrecompileDispatch

end EvmAsm.EL
