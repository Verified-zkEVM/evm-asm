/-
  EvmAsm.EL.Sha256PrecompileDispatch

  Pure EVM SHA256 precompile framing. The digest computation is supplied by
  the zkVM SHA256 accelerator boundary; this module fixes the target check,
  word-linear gas charge, accelerator input, and shared precompile result shape.
-/

import EvmAsm.EL.Sha256PrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Sha256PrecompileDispatch

abbrev Byte := EvmAsm.EL.Byte

def acceleratorInput (payload : List Byte) : Sha256InputBridge.AcceleratorInput :=
  { bytes := payload }

def gasCost (payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .sha256 payload.length |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/--
Pure SHA256 precompile dispatch.

SHA256 has no payload-length validity condition: all byte strings are accepted,
with gas `60 + 12 * ceil(len / 32)` charged before the accelerator result is
mapped to the common precompile result surface.
-/
def dispatch
    (accelerator : Sha256InputBridge.AcceleratorInput ->
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .sha256 then
    let cost := gasCost input.input
    if _h_gas : cost <= input.gas then
      let request := Sha256EcallBridge.requestFromInput (acceleratorInput input.input)
      let result := Sha256EcallBridge.executeSha256Ecall accelerator request
      Sha256PrecompileResultBridge.fromSha256Result (input.gas - cost) result
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem acceleratorInput_bytes (payload : List Byte) :
    (acceleratorInput payload).bytes = payload := rfl

theorem gasCost_eq_precompileGasCost (payload : List Byte) :
    gasCost payload = 60 + 12 * EvmAsm.Evm64.Precompile.inputWords payload.length := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem gasCost_empty : gasCost ([] : List Byte) = 60 := by
  rw [gasCost_eq_precompileGasCost]
  simp [EvmAsm.Evm64.Precompile.inputWords_zero]

theorem dispatch_non_sha256
    (accelerator : Sha256InputBridge.AcceleratorInput ->
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .sha256) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_out_of_gas
    (accelerator : Sha256InputBridge.AcceleratorInput ->
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .sha256)
    (h_gas : input.gas < gasCost input.input) :
    dispatch accelerator input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_not]

theorem dispatch_success
    (accelerator : Sha256InputBridge.AcceleratorInput ->
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .sha256)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).1 =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    dispatch accelerator input =
      EvmAsm.Evm64.PrecompileResult.ok
        (Sha256ResultBridge.hashBytesList
          (accelerator (acceleratorInput input.input)).2.hash)
        (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas,
    Sha256EcallBridge.requestFromInput,
    Sha256EcallBridge.executeSha256Ecall,
    Sha256PrecompileResultBridge.fromSha256Result,
    Sha256PrecompileResultBridge.outputBytesFromResult, h_status]

theorem dispatch_success_output_length
    (accelerator : Sha256InputBridge.AcceleratorInput ->
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .sha256)
    (h_gas : gasCost input.input <= input.gas)
    (h_status : (accelerator (acceleratorInput input.input)).1 =
      EvmAsm.Accelerators.ZkvmStatus.eok) :
    (dispatch accelerator input).output.length = 32 := by
  rw [dispatch_success accelerator h_target h_gas h_status]
  simp [Sha256ResultBridge.hashBytesList_length]

theorem dispatch_preservesGasBound
    (accelerator : Sha256InputBridge.AcceleratorInput ->
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch accelerator input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .sha256
  · simp only [h_target, ↓reduceDIte]
    by_cases h_gas : gasCost input.input <= input.gas
    · simp only [h_gas, ↓reduceDIte]
      cases h_status : (Sha256EcallBridge.executeSha256Ecall accelerator
        (Sha256EcallBridge.requestFromInput
          (acceleratorInput input.input))).status <;>
        simp [Sha256PrecompileResultBridge.fromSha256Result, h_status,
          EvmAsm.Evm64.PrecompileResult.ok, EvmAsm.Evm64.PrecompileResult.fail]
    · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end Sha256PrecompileDispatch

end EvmAsm.EL
