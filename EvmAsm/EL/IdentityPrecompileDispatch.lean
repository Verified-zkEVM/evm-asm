/-
  EvmAsm.EL.IdentityPrecompileDispatch

  Pure EVM IDENTITY precompile framing. This module fixes the target check,
  word-linear gas charge, and shared precompile result shape for address 0x04.
-/

import EvmAsm.EL.IdentityPrecompileResultBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace IdentityPrecompileDispatch

abbrev Byte := BitVec 8

def gasCost (payload : List Byte) : Nat :=
  EvmAsm.Evm64.Precompile.precompileGasCost? .identity payload.length |>.getD 0

def affordable (input : EvmAsm.Evm64.PrecompileInput) : Prop :=
  gasCost input.input <= input.gas

/-- Pure IDENTITY precompile dispatch. -/
def dispatch (input : EvmAsm.Evm64.PrecompileInput) : EvmAsm.Evm64.PrecompileResult :=
  if _h_target : input.target = .identity then
    let cost := gasCost input.input
    if _h_gas : cost <= input.gas then
      IdentityPrecompileResultBridge.fromIdentityInput (input.gas - cost) input
    else
      EvmAsm.Evm64.PrecompileResult.fail input.gas
  else
    EvmAsm.Evm64.PrecompileResult.fail input.gas

theorem gasCost_eq_precompileGasCost (payload : List Byte) :
    gasCost payload = 15 + 3 * EvmAsm.Evm64.Precompile.inputWords payload.length := by
  simp [gasCost, EvmAsm.Evm64.Precompile.precompileGasCost?,
    EvmAsm.Evm64.Precompile.gasSchedule]

theorem gasCost_empty : gasCost ([] : List Byte) = 15 := by
  rw [gasCost_eq_precompileGasCost]
  simp [EvmAsm.Evm64.Precompile.inputWords_zero]

theorem dispatch_non_identity
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target ≠ .identity) :
    dispatch input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  simp [dispatch, h_target]

theorem dispatch_out_of_gas
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .identity)
    (h_gas : input.gas < gasCost input.input) :
    dispatch input = EvmAsm.Evm64.PrecompileResult.fail input.gas := by
  have h_not : ¬ gasCost input.input <= input.gas := Nat.not_le.mpr h_gas
  simp [dispatch, h_target, h_not]

theorem dispatch_success
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .identity)
    (h_gas : gasCost input.input <= input.gas) :
    dispatch input =
      EvmAsm.Evm64.PrecompileResult.ok input.input (input.gas - gasCost input.input) := by
  simp [dispatch, h_target, h_gas,
    IdentityPrecompileResultBridge.fromIdentityInput,
    IdentityPrecompileResultBridge.outputBytesFromInput]

theorem dispatch_success_output
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .identity)
    (h_gas : gasCost input.input <= input.gas) :
    (dispatch input).output = input.input := by
  rw [dispatch_success h_target h_gas]
  rfl

theorem dispatch_success_output_length
    {input : EvmAsm.Evm64.PrecompileInput}
    (h_target : input.target = .identity)
    (h_gas : gasCost input.input <= input.gas) :
    (dispatch input).output.length = input.input.length := by
  rw [dispatch_success_output h_target h_gas]

theorem dispatch_preservesGasBound
    (input : EvmAsm.Evm64.PrecompileInput) :
    (dispatch input).gasRemaining <= input.gas := by
  unfold dispatch
  by_cases h_target : input.target = .identity
  · simp only [h_target, ↓reduceDIte]
    by_cases h_gas : gasCost input.input <= input.gas
    · simp [h_gas, IdentityPrecompileResultBridge.fromIdentityInput,
        EvmAsm.Evm64.PrecompileResult.ok]
    · simp [h_gas, EvmAsm.Evm64.PrecompileResult.fail]
  · simp [h_target, EvmAsm.Evm64.PrecompileResult.fail]

end IdentityPrecompileDispatch

end EvmAsm.EL
