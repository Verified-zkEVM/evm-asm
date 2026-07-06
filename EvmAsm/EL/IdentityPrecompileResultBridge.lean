/-
  EvmAsm.EL.IdentityPrecompileResultBridge

  Pure bridge from EVM IDENTITY precompile input to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace IdentityPrecompileResultBridge

abbrev Byte := BitVec 8
abbrev PrecompileInput := EvmAsm.Evm64.PrecompileInput
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

def outputBytesFromInput (input : PrecompileInput) : List Byte :=
  input.input

def fromIdentityInput (gasRemaining : Nat) (input : PrecompileInput) : PrecompileResult :=
  EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromInput input) gasRemaining

def gasRemainingAfterCost (input : PrecompileInput) (cost : Nat) : Nat :=
  input.gas - cost

theorem outputBytesFromInput_eq (input : PrecompileInput) :
    outputBytesFromInput input = input.input := rfl

theorem outputBytesFromInput_length (input : PrecompileInput) :
    (outputBytesFromInput input).length = input.input.length := rfl

theorem fromIdentityInput_eq_ok (gasRemaining : Nat) (input : PrecompileInput) :
    fromIdentityInput gasRemaining input =
      EvmAsm.Evm64.PrecompileResult.ok input.input gasRemaining := rfl

theorem fromIdentityInput_output (gasRemaining : Nat) (input : PrecompileInput) :
    (fromIdentityInput gasRemaining input).output = input.input := rfl

theorem fromIdentityInput_output_length (gasRemaining : Nat) (input : PrecompileInput) :
    (fromIdentityInput gasRemaining input).output.length = input.input.length := rfl

theorem fromIdentityInput_status (gasRemaining : Nat) (input : PrecompileInput) :
    (fromIdentityInput gasRemaining input).status = .success := rfl

theorem fromIdentityInput_gasRemaining (gasRemaining : Nat) (input : PrecompileInput) :
    (fromIdentityInput gasRemaining input).gasRemaining = gasRemaining := rfl

theorem gasRemainingAfterCost_le_inputGas (input : PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromIdentityInput_preservesGasBound
    {gasRemaining : Nat} {input : PrecompileInput} (h_gas : gasRemaining ≤ input.gas) :
    EvmAsm.Evm64.PrecompileResult.preservesGasBound input
      (fromIdentityInput gasRemaining input) := by
  simpa [fromIdentityInput, EvmAsm.Evm64.PrecompileResult.preservesGasBound] using h_gas

end IdentityPrecompileResultBridge

end EvmAsm.EL
