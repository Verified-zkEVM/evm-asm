/-
  EvmAsm.EL.ModexpPrecompileResultBridge

  Bridge from MODEXP accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.ModexpEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace ModexpPrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

def outputBytesFromResult (result : ModexpEcallBridge.ModexpResult) : List Byte :=
  result.output.bytes

def fromModexpResult
    (gasRemaining : Nat) (result : ModexpEcallBridge.ModexpResult) : PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromResult result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def gasRemainingAfterCost (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) : Nat :=
  input.gas - cost

theorem outputBytesFromResult_eq (result : ModexpEcallBridge.ModexpResult) :
    outputBytesFromResult result = result.output.bytes := rfl

theorem outputBytesFromResult_length (result : ModexpEcallBridge.ModexpResult) :
    (outputBytesFromResult result).length = result.output.bytes.length := rfl

theorem outputBytesFromResult_nil
    {result : ModexpEcallBridge.ModexpResult} (h_bytes : result.output.bytes = []) :
    outputBytesFromResult result = [] := by
  rw [outputBytesFromResult_eq, h_bytes]

theorem fromModexpResult_eok
    {gasRemaining : Nat} {result : ModexpEcallBridge.ModexpResult}
    (h_status : result.status = .eok) :
    fromModexpResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromResult result) gasRemaining := by
  simp [fromModexpResult, h_status]

theorem fromModexpResult_efail
    {gasRemaining : Nat} {result : ModexpEcallBridge.ModexpResult}
    (h_status : result.status = .efail) :
    fromModexpResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromModexpResult, h_status]

theorem fromModexpResult_output_eq
    {gasRemaining : Nat} {result : ModexpEcallBridge.ModexpResult}
    (h_status : result.status = .eok) :
    (fromModexpResult gasRemaining result).output = outputBytesFromResult result := by
  rw [fromModexpResult_eok h_status]
  rfl

theorem fromModexpResult_output_length
    {gasRemaining : Nat} {result : ModexpEcallBridge.ModexpResult}
    (h_status : result.status = .eok) :
    (fromModexpResult gasRemaining result).output.length = result.output.bytes.length := by
  rw [fromModexpResult_output_eq h_status]
  rfl

@[simp] theorem fromModexpResult_failure_output_length
    {gasRemaining : Nat} {result : ModexpEcallBridge.ModexpResult}
    (h_status : result.status = .efail) :
    (fromModexpResult gasRemaining result).output.length = 0 := by
  rw [fromModexpResult_efail h_status]
  rfl

theorem fromModexpResult_empty_success_output_length
    {gasRemaining : Nat} {result : ModexpEcallBridge.ModexpResult}
    (h_status : result.status = .eok) (h_bytes : result.output.bytes = []) :
    (fromModexpResult gasRemaining result).output.length = 0 := by
  rw [fromModexpResult_output_length h_status, h_bytes]
  rfl

theorem gasRemainingAfterCost_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromModexpResult_gasRemaining
    (gasRemaining : Nat) (result : ModexpEcallBridge.ModexpResult) :
    (fromModexpResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromModexpResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end ModexpPrecompileResultBridge

end EvmAsm.EL
