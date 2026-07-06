/-
  EvmAsm.EL.Sha256PrecompileResultBridge

  Bridge from SHA256 accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Sha256EcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Sha256PrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

def outputBytesFromResult (result : Sha256EcallBridge.Sha256Result) : List Byte :=
  Sha256ResultBridge.hashBytesList result.output.hash

def fromSha256Result
    (gasRemaining : Nat) (result : Sha256EcallBridge.Sha256Result) : PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromResult result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def gasRemainingAfterCost (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) : Nat :=
  input.gas - cost

theorem outputBytesFromResult_eq (result : Sha256EcallBridge.Sha256Result) :
    outputBytesFromResult result = Sha256ResultBridge.hashBytesList result.output.hash := rfl

theorem outputBytesFromResult_length (result : Sha256EcallBridge.Sha256Result) :
    (outputBytesFromResult result).length = 32 := by
  simp [outputBytesFromResult, Sha256ResultBridge.hashBytesList_length]

theorem fromSha256Result_eok
    {gasRemaining : Nat} {result : Sha256EcallBridge.Sha256Result}
    (h_status : result.status = .eok) :
    fromSha256Result gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromResult result) gasRemaining := by
  simp [fromSha256Result, h_status]

theorem fromSha256Result_efail
    {gasRemaining : Nat} {result : Sha256EcallBridge.Sha256Result}
    (h_status : result.status = .efail) :
    fromSha256Result gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromSha256Result, h_status]

theorem fromSha256Result_output_eq
    {gasRemaining : Nat} {result : Sha256EcallBridge.Sha256Result}
    (h_status : result.status = .eok) :
    (fromSha256Result gasRemaining result).output = outputBytesFromResult result := by
  rw [fromSha256Result_eok h_status]
  rfl

theorem fromSha256Result_output_length
    {gasRemaining : Nat} {result : Sha256EcallBridge.Sha256Result}
    (h_status : result.status = .eok) :
    (fromSha256Result gasRemaining result).output.length = 32 := by
  rw [fromSha256Result_output_eq h_status]
  exact outputBytesFromResult_length result

@[simp] theorem fromSha256Result_failure_output_length
    {gasRemaining : Nat} {result : Sha256EcallBridge.Sha256Result}
    (h_status : result.status = .efail) :
    (fromSha256Result gasRemaining result).output.length = 0 := by
  rw [fromSha256Result_efail h_status]
  rfl

theorem gasRemainingAfterCost_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromSha256Result_gasRemaining
    (gasRemaining : Nat) (result : Sha256EcallBridge.Sha256Result) :
    (fromSha256Result gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromSha256Result, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end Sha256PrecompileResultBridge

end EvmAsm.EL
