/-
  EvmAsm.EL.Blake2fPrecompileResultBridge

  Bridge from the zkVM BLAKE2F accelerator ECALL result to the shared EVM
  precompile result surface used by CALL/STATICCALL plumbing.
-/

import EvmAsm.EL.Blake2fEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Blake2fPrecompileResultBridge

abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult
abbrev Blake2fResult := Blake2fEcallBridge.Blake2fResult

def outputBytes (result : Blake2fResult) : List Byte :=
  Blake2fEcallBridge.outputBytesList result

/-- Distinctive token: Blake2fPrecompileResultBridge.toPrecompileResult. -/
def toPrecompileResult (gasRemaining : Nat) (result : Blake2fResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (outputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

theorem outputBytes_length (result : Blake2fResult) :
    (outputBytes result).length = 64 := by
  simp [outputBytes, Blake2fEcallBridge.outputBytesList,
    Blake2fResultBridge.outputBytesList_length]

theorem toPrecompileResult_eok
    {result : Blake2fResult} (gasRemaining : Nat)
    (h_status : result.status = .eok) :
    toPrecompileResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (outputBytes result) gasRemaining := by
  simp [toPrecompileResult, h_status]

theorem toPrecompileResult_efail
    {result : Blake2fResult} (gasRemaining : Nat)
    (h_status : result.status = .efail) :
    toPrecompileResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [toPrecompileResult, h_status]

theorem toPrecompileResult_status_eok
    {result : Blake2fResult} (gasRemaining : Nat)
    (h_status : result.status = .eok) :
    (toPrecompileResult gasRemaining result).status =
      EvmAsm.Evm64.PrecompileStatus.success := by
  rw [toPrecompileResult_eok gasRemaining h_status]
  rfl

theorem toPrecompileResult_status_efail
    {result : Blake2fResult} (gasRemaining : Nat)
    (h_status : result.status = .efail) :
    (toPrecompileResult gasRemaining result).status =
      EvmAsm.Evm64.PrecompileStatus.failure := by
  rw [toPrecompileResult_efail gasRemaining h_status]
  rfl

theorem toPrecompileResult_output_eok
    {result : Blake2fResult} (gasRemaining : Nat)
    (h_status : result.status = .eok) :
    (toPrecompileResult gasRemaining result).output = outputBytes result := by
  rw [toPrecompileResult_eok gasRemaining h_status]
  rfl

theorem toPrecompileResult_output_efail
    {result : Blake2fResult} (gasRemaining : Nat)
    (h_status : result.status = .efail) :
    (toPrecompileResult gasRemaining result).output = [] := by
  rw [toPrecompileResult_efail gasRemaining h_status]
  rfl

theorem toPrecompileResult_gasRemaining
    (gasRemaining : Nat) (result : Blake2fResult) :
    (toPrecompileResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;> simp [toPrecompileResult, h_status]

theorem toPrecompileResult_output_length_eok
    {result : Blake2fResult} (gasRemaining : Nat)
    (h_status : result.status = .eok) :
    (toPrecompileResult gasRemaining result).output.length = 64 := by
  rw [toPrecompileResult_output_eok gasRemaining h_status]
  exact outputBytes_length result

end Blake2fPrecompileResultBridge

end EvmAsm.EL
