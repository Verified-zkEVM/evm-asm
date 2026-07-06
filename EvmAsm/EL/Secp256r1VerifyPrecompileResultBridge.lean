/-
  EvmAsm.EL.Secp256r1VerifyPrecompileResultBridge

  Bridge from P256VERIFY accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Secp256r1VerifyEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Secp256r1VerifyPrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

def zeroPad31 : List Byte := List.replicate 31 0

def verifiedByte (verified : Bool) : Byte :=
  if verified then 1 else 0

/-- Execution-specs P256VERIFY output: left-padded 32-byte word `0` or `1`. -/
def verifyOutputBytes (verified : Bool) : List Byte :=
  zeroPad31 ++ [verifiedByte verified]

def outputBytesFromResult
    (result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult) : List Byte :=
  verifyOutputBytes result.output.verified

def fromVerifyResult
    (gasRemaining : Nat) (result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromResult result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def gasRemainingAfterCost (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) : Nat :=
  input.gas - cost

theorem zeroPad31_length : zeroPad31.length = 31 := by
  simp [zeroPad31]

theorem verifiedByte_true : verifiedByte true = 1 := rfl

theorem verifiedByte_false : verifiedByte false = 0 := rfl

theorem verifyOutputBytes_true :
    verifyOutputBytes true = zeroPad31 ++ [1] := rfl

theorem verifyOutputBytes_false :
    verifyOutputBytes false = zeroPad31 ++ [0] := rfl

theorem verifyOutputBytes_length (verified : Bool) :
    (verifyOutputBytes verified).length = 32 := by
  simp [verifyOutputBytes, zeroPad31_length]

theorem outputBytesFromResult_length
    (result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult) :
    (outputBytesFromResult result).length = 32 := by
  simp [outputBytesFromResult, verifyOutputBytes_length]

theorem outputBytesFromResult_true
    {result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult}
    (h_verified : result.output.verified = true) :
    outputBytesFromResult result = zeroPad31 ++ [1] := by
  simp [outputBytesFromResult, verifyOutputBytes, verifiedByte, h_verified]

theorem outputBytesFromResult_false
    {result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult}
    (h_verified : result.output.verified = false) :
    outputBytesFromResult result = zeroPad31 ++ [0] := by
  simp [outputBytesFromResult, verifyOutputBytes, verifiedByte, h_verified]

theorem fromVerifyResult_eok
    {gasRemaining : Nat} {result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult}
    (h_status : result.status = .eok) :
    fromVerifyResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromResult result) gasRemaining := by
  simp [fromVerifyResult, h_status]

theorem fromVerifyResult_efail
    {gasRemaining : Nat} {result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult}
    (h_status : result.status = .efail) :
    fromVerifyResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromVerifyResult, h_status]

theorem fromVerifyResult_output_length
    {gasRemaining : Nat} {result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult}
    (h_status : result.status = .eok) :
    (fromVerifyResult gasRemaining result).output.length = 32 := by
  rw [fromVerifyResult_eok h_status]
  simp [outputBytesFromResult_length]

@[simp] theorem fromVerifyResult_failure_output_length
    {gasRemaining : Nat} {result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult}
    (h_status : result.status = .efail) :
    (fromVerifyResult gasRemaining result).output.length = 0 := by
  rw [fromVerifyResult_efail h_status]
  rfl

theorem gasRemainingAfterCost_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromVerifyResult_gasRemaining
    (gasRemaining : Nat) (result : Secp256r1VerifyEcallBridge.Secp256r1VerifyResult) :
    (fromVerifyResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromVerifyResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end Secp256r1VerifyPrecompileResultBridge

end EvmAsm.EL
