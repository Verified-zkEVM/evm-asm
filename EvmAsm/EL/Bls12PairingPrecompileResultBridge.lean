/-
  EvmAsm.EL.Bls12PairingPrecompileResultBridge

  Bridge from BLS12-381 pairing accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Bls12PairingEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12PairingPrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

def zeroPad31 : List Byte := List.replicate 31 0

def verifiedByte (verified : Bool) : Byte :=
  if verified then 1 else 0

/-- Execution-specs pairing output: left-padded 32-byte word `0` or `1`. -/
def pairingOutputBytes (verified : Bool) : List Byte :=
  zeroPad31 ++ [verifiedByte verified]

def outputBytesFromResult (result : Bls12PairingEcallBridge.Bls12PairingResult) : List Byte :=
  pairingOutputBytes result.output.verified

def fromPairingResult
    (gasRemaining : Nat) (result : Bls12PairingEcallBridge.Bls12PairingResult) :
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

theorem pairingOutputBytes_true :
    pairingOutputBytes true = zeroPad31 ++ [1] := rfl

theorem pairingOutputBytes_false :
    pairingOutputBytes false = zeroPad31 ++ [0] := rfl

theorem pairingOutputBytes_length (verified : Bool) :
    (pairingOutputBytes verified).length = 32 := by
  simp [pairingOutputBytes, zeroPad31_length]

theorem outputBytesFromResult_length
    (result : Bls12PairingEcallBridge.Bls12PairingResult) :
    (outputBytesFromResult result).length = 32 := by
  simp [outputBytesFromResult, pairingOutputBytes_length]

theorem outputBytesFromResult_true
    {result : Bls12PairingEcallBridge.Bls12PairingResult}
    (h_verified : result.output.verified = true) :
    outputBytesFromResult result = zeroPad31 ++ [1] := by
  simp [outputBytesFromResult, pairingOutputBytes, verifiedByte, h_verified]

theorem outputBytesFromResult_false
    {result : Bls12PairingEcallBridge.Bls12PairingResult}
    (h_verified : result.output.verified = false) :
    outputBytesFromResult result = zeroPad31 ++ [0] := by
  simp [outputBytesFromResult, pairingOutputBytes, verifiedByte, h_verified]

theorem fromPairingResult_eok
    {gasRemaining : Nat} {result : Bls12PairingEcallBridge.Bls12PairingResult}
    (h_status : result.status = .eok) :
    fromPairingResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (outputBytesFromResult result) gasRemaining := by
  simp [fromPairingResult, h_status]

theorem fromPairingResult_efail
    {gasRemaining : Nat} {result : Bls12PairingEcallBridge.Bls12PairingResult}
    (h_status : result.status = .efail) :
    fromPairingResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromPairingResult, h_status]

theorem fromPairingResult_output_length
    {gasRemaining : Nat} {result : Bls12PairingEcallBridge.Bls12PairingResult}
    (h_status : result.status = .eok) :
    (fromPairingResult gasRemaining result).output.length = 32 := by
  rw [fromPairingResult_eok h_status]
  simp [outputBytesFromResult_length]

@[simp] theorem fromPairingResult_failure_output_length
    {gasRemaining : Nat} {result : Bls12PairingEcallBridge.Bls12PairingResult}
    (h_status : result.status = .efail) :
    (fromPairingResult gasRemaining result).output.length = 0 := by
  rw [fromPairingResult_efail h_status]
  rfl

theorem gasRemainingAfterCost_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromPairingResult_gasRemaining
    (gasRemaining : Nat) (result : Bls12PairingEcallBridge.Bls12PairingResult) :
    (fromPairingResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromPairingResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end Bls12PairingPrecompileResultBridge

end EvmAsm.EL
