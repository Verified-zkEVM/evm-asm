/-
  EvmAsm.EL.Bn254PrecompileResultBridge

  Bridge from BN254 accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Bn254G1AddEcallBridge
import EvmAsm.EL.Bn254G1MulEcallBridge
import EvmAsm.EL.Bn254PairingEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bn254PrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

def zeroPad31 : List Byte := List.replicate 31 0

def verifiedByte (verified : Bool) : Byte :=
  if verified then 1 else 0

/-- Execution-specs BN254 pairing output: left-padded 32-byte word `0` or `1`. -/
def pairingOutputBytes (verified : Bool) : List Byte :=
  zeroPad31 ++ [verifiedByte verified]

def addOutputBytes (result : Bn254G1AddEcallBridge.Bn254G1AddResult) : List Byte :=
  Bn254G1AddEcallBridge.outputBytesList result

def mulOutputBytes (result : Bn254G1MulEcallBridge.Bn254G1MulResult) : List Byte :=
  Bn254G1MulResultBridge.g1PointBytesList
    (Bn254G1MulEcallBridge.outputPointFromResult result)

def pairingOutputBytesFromResult
    (result : Bn254PairingEcallBridge.Bn254PairingResult) : List Byte :=
  pairingOutputBytes result.output.verified

def fromAddResult
    (gasRemaining : Nat) (result : Bn254G1AddEcallBridge.Bn254G1AddResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (addOutputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def fromMulResult
    (gasRemaining : Nat) (result : Bn254G1MulEcallBridge.Bn254G1MulResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (mulOutputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def fromPairingResult
    (gasRemaining : Nat) (result : Bn254PairingEcallBridge.Bn254PairingResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (pairingOutputBytesFromResult result) gasRemaining
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

theorem addOutputBytes_length (result : Bn254G1AddEcallBridge.Bn254G1AddResult) :
    (addOutputBytes result).length = 64 := by
  simp [addOutputBytes, Bn254G1AddEcallBridge.outputBytesList,
    Bn254G1AddResultBridge.outputBytesList_length]

theorem mulOutputBytes_length (result : Bn254G1MulEcallBridge.Bn254G1MulResult) :
    (mulOutputBytes result).length = 64 := by
  simp [mulOutputBytes, Bn254G1MulResultBridge.g1PointBytesList_length]

theorem pairingOutputBytesFromResult_length
    (result : Bn254PairingEcallBridge.Bn254PairingResult) :
    (pairingOutputBytesFromResult result).length = 32 := by
  simp [pairingOutputBytesFromResult, pairingOutputBytes_length]

theorem pairingOutputBytesFromResult_true
    {result : Bn254PairingEcallBridge.Bn254PairingResult}
    (h_verified : result.output.verified = true) :
    pairingOutputBytesFromResult result = zeroPad31 ++ [1] := by
  simp [pairingOutputBytesFromResult, pairingOutputBytes, verifiedByte, h_verified]

theorem pairingOutputBytesFromResult_false
    {result : Bn254PairingEcallBridge.Bn254PairingResult}
    (h_verified : result.output.verified = false) :
    pairingOutputBytesFromResult result = zeroPad31 ++ [0] := by
  simp [pairingOutputBytesFromResult, pairingOutputBytes, verifiedByte, h_verified]

theorem fromAddResult_eok
    {gasRemaining : Nat} {result : Bn254G1AddEcallBridge.Bn254G1AddResult}
    (h_status : result.status = .eok) :
    fromAddResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (addOutputBytes result) gasRemaining := by
  simp [fromAddResult, h_status]

theorem fromAddResult_efail
    {gasRemaining : Nat} {result : Bn254G1AddEcallBridge.Bn254G1AddResult}
    (h_status : result.status = .efail) :
    fromAddResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromAddResult, h_status]

theorem fromMulResult_eok
    {gasRemaining : Nat} {result : Bn254G1MulEcallBridge.Bn254G1MulResult}
    (h_status : result.status = .eok) :
    fromMulResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (mulOutputBytes result) gasRemaining := by
  simp [fromMulResult, h_status]

theorem fromMulResult_efail
    {gasRemaining : Nat} {result : Bn254G1MulEcallBridge.Bn254G1MulResult}
    (h_status : result.status = .efail) :
    fromMulResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromMulResult, h_status]

theorem fromPairingResult_eok
    {gasRemaining : Nat} {result : Bn254PairingEcallBridge.Bn254PairingResult}
    (h_status : result.status = .eok) :
    fromPairingResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (pairingOutputBytesFromResult result) gasRemaining := by
  simp [fromPairingResult, h_status]

theorem fromPairingResult_efail
    {gasRemaining : Nat} {result : Bn254PairingEcallBridge.Bn254PairingResult}
    (h_status : result.status = .efail) :
    fromPairingResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromPairingResult, h_status]

theorem fromAddResult_output_length
    {gasRemaining : Nat} {result : Bn254G1AddEcallBridge.Bn254G1AddResult}
    (h_status : result.status = .eok) :
    (fromAddResult gasRemaining result).output.length = 64 := by
  rw [fromAddResult_eok h_status]
  simp [addOutputBytes_length]

theorem fromMulResult_output_length
    {gasRemaining : Nat} {result : Bn254G1MulEcallBridge.Bn254G1MulResult}
    (h_status : result.status = .eok) :
    (fromMulResult gasRemaining result).output.length = 64 := by
  rw [fromMulResult_eok h_status]
  simp [mulOutputBytes_length]

theorem fromPairingResult_output_length
    {gasRemaining : Nat} {result : Bn254PairingEcallBridge.Bn254PairingResult}
    (h_status : result.status = .eok) :
    (fromPairingResult gasRemaining result).output.length = 32 := by
  rw [fromPairingResult_eok h_status]
  simp [pairingOutputBytesFromResult_length]

@[simp] theorem fromAddResult_failure_output_length
    {gasRemaining : Nat} {result : Bn254G1AddEcallBridge.Bn254G1AddResult}
    (h_status : result.status = .efail) :
    (fromAddResult gasRemaining result).output.length = 0 := by
  rw [fromAddResult_efail h_status]
  rfl

@[simp] theorem fromMulResult_failure_output_length
    {gasRemaining : Nat} {result : Bn254G1MulEcallBridge.Bn254G1MulResult}
    (h_status : result.status = .efail) :
    (fromMulResult gasRemaining result).output.length = 0 := by
  rw [fromMulResult_efail h_status]
  rfl

@[simp] theorem fromPairingResult_failure_output_length
    {gasRemaining : Nat} {result : Bn254PairingEcallBridge.Bn254PairingResult}
    (h_status : result.status = .efail) :
    (fromPairingResult gasRemaining result).output.length = 0 := by
  rw [fromPairingResult_efail h_status]
  rfl

theorem gasRemainingAfterCost_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromAddResult_gasRemaining
    (gasRemaining : Nat) (result : Bn254G1AddEcallBridge.Bn254G1AddResult) :
    (fromAddResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromAddResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

theorem fromMulResult_gasRemaining
    (gasRemaining : Nat) (result : Bn254G1MulEcallBridge.Bn254G1MulResult) :
    (fromMulResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromMulResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

theorem fromPairingResult_gasRemaining
    (gasRemaining : Nat) (result : Bn254PairingEcallBridge.Bn254PairingResult) :
    (fromPairingResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromPairingResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end Bn254PrecompileResultBridge

end EvmAsm.EL
