/-
  EvmAsm.EL.KzgPointEvalPrecompileResultBridge

  Bridge from KZG point-evaluation accelerator ECALL results to EVM precompile
  results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.KzgPointEvalEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace KzgPointEvalPrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

/-- `U256(4096).to_be_bytes32()`, i.e. `FIELD_ELEMENTS_PER_BLOB`. -/
def fieldElementsPerBlobOutput : List Byte :=
  List.replicate 30 (0 : Byte) ++ [0x10, 0x00]

/-- `U256(BLS_MODULUS).to_be_bytes32()` from execution-specs. -/
def blsModulusOutput : List Byte :=
  [ 0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48
  , 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05
  , 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe
  , 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01 ]

/-- Successful KZG point evaluation returns `FIELD_ELEMENTS_PER_BLOB || BLS_MODULUS`. -/
def successOutputBytes : List Byte :=
  fieldElementsPerBlobOutput ++ blsModulusOutput

def outputBytesFromVerified (verified : Bool) : List Byte :=
  if verified then successOutputBytes else []

def outputBytesFromResult
    (result : KzgPointEvalEcallBridge.KzgPointEvalResult) : List Byte :=
  outputBytesFromVerified result.output.verified

def fromPointEvalResult
    (gasRemaining : Nat) (result : KzgPointEvalEcallBridge.KzgPointEvalResult) :
    PrecompileResult :=
  match result.status with
  | .eok =>
      if result.output.verified then
        EvmAsm.Evm64.PrecompileResult.ok successOutputBytes gasRemaining
      else
        EvmAsm.Evm64.PrecompileResult.fail gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def gasRemainingAfterCost (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) : Nat :=
  input.gas - cost

theorem fieldElementsPerBlobOutput_length :
    fieldElementsPerBlobOutput.length = 32 := by
  decide

theorem blsModulusOutput_length :
    blsModulusOutput.length = 32 := by
  decide

theorem successOutputBytes_length :
    successOutputBytes.length = 64 := by
  decide

theorem outputBytesFromVerified_true :
    outputBytesFromVerified true = successOutputBytes := rfl

theorem outputBytesFromVerified_false :
    outputBytesFromVerified false = [] := rfl

theorem outputBytesFromVerified_true_length :
    (outputBytesFromVerified true).length = 64 := by
  simp [outputBytesFromVerified, successOutputBytes_length]

theorem outputBytesFromVerified_false_length :
    (outputBytesFromVerified false).length = 0 := rfl

theorem outputBytesFromResult_true
    {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_verified : result.output.verified = true) :
    outputBytesFromResult result = successOutputBytes := by
  simp [outputBytesFromResult, outputBytesFromVerified, h_verified]

theorem outputBytesFromResult_false
    {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_verified : result.output.verified = false) :
    outputBytesFromResult result = [] := by
  simp [outputBytesFromResult, outputBytesFromVerified, h_verified]

theorem outputBytesFromResult_true_length
    {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_verified : result.output.verified = true) :
    (outputBytesFromResult result).length = 64 := by
  rw [outputBytesFromResult_true h_verified]
  exact successOutputBytes_length

theorem outputBytesFromResult_false_length
    {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_verified : result.output.verified = false) :
    (outputBytesFromResult result).length = 0 := by
  rw [outputBytesFromResult_false h_verified]
  rfl

theorem fromPointEvalResult_eok_verified
    {gasRemaining : Nat} {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_status : result.status = .eok) (h_verified : result.output.verified = true) :
    fromPointEvalResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok successOutputBytes gasRemaining := by
  simp [fromPointEvalResult, h_status, h_verified]

theorem fromPointEvalResult_eok_unverified
    {gasRemaining : Nat} {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_status : result.status = .eok) (h_verified : result.output.verified = false) :
    fromPointEvalResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromPointEvalResult, h_status, h_verified]

theorem fromPointEvalResult_efail
    {gasRemaining : Nat} {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_status : result.status = .efail) :
    fromPointEvalResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromPointEvalResult, h_status]

theorem fromPointEvalResult_success_output_length
    {gasRemaining : Nat} {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_status : result.status = .eok) (h_verified : result.output.verified = true) :
    (fromPointEvalResult gasRemaining result).output.length = 64 := by
  rw [fromPointEvalResult_eok_verified h_status h_verified]
  simp [successOutputBytes_length]

@[simp] theorem fromPointEvalResult_unverified_output_length
    {gasRemaining : Nat} {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_status : result.status = .eok) (h_verified : result.output.verified = false) :
    (fromPointEvalResult gasRemaining result).output.length = 0 := by
  rw [fromPointEvalResult_eok_unverified h_status h_verified]
  rfl

@[simp] theorem fromPointEvalResult_failure_output_length
    {gasRemaining : Nat} {result : KzgPointEvalEcallBridge.KzgPointEvalResult}
    (h_status : result.status = .efail) :
    (fromPointEvalResult gasRemaining result).output.length = 0 := by
  rw [fromPointEvalResult_efail h_status]
  rfl

theorem gasRemainingAfterCost_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromPointEvalResult_gasRemaining
    (gasRemaining : Nat) (result : KzgPointEvalEcallBridge.KzgPointEvalResult) :
    (fromPointEvalResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status
  · cases h_verified : result.output.verified <;>
      simp [fromPointEvalResult, h_status, h_verified, EvmAsm.Evm64.PrecompileResult.ok,
        EvmAsm.Evm64.PrecompileResult.fail]
  · simp [fromPointEvalResult, h_status, EvmAsm.Evm64.PrecompileResult.fail]

end KzgPointEvalPrecompileResultBridge

end EvmAsm.EL
