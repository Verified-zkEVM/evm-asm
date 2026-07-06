/-
  EvmAsm.EL.Bls12G1PrecompileResultBridge

  Bridge from BLS12-381 G1 accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Bls12G1AddEcallBridge
import EvmAsm.EL.Bls12G1MsmEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12G1PrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

def zeroPad16 : List Byte := List.replicate 16 0

def g1PointXBytes (point : Fin 96 → Byte) : List Byte :=
  List.ofFn fun i : Fin 48 => point ⟨i.val, by
    have h_i := i.isLt
    omega⟩

def g1PointYBytes (point : Fin 96 → Byte) : List Byte :=
  List.ofFn fun i : Fin 48 => point ⟨48 + i.val, by
    have h_i := i.isLt
    omega⟩

/-- Execution-specs `g1_to_bytes`: each 48-byte coordinate is left-padded to 64 bytes. -/
def evmG1PointBytes (point : Fin 96 → Byte) : List Byte :=
  zeroPad16 ++ g1PointXBytes point ++ zeroPad16 ++ g1PointYBytes point

def addOutputBytes (result : Bls12G1AddEcallBridge.Bls12G1AddResult) : List Byte :=
  evmG1PointBytes (Bls12G1AddEcallBridge.outputPointFromResult result)

def msmOutputBytes (result : Bls12G1MsmEcallBridge.Bls12G1MsmResult) : List Byte :=
  evmG1PointBytes (Bls12G1MsmEcallBridge.outputPointFromResult result)

def fromAddResult
    (gasRemaining : Nat) (result : Bls12G1AddEcallBridge.Bls12G1AddResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (addOutputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def fromMsmResult
    (gasRemaining : Nat) (result : Bls12G1MsmEcallBridge.Bls12G1MsmResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (msmOutputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def addGasRemaining (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) : Nat :=
  input.gas - cost

def msmGasRemaining (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) : Nat :=
  input.gas - cost

theorem zeroPad16_length : zeroPad16.length = 16 := by
  simp [zeroPad16]

theorem g1PointXBytes_length (point : Fin 96 → Byte) :
    (g1PointXBytes point).length = 48 := by
  simp [g1PointXBytes]

theorem g1PointYBytes_length (point : Fin 96 → Byte) :
    (g1PointYBytes point).length = 48 := by
  simp [g1PointYBytes]

theorem evmG1PointBytes_length (point : Fin 96 → Byte) :
    (evmG1PointBytes point).length = 128 := by
  simp [evmG1PointBytes, zeroPad16_length, g1PointXBytes_length, g1PointYBytes_length]

theorem addOutputBytes_length (result : Bls12G1AddEcallBridge.Bls12G1AddResult) :
    (addOutputBytes result).length = 128 := by
  simp [addOutputBytes, evmG1PointBytes_length]

theorem msmOutputBytes_length (result : Bls12G1MsmEcallBridge.Bls12G1MsmResult) :
    (msmOutputBytes result).length = 128 := by
  simp [msmOutputBytes, evmG1PointBytes_length]

theorem fromAddResult_eok
    {gasRemaining : Nat} {result : Bls12G1AddEcallBridge.Bls12G1AddResult}
    (h_status : result.status = .eok) :
    fromAddResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (addOutputBytes result) gasRemaining := by
  simp [fromAddResult, h_status]

theorem fromAddResult_efail
    {gasRemaining : Nat} {result : Bls12G1AddEcallBridge.Bls12G1AddResult}
    (h_status : result.status = .efail) :
    fromAddResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromAddResult, h_status]

theorem fromMsmResult_eok
    {gasRemaining : Nat} {result : Bls12G1MsmEcallBridge.Bls12G1MsmResult}
    (h_status : result.status = .eok) :
    fromMsmResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (msmOutputBytes result) gasRemaining := by
  simp [fromMsmResult, h_status]

theorem fromMsmResult_efail
    {gasRemaining : Nat} {result : Bls12G1MsmEcallBridge.Bls12G1MsmResult}
    (h_status : result.status = .efail) :
    fromMsmResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromMsmResult, h_status]

theorem fromAddResult_output_length
    {gasRemaining : Nat} {result : Bls12G1AddEcallBridge.Bls12G1AddResult}
    (h_status : result.status = .eok) :
    (fromAddResult gasRemaining result).output.length = 128 := by
  rw [fromAddResult_eok h_status]
  simp [addOutputBytes_length]

theorem fromMsmResult_output_length
    {gasRemaining : Nat} {result : Bls12G1MsmEcallBridge.Bls12G1MsmResult}
    (h_status : result.status = .eok) :
    (fromMsmResult gasRemaining result).output.length = 128 := by
  rw [fromMsmResult_eok h_status]
  simp [msmOutputBytes_length]

@[simp] theorem fromAddResult_failure_output_length
    {gasRemaining : Nat} {result : Bls12G1AddEcallBridge.Bls12G1AddResult}
    (h_status : result.status = .efail) :
    (fromAddResult gasRemaining result).output.length = 0 := by
  rw [fromAddResult_efail h_status]
  rfl

@[simp] theorem fromMsmResult_failure_output_length
    {gasRemaining : Nat} {result : Bls12G1MsmEcallBridge.Bls12G1MsmResult}
    (h_status : result.status = .efail) :
    (fromMsmResult gasRemaining result).output.length = 0 := by
  rw [fromMsmResult_efail h_status]
  rfl

theorem addGasRemaining_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    addGasRemaining input cost ≤ input.gas := by
  simp [addGasRemaining]

theorem msmGasRemaining_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    msmGasRemaining input cost ≤ input.gas := by
  simp [msmGasRemaining]

theorem fromAddResult_gasRemaining
    (gasRemaining : Nat) (result : Bls12G1AddEcallBridge.Bls12G1AddResult) :
    (fromAddResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromAddResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

theorem fromMsmResult_gasRemaining
    (gasRemaining : Nat) (result : Bls12G1MsmEcallBridge.Bls12G1MsmResult) :
    (fromMsmResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromMsmResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end Bls12G1PrecompileResultBridge

end EvmAsm.EL
