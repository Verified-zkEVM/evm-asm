/-
  EvmAsm.EL.Bls12G2PrecompileResultBridge

  Bridge from BLS12-381 G2 accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Bls12G2AddEcallBridge
import EvmAsm.EL.Bls12G2MsmEcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12G2PrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

def zeroPad16 : List Byte := List.replicate 16 0

def g2PointChunkBytes (point : Fin 192 → Byte) (chunk : Fin 4) : List Byte :=
  List.ofFn fun i : Fin 48 => point ⟨48 * chunk.val + i.val, by
    have h_chunk := chunk.isLt
    have h_i := i.isLt
    omega⟩

def paddedG2PointChunkBytes (point : Fin 192 → Byte) (chunk : Fin 4) : List Byte :=
  zeroPad16 ++ g2PointChunkBytes point chunk

/-- Execution-specs `g2_to_bytes`: each 48-byte FQ component is left-padded to 64 bytes. -/
def evmG2PointBytes (point : Fin 192 → Byte) : List Byte :=
  paddedG2PointChunkBytes point ⟨0, by decide⟩ ++
  paddedG2PointChunkBytes point ⟨1, by decide⟩ ++
  paddedG2PointChunkBytes point ⟨2, by decide⟩ ++
  paddedG2PointChunkBytes point ⟨3, by decide⟩

def addOutputBytes (result : Bls12G2AddEcallBridge.Bls12G2AddResult) : List Byte :=
  evmG2PointBytes (Bls12G2AddEcallBridge.outputPointFromResult result)

def msmOutputBytes (result : Bls12G2MsmEcallBridge.Bls12G2MsmResult) : List Byte :=
  evmG2PointBytes (Bls12G2MsmEcallBridge.outputPointFromResult result)

def fromAddResult
    (gasRemaining : Nat) (result : Bls12G2AddEcallBridge.Bls12G2AddResult) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (addOutputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def fromMsmResult
    (gasRemaining : Nat) (result : Bls12G2MsmEcallBridge.Bls12G2MsmResult) :
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

theorem g2PointChunkBytes_length (point : Fin 192 → Byte) (chunk : Fin 4) :
    (g2PointChunkBytes point chunk).length = 48 := by
  simp [g2PointChunkBytes]

theorem paddedG2PointChunkBytes_length (point : Fin 192 → Byte) (chunk : Fin 4) :
    (paddedG2PointChunkBytes point chunk).length = 64 := by
  simp [paddedG2PointChunkBytes, zeroPad16_length, g2PointChunkBytes_length]

theorem evmG2PointBytes_length (point : Fin 192 → Byte) :
    (evmG2PointBytes point).length = 256 := by
  simp [evmG2PointBytes, paddedG2PointChunkBytes_length]

theorem addOutputBytes_length (result : Bls12G2AddEcallBridge.Bls12G2AddResult) :
    (addOutputBytes result).length = 256 := by
  simp [addOutputBytes, evmG2PointBytes_length]

theorem msmOutputBytes_length (result : Bls12G2MsmEcallBridge.Bls12G2MsmResult) :
    (msmOutputBytes result).length = 256 := by
  simp [msmOutputBytes, evmG2PointBytes_length]

theorem fromAddResult_eok
    {gasRemaining : Nat} {result : Bls12G2AddEcallBridge.Bls12G2AddResult}
    (h_status : result.status = .eok) :
    fromAddResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (addOutputBytes result) gasRemaining := by
  simp [fromAddResult, h_status]

theorem fromAddResult_efail
    {gasRemaining : Nat} {result : Bls12G2AddEcallBridge.Bls12G2AddResult}
    (h_status : result.status = .efail) :
    fromAddResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromAddResult, h_status]

theorem fromMsmResult_eok
    {gasRemaining : Nat} {result : Bls12G2MsmEcallBridge.Bls12G2MsmResult}
    (h_status : result.status = .eok) :
    fromMsmResult gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (msmOutputBytes result) gasRemaining := by
  simp [fromMsmResult, h_status]

theorem fromMsmResult_efail
    {gasRemaining : Nat} {result : Bls12G2MsmEcallBridge.Bls12G2MsmResult}
    (h_status : result.status = .efail) :
    fromMsmResult gasRemaining result = EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromMsmResult, h_status]

theorem fromAddResult_output_length
    {gasRemaining : Nat} {result : Bls12G2AddEcallBridge.Bls12G2AddResult}
    (h_status : result.status = .eok) :
    (fromAddResult gasRemaining result).output.length = 256 := by
  rw [fromAddResult_eok h_status]
  simp [addOutputBytes_length]

theorem fromMsmResult_output_length
    {gasRemaining : Nat} {result : Bls12G2MsmEcallBridge.Bls12G2MsmResult}
    (h_status : result.status = .eok) :
    (fromMsmResult gasRemaining result).output.length = 256 := by
  rw [fromMsmResult_eok h_status]
  simp [msmOutputBytes_length]

@[simp] theorem fromAddResult_failure_output_length
    {gasRemaining : Nat} {result : Bls12G2AddEcallBridge.Bls12G2AddResult}
    (h_status : result.status = .efail) :
    (fromAddResult gasRemaining result).output.length = 0 := by
  rw [fromAddResult_efail h_status]
  rfl

@[simp] theorem fromMsmResult_failure_output_length
    {gasRemaining : Nat} {result : Bls12G2MsmEcallBridge.Bls12G2MsmResult}
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
    (gasRemaining : Nat) (result : Bls12G2AddEcallBridge.Bls12G2AddResult) :
    (fromAddResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromAddResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

theorem fromMsmResult_gasRemaining
    (gasRemaining : Nat) (result : Bls12G2MsmEcallBridge.Bls12G2MsmResult) :
    (fromMsmResult gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromMsmResult, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end Bls12G2PrecompileResultBridge

end EvmAsm.EL
