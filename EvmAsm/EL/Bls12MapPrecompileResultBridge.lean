/-
  EvmAsm.EL.Bls12MapPrecompileResultBridge

  Bridge from BLS12-381 map accelerator ECALL results to EVM precompile results.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Bls12MapFpToG1EcallBridge
import EvmAsm.EL.Bls12MapFp2ToG2EcallBridge
import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.EL

namespace Bls12MapPrecompileResultBridge

abbrev Byte := EvmAsm.EL.Byte
abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult

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

def mapFpToG1OutputBytes
    (result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result) : List Byte :=
  evmG1PointBytes (Bls12MapFpToG1EcallBridge.outputPointFromResult result)

def mapFp2ToG2OutputBytes
    (result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result) : List Byte :=
  evmG2PointBytes (Bls12MapFp2ToG2EcallBridge.outputPointFromResult result)

def fromMapFpToG1Result
    (gasRemaining : Nat) (result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (mapFpToG1OutputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def fromMapFp2ToG2Result
    (gasRemaining : Nat) (result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result) :
    PrecompileResult :=
  match result.status with
  | .eok => EvmAsm.Evm64.PrecompileResult.ok (mapFp2ToG2OutputBytes result) gasRemaining
  | .efail => EvmAsm.Evm64.PrecompileResult.fail gasRemaining

def gasRemainingAfterCost (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) : Nat :=
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

theorem g2PointChunkBytes_length (point : Fin 192 → Byte) (chunk : Fin 4) :
    (g2PointChunkBytes point chunk).length = 48 := by
  simp [g2PointChunkBytes]

theorem paddedG2PointChunkBytes_length (point : Fin 192 → Byte) (chunk : Fin 4) :
    (paddedG2PointChunkBytes point chunk).length = 64 := by
  simp [paddedG2PointChunkBytes, zeroPad16_length, g2PointChunkBytes_length]

theorem evmG2PointBytes_length (point : Fin 192 → Byte) :
    (evmG2PointBytes point).length = 256 := by
  simp [evmG2PointBytes, paddedG2PointChunkBytes_length]

theorem mapFpToG1OutputBytes_length
    (result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result) :
    (mapFpToG1OutputBytes result).length = 128 := by
  simp [mapFpToG1OutputBytes, evmG1PointBytes_length]

theorem mapFp2ToG2OutputBytes_length
    (result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result) :
    (mapFp2ToG2OutputBytes result).length = 256 := by
  simp [mapFp2ToG2OutputBytes, evmG2PointBytes_length]

theorem fromMapFpToG1Result_eok
    {gasRemaining : Nat} {result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result}
    (h_status : result.status = .eok) :
    fromMapFpToG1Result gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (mapFpToG1OutputBytes result) gasRemaining := by
  simp [fromMapFpToG1Result, h_status]

theorem fromMapFpToG1Result_efail
    {gasRemaining : Nat} {result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result}
    (h_status : result.status = .efail) :
    fromMapFpToG1Result gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromMapFpToG1Result, h_status]

theorem fromMapFp2ToG2Result_eok
    {gasRemaining : Nat} {result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result}
    (h_status : result.status = .eok) :
    fromMapFp2ToG2Result gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.ok (mapFp2ToG2OutputBytes result) gasRemaining := by
  simp [fromMapFp2ToG2Result, h_status]

theorem fromMapFp2ToG2Result_efail
    {gasRemaining : Nat} {result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result}
    (h_status : result.status = .efail) :
    fromMapFp2ToG2Result gasRemaining result =
      EvmAsm.Evm64.PrecompileResult.fail gasRemaining := by
  simp [fromMapFp2ToG2Result, h_status]

theorem fromMapFpToG1Result_output_length
    {gasRemaining : Nat} {result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result}
    (h_status : result.status = .eok) :
    (fromMapFpToG1Result gasRemaining result).output.length = 128 := by
  rw [fromMapFpToG1Result_eok h_status]
  simp [mapFpToG1OutputBytes_length]

theorem fromMapFp2ToG2Result_output_length
    {gasRemaining : Nat} {result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result}
    (h_status : result.status = .eok) :
    (fromMapFp2ToG2Result gasRemaining result).output.length = 256 := by
  rw [fromMapFp2ToG2Result_eok h_status]
  simp [mapFp2ToG2OutputBytes_length]

@[simp] theorem fromMapFpToG1Result_failure_output_length
    {gasRemaining : Nat} {result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result}
    (h_status : result.status = .efail) :
    (fromMapFpToG1Result gasRemaining result).output.length = 0 := by
  rw [fromMapFpToG1Result_efail h_status]
  rfl

@[simp] theorem fromMapFp2ToG2Result_failure_output_length
    {gasRemaining : Nat} {result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result}
    (h_status : result.status = .efail) :
    (fromMapFp2ToG2Result gasRemaining result).output.length = 0 := by
  rw [fromMapFp2ToG2Result_efail h_status]
  rfl

theorem gasRemainingAfterCost_le_inputGas
    (input : EvmAsm.Evm64.PrecompileInput) (cost : Nat) :
    gasRemainingAfterCost input cost ≤ input.gas := by
  simp [gasRemainingAfterCost]

theorem fromMapFpToG1Result_gasRemaining
    (gasRemaining : Nat) (result : Bls12MapFpToG1EcallBridge.Bls12MapFpToG1Result) :
    (fromMapFpToG1Result gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromMapFpToG1Result, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

theorem fromMapFp2ToG2Result_gasRemaining
    (gasRemaining : Nat) (result : Bls12MapFp2ToG2EcallBridge.Bls12MapFp2ToG2Result) :
    (fromMapFp2ToG2Result gasRemaining result).gasRemaining = gasRemaining := by
  cases h_status : result.status <;>
    simp [fromMapFp2ToG2Result, h_status, EvmAsm.Evm64.PrecompileResult.ok,
      EvmAsm.Evm64.PrecompileResult.fail]

end Bls12MapPrecompileResultBridge

end EvmAsm.EL
