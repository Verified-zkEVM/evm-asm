/-
  EvmAsm.EL.Bn254G1AddResultBridge

  Bridge from the zkVM `zkvm_bn254_g1_add` accelerator output buffer (a single
  64-byte `zkvm_bn254_g1_point` written through the `result` pointer) to the
  byte-list view consumed by EL precompile return-data assembly. Mirrors the
  SHA256/RIPEMD160 result-bridge skeleton; we do NOT compute a stack word
  here because the BN254 G1 point is 64 bytes (does not fit into one EVM
  stack word) — precompile-output framing is left to a downstream slice.
-/

module

public import EvmAsm.EL.WorldState

@[expose] public section

namespace EvmAsm.EL

namespace Bn254G1AddResultBridge

/-- The 64-byte BN254 G1 point payload (`zkvm_bn254_g1_point`). -/
abbrev PointBytes := Fin 64 → Byte

/-- Accelerator output payload for `zkvm_bn254_g1_add`. -/
structure AcceleratorOutput where
  result : PointBytes

/-- Materialise the output point as a byte list (length 64). -/
def pointBytesList (point : PointBytes) : List Byte :=
  List.ofFn point

/-- Distinctive token: Bn254G1AddResultBridge.outputBytesList. -/
def outputBytesList (output : AcceleratorOutput) : List Byte :=
  pointBytesList output.result

theorem pointBytesList_length (point : PointBytes) :
    (pointBytesList point).length = 64 := by
  simp [pointBytesList]

theorem outputBytesList_length (output : AcceleratorOutput) :
    (outputBytesList output).length = 64 := by
  simp [outputBytesList, pointBytesList_length]

theorem outputBytesList_eq (output : AcceleratorOutput) :
    outputBytesList output = pointBytesList output.result := rfl

end Bn254G1AddResultBridge

end EvmAsm.EL
