/-
  EvmAsm.EL.KzgPointEvalInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_kzg_point_eval` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace KzgPointEvalInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A KZG commitment/proof as represented by `zkvm_bytes_48`. -/
abbrev Bytes48 := Fin 48 → Byte

/-- A KZG field element as represented by `zkvm_bytes_32`. -/
abbrev Bytes32 := Fin 32 → Byte

/-- Input payload passed to `zkvm_kzg_point_eval(commitment, z, y, proof, verified)`. -/
structure AcceleratorInput where
  commitment : Bytes48
  z : Bytes32
  y : Bytes32
  proof : Bytes48

/-- Read one fixed-width 48-byte KZG payload from executable memory. -/
def bytes48FromMemory (memory : MemoryReader) (start : Nat) : Bytes48 :=
  fun i => memory (start + i.toNat)

/-- Read one fixed-width 32-byte KZG field element from executable memory. -/
def bytes32FromMemory (memory : MemoryReader) (start : Nat) : Bytes32 :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: KzgPointEvalInputBridge.kzgPointEvalInputFromMemory.
-/
def kzgPointEvalInputFromMemory
    (memory : MemoryReader)
    (commitmentStart zStart yStart proofStart : Nat) : AcceleratorInput :=
  { commitment := bytes48FromMemory memory commitmentStart
    z := bytes32FromMemory memory zStart
    y := bytes32FromMemory memory yStart
    proof := bytes48FromMemory memory proofStart }

theorem bytes48FromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 48) :
    bytes48FromMemory memory start i = memory (start + i.toNat) := rfl

theorem bytes32FromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    bytes32FromMemory memory start i = memory (start + i.toNat) := rfl

theorem kzgPointEvalInputFromMemory_commitment
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).commitment =
      bytes48FromMemory memory commitmentStart := rfl

theorem kzgPointEvalInputFromMemory_z
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).z =
      bytes32FromMemory memory zStart := rfl

theorem kzgPointEvalInputFromMemory_y
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).y =
      bytes32FromMemory memory yStart := rfl

theorem kzgPointEvalInputFromMemory_proof
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).proof =
      bytes48FromMemory memory proofStart := rfl

end KzgPointEvalInputBridge

end EvmAsm.EL
