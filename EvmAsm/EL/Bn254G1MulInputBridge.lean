/-
  EvmAsm.EL.Bn254G1MulInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bn254_g1_mul` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bn254G1MulInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A BN254 G1 point as represented by `zkvm_bn254_g1_point`. -/
abbrev G1PointBytes := Fin 64 → Byte

/-- A BN254 scalar as represented by `zkvm_bn254_scalar`. -/
abbrev ScalarBytes := Fin 32 → Byte

/-- Input payload passed to `zkvm_bn254_g1_mul(point, scalar, result)`. -/
structure AcceleratorInput where
  point : G1PointBytes
  scalar : ScalarBytes

/-- Read one fixed-width BN254 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)

/-- Read one fixed-width BN254 scalar from executable memory. -/
def scalarFromMemory (memory : MemoryReader) (start : Nat) : ScalarBytes :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: Bn254G1MulInputBridge.bn254G1MulInputFromMemory.
-/
def bn254G1MulInputFromMemory
    (memory : MemoryReader) (pointStart scalarStart : Nat) : AcceleratorInput :=
  { point := g1PointFromMemory memory pointStart
    scalar := scalarFromMemory memory scalarStart }

theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl

theorem scalarFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    scalarFromMemory memory start i = memory (start + i.toNat) := rfl

theorem bn254G1MulInputFromMemory_point
    (memory : MemoryReader) (pointStart scalarStart : Nat) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).point =
      g1PointFromMemory memory pointStart := rfl

theorem bn254G1MulInputFromMemory_scalar
    (memory : MemoryReader) (pointStart scalarStart : Nat) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).scalar =
      scalarFromMemory memory scalarStart := rfl

theorem bn254G1MulInputFromMemory_point_apply
    (memory : MemoryReader) (pointStart scalarStart : Nat) (i : Fin 64) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).point i =
      memory (pointStart + i.toNat) := rfl

theorem bn254G1MulInputFromMemory_scalar_apply
    (memory : MemoryReader) (pointStart scalarStart : Nat) (i : Fin 32) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).scalar i =
      memory (scalarStart + i.toNat) := rfl

end Bn254G1MulInputBridge

end EvmAsm.EL
