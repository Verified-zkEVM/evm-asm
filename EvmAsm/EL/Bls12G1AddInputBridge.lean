/-
  EvmAsm.EL.Bls12G1AddInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_g1_add` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bls12G1AddInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A BLS12-381 G1 point as represented by `zkvm_bls12_381_g1_point`. -/
abbrev G1PointBytes := Fin 96 → Byte

/-- Input payload passed to `zkvm_bls12_g1_add(p1, p2, result)`. -/
structure AcceleratorInput where
  p1 : G1PointBytes
  p2 : G1PointBytes

/-- Read one fixed-width BLS12-381 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: Bls12G1AddInputBridge.bls12G1AddInputFromMemory.
-/
def bls12G1AddInputFromMemory
    (memory : MemoryReader) (p1Start p2Start : Nat) : AcceleratorInput :=
  { p1 := g1PointFromMemory memory p1Start
    p2 := g1PointFromMemory memory p2Start }

theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 96) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl

theorem bls12G1AddInputFromMemory_p1
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p1 =
      g1PointFromMemory memory p1Start := rfl

theorem bls12G1AddInputFromMemory_p2
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p2 =
      g1PointFromMemory memory p2Start := rfl

theorem bls12G1AddInputFromMemory_p1_apply
    (memory : MemoryReader) (p1Start p2Start : Nat) (i : Fin 96) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p1 i =
      memory (p1Start + i.toNat) := rfl

theorem bls12G1AddInputFromMemory_p2_apply
    (memory : MemoryReader) (p1Start p2Start : Nat) (i : Fin 96) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p2 i =
      memory (p2Start + i.toNat) := rfl

end Bls12G1AddInputBridge

end EvmAsm.EL
