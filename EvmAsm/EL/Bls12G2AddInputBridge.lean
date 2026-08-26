/-
  EvmAsm.EL.Bls12G2AddInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_g2_add` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bls12G2AddInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A BLS12-381 G2 point as represented by `zkvm_bls12_381_g2_point`
(`zkvm_bytes_192`). -/
abbrev G2PointBytes := Fin 192 → Byte

/-- Input payload passed to `zkvm_bls12_g2_add(p1, p2, result)`. -/
structure AcceleratorInput where
  p1 : G2PointBytes
  p2 : G2PointBytes

/-- Read one fixed-width BLS12-381 G2 point from executable memory. -/
def g2PointFromMemory (memory : MemoryReader) (start : Nat) : G2PointBytes :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: Bls12G2AddInputBridge.bls12G2AddInputFromMemory.
-/
def bls12G2AddInputFromMemory
    (memory : MemoryReader) (p1Start p2Start : Nat) : AcceleratorInput :=
  { p1 := g2PointFromMemory memory p1Start
    p2 := g2PointFromMemory memory p2Start }

theorem g2PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 192) :
    g2PointFromMemory memory start i = memory (start + i.toNat) := rfl

theorem bls12G2AddInputFromMemory_p1
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bls12G2AddInputFromMemory memory p1Start p2Start).p1 =
      g2PointFromMemory memory p1Start := rfl

theorem bls12G2AddInputFromMemory_p2
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bls12G2AddInputFromMemory memory p1Start p2Start).p2 =
      g2PointFromMemory memory p2Start := rfl

theorem bls12G2AddInputFromMemory_p1_apply
    (memory : MemoryReader) (p1Start p2Start : Nat) (i : Fin 192) :
    (bls12G2AddInputFromMemory memory p1Start p2Start).p1 i =
      memory (p1Start + i.toNat) := rfl

theorem bls12G2AddInputFromMemory_p2_apply
    (memory : MemoryReader) (p1Start p2Start : Nat) (i : Fin 192) :
    (bls12G2AddInputFromMemory memory p1Start p2Start).p2 i =
      memory (p2Start + i.toNat) := rfl

end Bls12G2AddInputBridge

end EvmAsm.EL
