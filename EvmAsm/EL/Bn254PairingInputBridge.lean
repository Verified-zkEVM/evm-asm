/-
  EvmAsm.EL.Bn254PairingInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bn254_pairing` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bn254PairingInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A BN254 G1 point as represented by `zkvm_bn254_g1_point`. -/
abbrev G1PointBytes := Fin 64 → Byte

/-- A BN254 G2 point as represented by `zkvm_bn254_g2_point`. -/
abbrev G2PointBytes := Fin 128 → Byte

/-- One `zkvm_bn254_pairing_pair` payload. -/
structure PairingPair where
  g1 : G1PointBytes
  g2 : G2PointBytes

/-- Input payload passed to `zkvm_bn254_pairing(pairs, num_pairs, verified)`. -/
structure AcceleratorInput where
  pairs : List PairingPair
  numPairs : Nat

/-- Read one fixed-width BN254 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)

/-- Read one fixed-width BN254 G2 point from executable memory. -/
def g2PointFromMemory (memory : MemoryReader) (start : Nat) : G2PointBytes :=
  fun i => memory (start + i.toNat)

/-- Read one `zkvm_bn254_pairing_pair` from executable memory. -/
def pairingPairFromMemory (memory : MemoryReader) (start : Nat) : PairingPair :=
  { g1 := g1PointFromMemory memory start
    g2 := g2PointFromMemory memory (start + 64) }

/-- Read `numPairs` consecutive 192-byte pairing pairs from executable memory. -/
def pairingPairsFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : List PairingPair :=
  (List.range numPairs).map
    (fun i => pairingPairFromMemory memory (pairsStart + 192 * i))

/--
Distinctive token: Bn254PairingInputBridge.bn254PairingInputFromMemory.
-/
def bn254PairingInputFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : AcceleratorInput :=
  { pairs := pairingPairsFromMemory memory pairsStart numPairs
    numPairs := numPairs }

theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl

theorem g2PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 128) :
    g2PointFromMemory memory start i = memory (start + i.toNat) := rfl

theorem pairingPairFromMemory_g1
    (memory : MemoryReader) (start : Nat) :
    (pairingPairFromMemory memory start).g1 =
      g1PointFromMemory memory start := rfl

theorem pairingPairFromMemory_g2
    (memory : MemoryReader) (start : Nat) :
    (pairingPairFromMemory memory start).g2 =
      g2PointFromMemory memory (start + 64) := rfl

theorem pairingPairsFromMemory_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (pairingPairsFromMemory memory pairsStart numPairs).length = numPairs := by
  simp [pairingPairsFromMemory]

theorem bn254PairingInputFromMemory_pairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bn254PairingInputFromMemory memory pairsStart numPairs).pairs =
      pairingPairsFromMemory memory pairsStart numPairs := rfl

theorem bn254PairingInputFromMemory_numPairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bn254PairingInputFromMemory memory pairsStart numPairs).numPairs = numPairs := rfl

theorem bn254PairingInputFromMemory_pairs_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bn254PairingInputFromMemory memory pairsStart numPairs).pairs.length = numPairs := by
  simp [bn254PairingInputFromMemory, pairingPairsFromMemory_length]

end Bn254PairingInputBridge

end EvmAsm.EL
