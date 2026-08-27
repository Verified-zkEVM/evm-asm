/-
  EvmAsm.EL.Bls12PairingInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_pairing` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bls12PairingInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A BLS12-381 G1 point as represented by `zkvm_bls12_381_g1_point`
(`zkvm_bytes_96`). -/
abbrev G1PointBytes := Fin 96 → Byte

/-- A BLS12-381 G2 point as represented by `zkvm_bls12_381_g2_point`
(`zkvm_bytes_192`). -/
abbrev G2PointBytes := Fin 192 → Byte

/-- One `zkvm_bls12_381_pairing_pair` payload. -/
structure PairingPair where
  g1 : G1PointBytes
  g2 : G2PointBytes

/-- Input payload passed to `zkvm_bls12_pairing(pairs, num_pairs, verified)`. -/
structure AcceleratorInput where
  pairs : List PairingPair
  numPairs : Nat

/-- Read one fixed-width BLS12-381 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)

/-- Read one fixed-width BLS12-381 G2 point from executable memory. -/
def g2PointFromMemory (memory : MemoryReader) (start : Nat) : G2PointBytes :=
  fun i => memory (start + i.toNat)

/-- Read one `zkvm_bls12_381_pairing_pair` from executable memory.
The pair layout is the 96-byte G1 point followed by the 192-byte G2 point
(288 bytes total per pair). -/
def pairingPairFromMemory (memory : MemoryReader) (start : Nat) : PairingPair :=
  { g1 := g1PointFromMemory memory start
    g2 := g2PointFromMemory memory (start + 96) }

/-- Read `numPairs` consecutive 288-byte BLS12-381 pairing pairs from memory. -/
def pairingPairsFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : List PairingPair :=
  (List.range numPairs).map
    (fun i => pairingPairFromMemory memory (pairsStart + 288 * i))

/--
Distinctive token: Bls12PairingInputBridge.bls12PairingInputFromMemory.
-/
def bls12PairingInputFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : AcceleratorInput :=
  { pairs := pairingPairsFromMemory memory pairsStart numPairs
    numPairs := numPairs }

theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 96) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl

theorem g2PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 192) :
    g2PointFromMemory memory start i = memory (start + i.toNat) := rfl

theorem pairingPairFromMemory_g1
    (memory : MemoryReader) (start : Nat) :
    (pairingPairFromMemory memory start).g1 =
      g1PointFromMemory memory start := rfl

theorem pairingPairFromMemory_g2
    (memory : MemoryReader) (start : Nat) :
    (pairingPairFromMemory memory start).g2 =
      g2PointFromMemory memory (start + 96) := rfl

theorem pairingPairsFromMemory_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (pairingPairsFromMemory memory pairsStart numPairs).length = numPairs := by
  simp [pairingPairsFromMemory]

theorem bls12PairingInputFromMemory_pairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12PairingInputFromMemory memory pairsStart numPairs).pairs =
      pairingPairsFromMemory memory pairsStart numPairs := rfl

theorem bls12PairingInputFromMemory_numPairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12PairingInputFromMemory memory pairsStart numPairs).numPairs = numPairs := rfl

theorem bls12PairingInputFromMemory_pairs_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12PairingInputFromMemory memory pairsStart numPairs).pairs.length = numPairs := by
  simp [bls12PairingInputFromMemory, pairingPairsFromMemory_length]

end Bls12PairingInputBridge

end EvmAsm.EL
