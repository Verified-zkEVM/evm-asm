/-
  EvmAsm.EL.Bn254G1AddInputBridge

  Bridge from BN254 G1-addition precompile call data to the byte-buffer input
  consumed by the zkVM `zkvm_bn254_g1_add` accelerator. The accelerator C
  signature is

      zkvm_status zkvm_bn254_g1_add(const zkvm_bn254_g1_point* p1,
                                    const zkvm_bn254_g1_point* p2,
                                    zkvm_bn254_g1_point* result);

  where `zkvm_bn254_g1_point` is `zkvm_bytes_64`. This module fixes the input
  payload shape (two 64-byte points read from memory) and provides the
  per-field memory-read decompositions; the result-buffer shape and pure
  execution boundary live in the sibling `Result`/`Ecall` bridges.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bn254G1AddInputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- The 64-byte BN254 G1 point payload (`zkvm_bn254_g1_point`). -/
abbrev PointBytes := Fin 64 → Byte

/--
Input payload passed to the
`zkvm_bn254_g1_add(p1, p2, result)` accelerator.

Distinctive token: Bn254G1AddInputBridge.AcceleratorInput zkvm_bn254_g1_add.
-/
structure AcceleratorInput where
  p1 : PointBytes
  p2 : PointBytes

/-- Read a fixed `n`-byte block starting at `start` from a `MemoryReader`. -/
def readFixed (n : Nat) (memory : MemoryReader) (start : Nat) : Fin n → Byte :=
  fun i => memory (start + i.val)

/-- Build the `p1` G1-point payload by reading 64 bytes from memory. -/
def p1BytesFromMemory (memory : MemoryReader) (start : Nat) : PointBytes :=
  readFixed 64 memory start

/-- Build the `p2` G1-point payload by reading 64 bytes from memory. -/
def p2BytesFromMemory (memory : MemoryReader) (start : Nat) : PointBytes :=
  readFixed 64 memory start

/--
Accelerator-call input assembled from two byte-addressed memory slices, one
per G1 point.

Distinctive token: Bn254G1AddInputBridge.bn254G1AddInputFromMemory.
-/
def bn254G1AddInputFromMemory
    (memory : MemoryReader) (p1Start p2Start : Nat) : AcceleratorInput :=
  { p1 := p1BytesFromMemory memory p1Start
    p2 := p2BytesFromMemory memory p2Start }

/-- Compatibility alias matching the SHA256/Secp256k1 bridge naming. -/
def acceleratorInputFromMemory
    (memory : MemoryReader) (p1Start p2Start : Nat) : AcceleratorInput :=
  bn254G1AddInputFromMemory memory p1Start p2Start

theorem readFixed_apply (n : Nat) (memory : MemoryReader) (start : Nat) (i : Fin n) :
    readFixed n memory start i = memory (start + i.val) := rfl

theorem p1BytesFromMemory_apply (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    p1BytesFromMemory memory start i = memory (start + i.val) := rfl

theorem p2BytesFromMemory_apply (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    p2BytesFromMemory memory start i = memory (start + i.val) := rfl

theorem bn254G1AddInputFromMemory_p1
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bn254G1AddInputFromMemory memory p1Start p2Start).p1 =
      p1BytesFromMemory memory p1Start := rfl

theorem bn254G1AddInputFromMemory_p2
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bn254G1AddInputFromMemory memory p1Start p2Start).p2 =
      p2BytesFromMemory memory p2Start := rfl

theorem acceleratorInputFromMemory_eq
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    acceleratorInputFromMemory memory p1Start p2Start =
      bn254G1AddInputFromMemory memory p1Start p2Start := rfl

end Bn254G1AddInputBridge

end EvmAsm.EL
