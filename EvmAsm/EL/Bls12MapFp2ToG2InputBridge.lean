/-
  EvmAsm.EL.Bls12MapFp2ToG2InputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_map_fp2_to_g2` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bls12MapFp2ToG2InputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A BLS12-381 quadratic-extension field element as represented by
`zkvm_bls12_381_fp2` (`zkvm_bytes_96`). -/
abbrev Fp2Bytes := Fin 96 → Byte

/-- Input payload passed to `zkvm_bls12_map_fp2_to_g2(fp2, result)`. -/
structure AcceleratorInput where
  fp2 : Fp2Bytes

/-- Read one fixed-width BLS12-381 Fp2 element from executable memory. -/
def fp2FromMemory (memory : MemoryReader) (start : Nat) : Fp2Bytes :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: Bls12MapFp2ToG2InputBridge.bls12MapFp2ToG2InputFromMemory.
-/
def bls12MapFp2ToG2InputFromMemory
    (memory : MemoryReader) (fp2Start : Nat) : AcceleratorInput :=
  { fp2 := fp2FromMemory memory fp2Start }

theorem fp2FromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 96) :
    fp2FromMemory memory start i = memory (start + i.toNat) := rfl

theorem bls12MapFp2ToG2InputFromMemory_fp2
    (memory : MemoryReader) (fp2Start : Nat) :
    (bls12MapFp2ToG2InputFromMemory memory fp2Start).fp2 =
      fp2FromMemory memory fp2Start := rfl

end Bls12MapFp2ToG2InputBridge

end EvmAsm.EL
