/-
  EvmAsm.EL.Bls12MapFpToG1InputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_map_fp_to_g1` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge

@[expose] public section

namespace EvmAsm.EL

namespace Bls12MapFpToG1InputBridge

/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader

/-- A BLS12-381 base-field element as represented by `zkvm_bls12_381_fp` (48 bytes). -/
abbrev FpBytes := Fin 48 → Byte

/-- Input payload passed to `zkvm_bls12_map_fp_to_g1(field_element, result)`. -/
structure AcceleratorInput where
  fieldElement : FpBytes

/-- Read one fixed-width BLS12-381 base-field element from executable memory. -/
def fpFromMemory (memory : MemoryReader) (start : Nat) : FpBytes :=
  fun i => memory (start + i.toNat)

/--
Distinctive token: Bls12MapFpToG1InputBridge.bls12MapFpToG1InputFromMemory.
-/
def bls12MapFpToG1InputFromMemory
    (memory : MemoryReader) (fpStart : Nat) : AcceleratorInput :=
  { fieldElement := fpFromMemory memory fpStart }

theorem fpFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 48) :
    fpFromMemory memory start i = memory (start + i.toNat) := rfl

theorem bls12MapFpToG1InputFromMemory_fieldElement
    (memory : MemoryReader) (fpStart : Nat) :
    (bls12MapFpToG1InputFromMemory memory fpStart).fieldElement =
      fpFromMemory memory fpStart := rfl

theorem bls12MapFpToG1InputFromMemory_fieldElement_apply
    (memory : MemoryReader) (fpStart : Nat) (i : Fin 48) :
    (bls12MapFpToG1InputFromMemory memory fpStart).fieldElement i =
      memory (fpStart + i.toNat) := rfl

end Bls12MapFpToG1InputBridge

end EvmAsm.EL
