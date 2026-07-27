/-
  EvmAsm.Evm64.KeccakArgs

  Pure stack-argument record for KECCAK256/SHA3 (GH #111).
-/

import EvmAsm.Evm64.EvmWord
import EvmAsm.Evm64.MemoryGas

namespace EvmAsm.Evm64

namespace KeccakArgs

/-- Memory slice hashed by KECCAK256, described by EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- Stack arguments for KECCAK256/SHA3: input memory offset and size. -/
structure Args where
  input : MemoryRange
  deriving Repr

/-- KECCAK256 pops two stack words: input offset and input size. -/
def stackArgumentCount : Nat := 2

/-- KECCAK256 pushes one 256-bit hash result. -/
def resultCount : Nat := 1

/-- Convenience builder for KECCAK256 stack arguments. -/
def keccakArgs (offset size : EvmWord) : Args :=
  { input := { offset := offset, size := size } }

/-- Input memory range projected from KECCAK256 stack arguments. -/
def inputRange (args : Args) : MemoryRange :=
  args.input

/-- Input offset converted to host `Nat` for executable gas/memory helpers. -/
def inputOffsetNat (args : Args) : Nat :=
  args.input.offset.toNat

/-- Input size converted to host `Nat` for executable gas/memory helpers. -/
def inputSizeNat (args : Args) : Nat :=
  args.input.size.toNat

/-- Dynamic gas for KECCAK256 computed from the stack-argument record.
    Distinctive token: KeccakArgs.keccakDynamicCostFromArgs. -/
def keccakDynamicCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.keccakDynamicCost sizeBytes (inputOffsetNat args) (inputSizeNat args)

theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl

theorem resultCount_eq_one : resultCount = 1 := rfl

theorem keccakArgs_offset (offset size : EvmWord) :
    (keccakArgs offset size).input.offset = offset := rfl

theorem keccakArgs_size (offset size : EvmWord) :
    (keccakArgs offset size).input.size = size := rfl

theorem inputRange_offset (args : Args) :
    (inputRange args).offset = args.input.offset := rfl

theorem inputRange_size (args : Args) :
    (inputRange args).size = args.input.size := rfl

theorem inputOffsetNat_eq (args : Args) :
    inputOffsetNat args = args.input.offset.toNat := rfl

theorem inputSizeNat_eq (args : Args) :
    inputSizeNat args = args.input.size.toNat := rfl

theorem keccakDynamicCostFromArgs_eq (sizeBytes : Nat) (args : Args) :
    keccakDynamicCostFromArgs sizeBytes args =
      MemoryGas.keccakDynamicCost sizeBytes args.input.offset.toNat args.input.size.toNat := rfl

@[simp] theorem keccakDynamicCostFromArgs_zero_length
    (sizeBytes : Nat) (offset : EvmWord) :
    keccakDynamicCostFromArgs sizeBytes (keccakArgs offset 0) = 0 := by
  simp [keccakDynamicCostFromArgs, keccakArgs, inputOffsetNat, inputSizeNat]

theorem keccakDynamicCostFromArgs_eq_word_charge_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.input.offset.toNat args.input.size.toNat = sizeBytes) :
    keccakDynamicCostFromArgs sizeBytes args =
      MemoryGas.keccakGasPerWord * MemoryGas.memoryWords args.input.size.toNat := by
  exact MemoryGas.keccakDynamicCost_eq_word_charge_of_no_growth h_no_growth

theorem keccakDynamicCostFromArgs_eq_word_charge_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.input.offset.toNat + args.input.size.toNat) ≤ sizeBytes) :
    keccakDynamicCostFromArgs sizeBytes args =
      MemoryGas.keccakGasPerWord * MemoryGas.memoryWords args.input.size.toNat := by
  exact MemoryGas.keccakDynamicCost_eq_word_charge_of_access_le h_access

end KeccakArgs

end EvmAsm.Evm64
