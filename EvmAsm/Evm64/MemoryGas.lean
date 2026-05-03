/-
  EvmAsm.Evm64.MemoryGas

  Pure EVM memory expansion gas helpers for issue #118.
-/

import EvmAsm.Evm64.Memory

namespace EvmAsm.Evm64
namespace MemoryGas

/-- Shanghai memory expansion linear coefficient, charged per 32-byte word. -/
def memoryGasPerWord : Nat := 3

/-- Convert a byte high-water mark to EVM memory words (32-byte chunks). -/
def memoryWords (sizeBytes : Nat) : Nat :=
  roundUpTo32 sizeBytes / 32

/-- EVM memory cost function `C_mem(words) = 3 * words + words^2 / 512`. -/
def memoryCost (words : Nat) : Nat :=
  memoryGasPerWord * words + (words * words) / 512

/-- Memory cost for a byte high-water mark. -/
def memoryCostForBytes (sizeBytes : Nat) : Nat :=
  memoryCost (memoryWords sizeBytes)

/-- Incremental memory expansion cost from an old byte high-water mark to a new one. -/
def memoryExpansionCost (oldSizeBytes newSizeBytes : Nat) : Nat :=
  memoryCostForBytes newSizeBytes - memoryCostForBytes oldSizeBytes

/-- Incremental memory expansion cost caused by an access `(offset, length)`. -/
def memoryAccessExpansionCost (sizeBytes offset length : Nat) : Nat :=
  memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length)

@[simp] theorem memoryWords_zero : memoryWords 0 = 0 := by
  simp [memoryWords, roundUpTo32_zero]

@[simp] theorem memoryCost_zero : memoryCost 0 = 0 := by
  simp [memoryCost, memoryGasPerWord]

@[simp] theorem memoryCostForBytes_zero : memoryCostForBytes 0 = 0 := by
  simp [memoryCostForBytes]

@[simp] theorem memoryExpansionCost_same (sizeBytes : Nat) :
    memoryExpansionCost sizeBytes sizeBytes = 0 := by
  simp [memoryExpansionCost]

@[simp] theorem memoryAccessExpansionCost_zero_length (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 0 = 0 := by
  simp [memoryAccessExpansionCost]

theorem memoryExpansionCost_eq
    (oldSizeBytes newSizeBytes : Nat) :
    memoryExpansionCost oldSizeBytes newSizeBytes =
      memoryCost (memoryWords newSizeBytes) - memoryCost (memoryWords oldSizeBytes) := rfl

theorem memoryAccessExpansionCost_eq
    (sizeBytes offset length : Nat) :
    memoryAccessExpansionCost sizeBytes offset length =
      memoryCost (memoryWords (evmMemExpand sizeBytes offset length)) -
        memoryCost (memoryWords sizeBytes) := rfl

theorem memoryAccessExpansionCost_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset length = 0 := by
  simp [memoryAccessExpansionCost, memoryExpansionCost, h_no_growth]

theorem memoryAccessExpansionCost_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes offset length h_access)

theorem memoryAccessExpansionCost_mload_eq (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 32 =
      memoryExpansionCost sizeBytes
        (max sizeBytes (roundUpTo32 (offset + 32))) := by
  simp [memoryAccessExpansionCost, evmMemExpand_word_eq]

theorem memoryAccessExpansionCost_mstore_eq (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 32 =
      memoryExpansionCost sizeBytes
        (max sizeBytes (roundUpTo32 (offset + 32))) := by
  exact memoryAccessExpansionCost_mload_eq sizeBytes offset

theorem memoryAccessExpansionCost_mstore8_eq (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 1 =
      memoryExpansionCost sizeBytes
        (max sizeBytes (roundUpTo32 (offset + 1))) := by
  simp [memoryAccessExpansionCost, evmMemExpand_byte_eq]

theorem memoryAccessExpansionCost_mload_eq_zero_of_no_growth
    {sizeBytes offset : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset 32 = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth

theorem memoryAccessExpansionCost_mstore_eq_zero_of_no_growth
    {sizeBytes offset : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset 32 = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth

theorem memoryAccessExpansionCost_mstore8_eq_zero_of_no_growth
    {sizeBytes offset : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset 1 = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 1 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth

theorem memoryAccessExpansionCost_mload_eq_zero_of_access_le
    {sizeBytes offset : Nat}
    (h_access : roundUpTo32 (offset + 32) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access

theorem memoryAccessExpansionCost_mstore_eq_zero_of_access_le
    {sizeBytes offset : Nat}
    (h_access : roundUpTo32 (offset + 32) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access

theorem memoryAccessExpansionCost_mstore8_eq_zero_of_access_le
    {sizeBytes offset : Nat}
    (h_access : roundUpTo32 (offset + 1) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 1 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access

end MemoryGas
end EvmAsm.Evm64
