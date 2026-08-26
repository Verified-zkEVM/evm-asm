/-
  EvmAsm.Evm64.MemoryGas

  Pure EVM memory expansion gas helpers for issue #118.
-/

module

public import EvmAsm.Evm64.Memory

@[expose] public section

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

/--
  Dynamic gas for RETURN memory output. RETURN charges memory expansion for
  the output byte slice, but no per-word copy charge.
-/
def returnDynamicCost (sizeBytes offset length : Nat) : Nat :=
  memoryAccessExpansionCost sizeBytes offset length

/--
  Dynamic gas for REVERT memory output. REVERT has the same memory-expansion
  shape as RETURN and no per-word copy charge.
-/
def revertDynamicCost (sizeBytes offset length : Nat) : Nat :=
  memoryAccessExpansionCost sizeBytes offset length

@[simp] theorem returnDynamicCost_zero_length (sizeBytes offset : Nat) :
    returnDynamicCost sizeBytes offset 0 = 0 := by
  simp [returnDynamicCost]

@[simp] theorem revertDynamicCost_zero_length (sizeBytes offset : Nat) :
    revertDynamicCost sizeBytes offset 0 = 0 := by
  simp [revertDynamicCost]

theorem returnDynamicCost_eq
    (sizeBytes offset length : Nat) :
    returnDynamicCost sizeBytes offset length =
      memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length) := rfl

theorem revertDynamicCost_eq
    (sizeBytes offset length : Nat) :
    revertDynamicCost sizeBytes offset length =
      memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length) := rfl

theorem returnDynamicCost_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    returnDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth

theorem revertDynamicCost_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    revertDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth

theorem returnDynamicCost_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    returnDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access

theorem revertDynamicCost_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    revertDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access

/-- KECCAK256/SHA3 dynamic gas charged per 32-byte input chunk. -/
def keccakGasPerWord : Nat := 6

/--
  KECCAK256 dynamic gas: per-word input charge plus memory expansion caused by
  the input range.
-/
def keccakDynamicCost (sizeBytes offset length : Nat) : Nat :=
  keccakGasPerWord * memoryWords length +
    memoryAccessExpansionCost sizeBytes offset length

@[simp] theorem keccakDynamicCost_zero_length (sizeBytes offset : Nat) :
    keccakDynamicCost sizeBytes offset 0 = 0 := by
  simp [keccakDynamicCost, keccakGasPerWord]

theorem keccakDynamicCost_eq
    (sizeBytes offset length : Nat) :
    keccakDynamicCost sizeBytes offset length =
      keccakGasPerWord * memoryWords length +
        memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length) := rfl

theorem keccakDynamicCost_eq_word_charge_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    keccakDynamicCost sizeBytes offset length =
      keccakGasPerWord * memoryWords length := by
  simp [keccakDynamicCost,
    memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth]

theorem keccakDynamicCost_eq_word_charge_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    keccakDynamicCost sizeBytes offset length =
      keccakGasPerWord * memoryWords length := by
  exact keccakDynamicCost_eq_word_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes offset length h_access)

/-- Dynamic copy gas charged per 32-byte input chunk for copy-style opcodes. -/
def copyGasPerWord : Nat := 3

/-- Number of 32-byte chunks charged by copy-style opcode dynamic gas. -/
def memoryCopyWords (length : Nat) : Nat :=
  memoryWords length

/--
  Generic dynamic gas for copy-style memory writes: per-word copy charge plus
  memory expansion caused by the destination range.
-/
def memoryCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  copyGasPerWord * memoryCopyWords length +
    memoryAccessExpansionCost sizeBytes dstOffset length

/-- CALLDATACOPY dynamic gas: copy charge plus destination memory expansion. -/
def calldataCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  memoryCopyDynamicCost sizeBytes dstOffset length

/-- CODECOPY dynamic gas: copy charge plus destination memory expansion. -/
def codeCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  memoryCopyDynamicCost sizeBytes dstOffset length

/-- RETURNDATACOPY dynamic gas: copy charge plus destination memory expansion. -/
def returndataCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  memoryCopyDynamicCost sizeBytes dstOffset length

@[simp] theorem memoryCopyWords_zero : memoryCopyWords 0 = 0 := by
  simp [memoryCopyWords]

@[simp] theorem memoryCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    memoryCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [memoryCopyDynamicCost, copyGasPerWord]

@[simp] theorem calldataCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    calldataCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [calldataCopyDynamicCost]

@[simp] theorem codeCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    codeCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [codeCopyDynamicCost]

@[simp] theorem returndataCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    returndataCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [returndataCopyDynamicCost]

theorem memoryCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    memoryCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryExpansionCost sizeBytes (evmMemExpand sizeBytes dstOffset length) := rfl

theorem calldataCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    calldataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryAccessExpansionCost sizeBytes dstOffset length := rfl

theorem codeCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    codeCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryAccessExpansionCost sizeBytes dstOffset length := rfl

theorem returndataCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    returndataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryAccessExpansionCost sizeBytes dstOffset length := rfl

theorem memoryCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    memoryCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  simp [memoryCopyDynamicCost,
    memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth]

theorem calldataCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    calldataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact memoryCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth

theorem codeCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    codeCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact memoryCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth

theorem returndataCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    returndataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact memoryCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth

theorem calldataCopyDynamicCost_eq_copy_charge_of_access_le
    {sizeBytes dstOffset length : Nat}
    (h_access : roundUpTo32 (dstOffset + length) ≤ sizeBytes) :
    calldataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact calldataCopyDynamicCost_eq_copy_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes dstOffset length h_access)

theorem codeCopyDynamicCost_eq_copy_charge_of_access_le
    {sizeBytes dstOffset length : Nat}
    (h_access : roundUpTo32 (dstOffset + length) ≤ sizeBytes) :
    codeCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact codeCopyDynamicCost_eq_copy_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes dstOffset length h_access)

theorem returndataCopyDynamicCost_eq_copy_charge_of_access_le
    {sizeBytes dstOffset length : Nat}
    (h_access : roundUpTo32 (dstOffset + length) ≤ sizeBytes) :
    returndataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact returndataCopyDynamicCost_eq_copy_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes dstOffset length h_access)

end MemoryGas
end EvmAsm.Evm64
