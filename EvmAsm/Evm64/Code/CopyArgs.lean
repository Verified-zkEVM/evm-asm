/-
  EvmAsm.Evm64.Code.CopyArgs

  Pure stack-argument record for CODECOPY executable-spec bridges
  (GH #107 / GH #118).
-/

import EvmAsm.Evm64.EvmWord
import EvmAsm.Evm64.MemoryGas

namespace EvmAsm.Evm64
namespace CodeCopyArgs

/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- CODECOPY stack arguments: destination memory offset, code source offset,
    and byte size. -/
structure Args where
  destOffset : EvmWord
  codeOffset : EvmWord
  size : EvmWord
  deriving Repr

/-- CODECOPY pops three stack words. -/
def stackArgumentCount : Nat := 3

/-- CODECOPY pushes no result words. -/
def resultCount : Nat := 0

/-- CODECOPY has one destination memory range. -/
def memoryRangeCount : Nat := 1

/-- Convenience builder for CODECOPY stack arguments.
    Distinctive token: CodeCopyArgs.copyArgs #107 #118. -/
def copyArgs (destOffset codeOffset size : EvmWord) : Args :=
  { destOffset := destOffset, codeOffset := codeOffset, size := size }

/-- Destination memory range written by CODECOPY. -/
def destinationRange (args : Args) : MemoryRange :=
  { offset := args.destOffset, size := args.size }

/-- Destination memory offset as a host `Nat` for executable memory helpers. -/
def destinationOffsetNat (args : Args) : Nat :=
  args.destOffset.toNat

/-- Code source offset as a host `Nat` for executable code helpers. -/
def sourceOffsetNat (args : Args) : Nat :=
  args.codeOffset.toNat

/-- Byte count as a host `Nat` for executable memory/code helpers. -/
def sizeNat (args : Args) : Nat :=
  args.size.toNat

/-- Dynamic gas caused by CODECOPY's copy charge and destination memory
    expansion. -/
def copyDynamicCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.codeCopyDynamicCost
    sizeBytes (destinationOffsetNat args) (sizeNat args)

theorem stackArgumentCount_eq_three : stackArgumentCount = 3 := rfl

theorem resultCount_eq_zero : resultCount = 0 := rfl

theorem memoryRangeCount_eq_one : memoryRangeCount = 1 := rfl

theorem copyArgs_destOffset (destOffset codeOffset size : EvmWord) :
    (copyArgs destOffset codeOffset size).destOffset = destOffset := rfl

theorem copyArgs_codeOffset (destOffset codeOffset size : EvmWord) :
    (copyArgs destOffset codeOffset size).codeOffset = codeOffset := rfl

theorem copyArgs_size (destOffset codeOffset size : EvmWord) :
    (copyArgs destOffset codeOffset size).size = size := rfl

theorem destinationRange_offset (args : Args) :
    (destinationRange args).offset = args.destOffset := rfl

theorem destinationRange_size (args : Args) :
    (destinationRange args).size = args.size := rfl

theorem destinationOffsetNat_eq (args : Args) :
    destinationOffsetNat args = args.destOffset.toNat := rfl

theorem sourceOffsetNat_eq (args : Args) :
    sourceOffsetNat args = args.codeOffset.toNat := rfl

theorem sizeNat_eq (args : Args) :
    sizeNat args = args.size.toNat := rfl

theorem copyDynamicCostFromArgs_eq
    (sizeBytes : Nat) (args : Args) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.codeCopyDynamicCost
        sizeBytes args.destOffset.toNat args.size.toNat := rfl

@[simp] theorem copyDynamicCostFromArgs_zero_size
    (sizeBytes : Nat) (destOffset codeOffset : EvmWord) :
    copyDynamicCostFromArgs sizeBytes
      (copyArgs destOffset codeOffset 0) = 0 := by
  simp [copyDynamicCostFromArgs, copyArgs, destinationOffsetNat, sizeNat]

theorem copyDynamicCostFromArgs_eq_copy_charge_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.destOffset.toNat args.size.toNat = sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.codeCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth

theorem copyDynamicCostFromArgs_eq_copy_charge_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.destOffset.toNat + args.size.toNat) ≤ sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.codeCopyDynamicCost_eq_copy_charge_of_access_le h_access

end CodeCopyArgs
end EvmAsm.Evm64
