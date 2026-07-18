/-
  EvmAsm.Evm64.Calldata.CopyArgs

  Pure stack-argument record for CALLDATACOPY (GH #104).
-/

import EvmAsm.Evm64.EvmWord
import EvmAsm.Evm64.MemoryGas

namespace EvmAsm.Evm64
namespace CallDataCopyArgs

/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- CALLDATACOPY stack arguments: destination memory offset, calldata source
    offset, and byte size. -/
structure Args where
  destOffset : EvmWord
  dataOffset : EvmWord
  size : EvmWord
  deriving Repr

/-- CALLDATACOPY pops three stack words. -/
def stackArgumentCount : Nat := 3

/-- CALLDATACOPY pushes no result words. -/
def resultCount : Nat := 0

/-- CALLDATACOPY has one destination memory range. -/
def memoryRangeCount : Nat := 1

/-- Convenience builder for CALLDATACOPY stack arguments. -/
def copyArgs (destOffset dataOffset size : EvmWord) : Args :=
  { destOffset := destOffset, dataOffset := dataOffset, size := size }

/-- Destination memory range written by CALLDATACOPY. -/
def destinationRange (args : Args) : MemoryRange :=
  { offset := args.destOffset, size := args.size }

/-- Destination memory offset as a host `Nat` for executable memory helpers. -/
def destinationOffsetNat (args : Args) : Nat :=
  args.destOffset.toNat

/-- Calldata source offset as a host `Nat` for executable calldata helpers. -/
def sourceOffsetNat (args : Args) : Nat :=
  args.dataOffset.toNat

/-- Byte count as a host `Nat` for executable memory/calldata helpers. -/
def sizeNat (args : Args) : Nat :=
  args.size.toNat

/-- Memory expansion caused by the CALLDATACOPY destination range.
    Distinctive token: CallDataCopyArgs.copyMemoryExpansionCostFromArgs. -/
def copyMemoryExpansionCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.memoryAccessExpansionCost
    sizeBytes (destinationOffsetNat args) (sizeNat args)

theorem stackArgumentCount_eq_three : stackArgumentCount = 3 := rfl

theorem resultCount_eq_zero : resultCount = 0 := rfl

theorem memoryRangeCount_eq_one : memoryRangeCount = 1 := rfl

theorem copyArgs_destOffset (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).destOffset = destOffset := rfl

theorem copyArgs_dataOffset (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).dataOffset = dataOffset := rfl

theorem copyArgs_size (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).size = size := rfl

theorem destinationRange_offset (args : Args) :
    (destinationRange args).offset = args.destOffset := rfl

theorem destinationRange_size (args : Args) :
    (destinationRange args).size = args.size := rfl

theorem destinationOffsetNat_eq (args : Args) :
    destinationOffsetNat args = args.destOffset.toNat := rfl

theorem sourceOffsetNat_eq (args : Args) :
    sourceOffsetNat args = args.dataOffset.toNat := rfl

theorem sizeNat_eq (args : Args) :
    sizeNat args = args.size.toNat := rfl

theorem copyMemoryExpansionCostFromArgs_eq
    (sizeBytes : Nat) (args : Args) :
    copyMemoryExpansionCostFromArgs sizeBytes args =
      MemoryGas.memoryAccessExpansionCost
        sizeBytes args.destOffset.toNat args.size.toNat := rfl

@[simp] theorem copyMemoryExpansionCostFromArgs_zero_size
    (sizeBytes : Nat) (destOffset dataOffset : EvmWord) :
    copyMemoryExpansionCostFromArgs sizeBytes
      (copyArgs destOffset dataOffset 0) = 0 := by
  simp [copyMemoryExpansionCostFromArgs, copyArgs, destinationOffsetNat, sizeNat]

theorem copyMemoryExpansionCostFromArgs_eq_zero_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.destOffset.toNat args.size.toNat = sizeBytes) :
    copyMemoryExpansionCostFromArgs sizeBytes args = 0 := by
  exact MemoryGas.memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth

theorem copyMemoryExpansionCostFromArgs_eq_zero_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.destOffset.toNat + args.size.toNat) ≤ sizeBytes) :
    copyMemoryExpansionCostFromArgs sizeBytes args = 0 := by
  exact MemoryGas.memoryAccessExpansionCost_eq_zero_of_access_le h_access

end CallDataCopyArgs
end EvmAsm.Evm64
