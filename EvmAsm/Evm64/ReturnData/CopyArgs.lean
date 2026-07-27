/-
  EvmAsm.Evm64.ReturnData.CopyArgs

  Pure stack-argument record for RETURNDATACOPY executable-spec bridges
  (GH #107 / GH #114).
-/

import EvmAsm.Evm64.EvmWord
import EvmAsm.Evm64.MemoryGas

namespace EvmAsm.Evm64
namespace ReturnDataCopyArgs

/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr

/-- RETURNDATACOPY stack arguments: destination memory offset, returndata
    source offset, and byte size. -/
structure Args where
  destOffset : EvmWord
  dataOffset : EvmWord
  size : EvmWord
  deriving Repr

/-- RETURNDATACOPY pops three stack words. -/
def stackArgumentCount : Nat := 3

/-- RETURNDATACOPY pushes no result words. -/
def resultCount : Nat := 0

/-- RETURNDATACOPY has one destination memory range. -/
def memoryRangeCount : Nat := 1

/-- Convenience builder for RETURNDATACOPY stack arguments.
    Distinctive token: ReturnDataCopyArgs.copyArgs #107 #114. -/
def copyArgs (destOffset dataOffset size : EvmWord) : Args :=
  { destOffset := destOffset, dataOffset := dataOffset, size := size }

/-- Destination memory range written by RETURNDATACOPY. -/
def destinationRange (args : Args) : MemoryRange :=
  { offset := args.destOffset, size := args.size }

/-- Destination memory offset as a host `Nat` for executable memory helpers. -/
def destinationOffsetNat (args : Args) : Nat :=
  args.destOffset.toNat

/-- Returndata source offset as a host `Nat` for executable returndata helpers. -/
def sourceOffsetNat (args : Args) : Nat :=
  args.dataOffset.toNat

/-- Byte count as a host `Nat` for executable memory/returndata helpers. -/
def sizeNat (args : Args) : Nat :=
  args.size.toNat

/-- Dynamic gas caused by RETURNDATACOPY's copy charge and destination memory
    expansion. -/
def copyDynamicCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.returndataCopyDynamicCost
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

theorem copyDynamicCostFromArgs_eq
    (sizeBytes : Nat) (args : Args) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.returndataCopyDynamicCost
        sizeBytes args.destOffset.toNat args.size.toNat := rfl

@[simp] theorem copyDynamicCostFromArgs_zero_size
    (sizeBytes : Nat) (destOffset dataOffset : EvmWord) :
    copyDynamicCostFromArgs sizeBytes
      (copyArgs destOffset dataOffset 0) = 0 := by
  simp [copyDynamicCostFromArgs, copyArgs, destinationOffsetNat, sizeNat]

theorem copyDynamicCostFromArgs_eq_copy_charge_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.destOffset.toNat args.size.toNat = sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.returndataCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth

theorem copyDynamicCostFromArgs_eq_copy_charge_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.destOffset.toNat + args.size.toNat) ≤ sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.returndataCopyDynamicCost_eq_copy_charge_of_access_le h_access

end ReturnDataCopyArgs
end EvmAsm.Evm64
