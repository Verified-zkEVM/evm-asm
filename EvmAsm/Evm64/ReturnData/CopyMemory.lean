/-
  EvmAsm.Evm64.ReturnData.CopyMemory

  Destination-address bridge for RETURNDATACOPY copied bytes
  (GH #107 / GH #114).
-/

module

public import Mathlib.Data.List.GetD
public import EvmAsm.Evm64.ReturnData.CopyExec

@[expose] public section

namespace EvmAsm.Evm64
namespace ReturnDataCopyMemory

/-- First destination memory byte written by RETURNDATACOPY. -/
def destinationStart (args : ReturnDataCopyArgs.Args) : Nat :=
  ReturnDataCopyArgs.destinationOffsetNat args

/-- One-past-the-end destination memory byte written by RETURNDATACOPY. -/
def destinationEnd (args : ReturnDataCopyArgs.Args) : Nat :=
  destinationStart args + ReturnDataCopyArgs.sizeNat args

/-- Destination-relative index for a concrete memory byte address. -/
def writeIndex (args : ReturnDataCopyArgs.Args) (addr : Nat) : Nat :=
  addr - destinationStart args

/-- Prop-valued range predicate for addresses written by RETURNDATACOPY. -/
def writesAddress (args : ReturnDataCopyArgs.Args) (addr : Nat) : Prop :=
  destinationStart args ≤ addr ∧ addr < destinationEnd args

instance (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    Decidable (writesAddress args addr) := by
  unfold writesAddress
  infer_instance

/-- Byte written at `addr` by RETURNDATACOPY, or zero outside the destination
    range. Distinctive token: ReturnDataCopyMemory.copyWriteByteAt #107 #114. -/
def copyWriteByteAt
    (data : List (BitVec 8)) (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    BitVec 8 :=
  if _ : writesAddress args addr then
    (ReturnDataCopyExec.copiedBytesFromArgs data args).getD (writeIndex args addr) 0
  else
    0

theorem destinationStart_eq (args : ReturnDataCopyArgs.Args) :
    destinationStart args = args.destOffset.toNat := rfl

theorem destinationEnd_eq (args : ReturnDataCopyArgs.Args) :
    destinationEnd args = args.destOffset.toNat + args.size.toNat := rfl

theorem writeIndex_eq (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    writeIndex args addr = addr - args.destOffset.toNat := rfl

theorem writesAddress_iff (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    writesAddress args addr ↔
      args.destOffset.toNat ≤ addr ∧ addr < args.destOffset.toNat + args.size.toNat := by
  rfl

theorem writesAddress_at_destination_add
    {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    writesAddress args (destinationStart args + i) := by
  unfold writesAddress destinationEnd destinationStart ReturnDataCopyArgs.destinationOffsetNat
    ReturnDataCopyArgs.sizeNat
  omega

theorem writeIndex_at_destination_add
    (args : ReturnDataCopyArgs.Args) (i : Nat) :
    writeIndex args (destinationStart args + i) = i := by
  unfold writeIndex
  omega

theorem copyWriteByteAt_outside
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {addr : Nat}
    (h : ¬ writesAddress args addr) :
    copyWriteByteAt data args addr = 0 := by
  rw [copyWriteByteAt]
  rw [dif_neg h]

theorem copyWriteByteAt_at_destination_add
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt data args (destinationStart args + i) =
      (ReturnDataCopyExec.copiedBytesFromArgs data args)[i]'(by
        simpa [ReturnDataCopyExec.copiedBytesFromArgs_length] using h) := by
  rw [copyWriteByteAt]
  rw [dif_pos (writesAddress_at_destination_add h)]
  rw [writeIndex_at_destination_add]
  exact List.getD_eq_getElem
    (l := ReturnDataCopyExec.copiedBytesFromArgs data args) (d := 0)
    (by simpa [ReturnDataCopyExec.copiedBytesFromArgs_length] using h)

theorem copyWriteByteAt_at_destination_add_eq_returnDataByte
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt data args (destinationStart args + i) =
      ReturnData.byte data (args.dataOffset.toNat + i) := by
  rw [copyWriteByteAt_at_destination_add h]
  exact ReturnDataCopyExec.copiedBytesFromArgs_get h

theorem copyWriteByteAt_at_destination_add_of_in_bounds
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : args.dataOffset.toNat + i < data.length) :
    copyWriteByteAt data args (destinationStart args + i) =
      data[args.dataOffset.toNat + i] := by
  rw [copyWriteByteAt_at_destination_add_eq_returnDataByte h]
  exact ReturnData.byte_of_lt hsrc

theorem copyWriteByteAt_at_destination_add_of_out_of_bounds
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : data.length ≤ args.dataOffset.toNat + i) :
    copyWriteByteAt data args (destinationStart args + i) = 0 := by
  rw [copyWriteByteAt_at_destination_add_eq_returnDataByte h]
  exact ReturnData.byte_of_ge hsrc

@[simp] theorem copyWriteByteAt_zero_size
    (data : List (BitVec 8)) (destOffset dataOffset : EvmWord) (addr : Nat) :
    copyWriteByteAt data (ReturnDataCopyArgs.copyArgs destOffset dataOffset 0) addr = 0 := by
  apply copyWriteByteAt_outside
  intro h
  unfold writesAddress destinationEnd destinationStart ReturnDataCopyArgs.destinationOffsetNat
    ReturnDataCopyArgs.sizeNat ReturnDataCopyArgs.copyArgs at h
  simp at h
  omega

end ReturnDataCopyMemory
end EvmAsm.Evm64
