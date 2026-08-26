/-
  EvmAsm.Evm64.Code.CopyMemory

  Destination-address bridge for CODECOPY copied bytes (GH #107 / GH #118).
-/

module

public import Mathlib.Data.List.GetD
public import EvmAsm.Evm64.Code.CopyExec

@[expose] public section

namespace EvmAsm.Evm64
namespace CodeCopyMemory

/-- First destination memory byte written by CODECOPY. -/
def destinationStart (args : CodeCopyArgs.Args) : Nat :=
  CodeCopyArgs.destinationOffsetNat args

/-- One-past-the-end destination memory byte written by CODECOPY. -/
def destinationEnd (args : CodeCopyArgs.Args) : Nat :=
  destinationStart args + CodeCopyArgs.sizeNat args

/-- Destination-relative index for a concrete memory byte address. -/
def writeIndex (args : CodeCopyArgs.Args) (addr : Nat) : Nat :=
  addr - destinationStart args

/-- Prop-valued range predicate for addresses written by CODECOPY. -/
def writesAddress (args : CodeCopyArgs.Args) (addr : Nat) : Prop :=
  destinationStart args ≤ addr ∧ addr < destinationEnd args

instance (args : CodeCopyArgs.Args) (addr : Nat) :
    Decidable (writesAddress args addr) := by
  unfold writesAddress
  infer_instance

/-- Byte written at `addr` by CODECOPY, or zero outside the destination range.
    Distinctive token: CodeCopyMemory.copyWriteByteAt #107 #118. -/
def copyWriteByteAt
    (code : List (BitVec 8)) (args : CodeCopyArgs.Args) (addr : Nat) :
    BitVec 8 :=
  if _ : writesAddress args addr then
    (CodeCopyExec.copiedBytesFromArgs code args).getD (writeIndex args addr) 0
  else
    0

theorem destinationStart_eq (args : CodeCopyArgs.Args) :
    destinationStart args = args.destOffset.toNat := rfl

theorem destinationEnd_eq (args : CodeCopyArgs.Args) :
    destinationEnd args = args.destOffset.toNat + args.size.toNat := rfl

theorem writeIndex_eq (args : CodeCopyArgs.Args) (addr : Nat) :
    writeIndex args addr = addr - args.destOffset.toNat := rfl

theorem writesAddress_iff (args : CodeCopyArgs.Args) (addr : Nat) :
    writesAddress args addr ↔
      args.destOffset.toNat ≤ addr ∧ addr < args.destOffset.toNat + args.size.toNat := by
  rfl

theorem writesAddress_at_destination_add
    {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    writesAddress args (destinationStart args + i) := by
  unfold writesAddress destinationEnd destinationStart CodeCopyArgs.destinationOffsetNat
    CodeCopyArgs.sizeNat
  omega

theorem writeIndex_at_destination_add
    (args : CodeCopyArgs.Args) (i : Nat) :
    writeIndex args (destinationStart args + i) = i := by
  unfold writeIndex
  omega

theorem copyWriteByteAt_outside
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {addr : Nat}
    (h : ¬ writesAddress args addr) :
    copyWriteByteAt code args addr = 0 := by
  rw [copyWriteByteAt]
  rw [dif_neg h]

theorem copyWriteByteAt_at_destination_add
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt code args (destinationStart args + i) =
      (CodeCopyExec.copiedBytesFromArgs code args)[i]'(by
        simpa [CodeCopyExec.copiedBytesFromArgs_length] using h) := by
  rw [copyWriteByteAt]
  rw [dif_pos (writesAddress_at_destination_add h)]
  rw [writeIndex_at_destination_add]
  exact List.getD_eq_getElem
    (l := CodeCopyExec.copiedBytesFromArgs code args) (d := 0)
    (by simpa [CodeCopyExec.copiedBytesFromArgs_length] using h)

theorem copyWriteByteAt_at_destination_add_eq_codeByte
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt code args (destinationStart args + i) =
      Code.byte code (args.codeOffset.toNat + i) := by
  rw [copyWriteByteAt_at_destination_add h]
  exact CodeCopyExec.copiedBytesFromArgs_get h

theorem copyWriteByteAt_at_destination_add_of_in_bounds
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : args.codeOffset.toNat + i < code.length) :
    copyWriteByteAt code args (destinationStart args + i) =
      code[args.codeOffset.toNat + i] := by
  rw [copyWriteByteAt_at_destination_add_eq_codeByte h]
  exact Code.byte_of_lt hsrc

theorem copyWriteByteAt_at_destination_add_of_out_of_bounds
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : code.length ≤ args.codeOffset.toNat + i) :
    copyWriteByteAt code args (destinationStart args + i) = 0 := by
  rw [copyWriteByteAt_at_destination_add_eq_codeByte h]
  exact Code.byte_of_ge hsrc

@[simp] theorem copyWriteByteAt_zero_size
    (code : List (BitVec 8)) (destOffset codeOffset : EvmWord) (addr : Nat) :
    copyWriteByteAt code (CodeCopyArgs.copyArgs destOffset codeOffset 0) addr = 0 := by
  apply copyWriteByteAt_outside
  intro h
  unfold writesAddress destinationEnd destinationStart CodeCopyArgs.destinationOffsetNat
    CodeCopyArgs.sizeNat CodeCopyArgs.copyArgs at h
  simp at h
  omega

end CodeCopyMemory
end EvmAsm.Evm64
