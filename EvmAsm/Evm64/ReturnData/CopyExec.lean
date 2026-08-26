/-
  EvmAsm.Evm64.ReturnData.CopyExec

  Bridge from RETURNDATACOPY stack arguments to executable returndata bytes
  (GH #107 / GH #114).
-/

module

public import EvmAsm.Evm64.ReturnData.Basic
public import EvmAsm.Evm64.ReturnData.CopyArgs

@[expose] public section

namespace EvmAsm.Evm64
namespace ReturnDataCopyExec

/-- Bytes written by RETURNDATACOPY for a decoded stack-argument record.
    Distinctive token: ReturnDataCopyExec.copiedBytesFromArgs. -/
def copiedBytesFromArgs
    (data : List (BitVec 8)) (args : ReturnDataCopyArgs.Args) : List (BitVec 8) :=
  ReturnData.copyBytes
    data (ReturnDataCopyArgs.sourceOffsetNat args) (ReturnDataCopyArgs.sizeNat args)

theorem copiedBytesFromArgs_eq
    (data : List (BitVec 8)) (args : ReturnDataCopyArgs.Args) :
    copiedBytesFromArgs data args =
      ReturnData.copyBytes data args.dataOffset.toNat args.size.toNat := rfl

@[simp] theorem copiedBytesFromArgs_length
    (data : List (BitVec 8)) (args : ReturnDataCopyArgs.Args) :
    (copiedBytesFromArgs data args).length = args.size.toNat := by
  simp [copiedBytesFromArgs, ReturnDataCopyArgs.sizeNat]

@[simp] theorem copiedBytesFromArgs_zero_size
    (data : List (BitVec 8)) (destOffset dataOffset : EvmWord) :
    copiedBytesFromArgs data (ReturnDataCopyArgs.copyArgs destOffset dataOffset 0) = [] := by
  simp [copiedBytesFromArgs, ReturnDataCopyArgs.copyArgs,
    ReturnDataCopyArgs.sourceOffsetNat, ReturnDataCopyArgs.sizeNat]

theorem copiedBytesFromArgs_get
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    (copiedBytesFromArgs data args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = ReturnData.byte data (args.dataOffset.toNat + i) := by
  unfold copiedBytesFromArgs ReturnDataCopyArgs.sourceOffsetNat ReturnDataCopyArgs.sizeNat
  exact ReturnData.copyBytes_get h

theorem copiedBytesFromArgs_get_of_in_bounds
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : args.dataOffset.toNat + i < data.length) :
    (copiedBytesFromArgs data args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = data[args.dataOffset.toNat + i] := by
  rw [copiedBytesFromArgs_get h, ReturnData.byte_of_lt hsrc]

theorem copiedBytesFromArgs_get_of_out_of_bounds
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : data.length ≤ args.dataOffset.toNat + i) :
    (copiedBytesFromArgs data args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = 0 := by
  rw [copiedBytesFromArgs_get h, ReturnData.byte_of_ge hsrc]

@[simp] theorem copiedBytesFromArgs_nil
    (args : ReturnDataCopyArgs.Args) :
    copiedBytesFromArgs [] args = List.replicate args.size.toNat 0 := by
  simp [copiedBytesFromArgs_eq]

end ReturnDataCopyExec
end EvmAsm.Evm64
