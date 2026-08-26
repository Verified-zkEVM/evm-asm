/-
  EvmAsm.Evm64.Code.CopyExec

  Bridge from CODECOPY stack arguments to executable code bytes
  (GH #107 / GH #118).
-/

module

public import EvmAsm.Evm64.Code.Basic
public import EvmAsm.Evm64.Code.CopyArgs

@[expose] public section

namespace EvmAsm.Evm64
namespace CodeCopyExec

/-- Bytes written by CODECOPY for a decoded stack-argument record.
    Distinctive token: CodeCopyExec.copiedBytesFromArgs. -/
def copiedBytesFromArgs
    (code : List (BitVec 8)) (args : CodeCopyArgs.Args) : List (BitVec 8) :=
  Code.copyBytes
    code (CodeCopyArgs.sourceOffsetNat args) (CodeCopyArgs.sizeNat args)

theorem copiedBytesFromArgs_eq
    (code : List (BitVec 8)) (args : CodeCopyArgs.Args) :
    copiedBytesFromArgs code args =
      Code.copyBytes code args.codeOffset.toNat args.size.toNat := rfl

@[simp] theorem copiedBytesFromArgs_length
    (code : List (BitVec 8)) (args : CodeCopyArgs.Args) :
    (copiedBytesFromArgs code args).length = args.size.toNat := by
  simp [copiedBytesFromArgs, CodeCopyArgs.sizeNat]

@[simp] theorem copiedBytesFromArgs_zero_size
    (code : List (BitVec 8)) (destOffset codeOffset : EvmWord) :
    copiedBytesFromArgs code (CodeCopyArgs.copyArgs destOffset codeOffset 0) = [] := by
  simp [copiedBytesFromArgs, CodeCopyArgs.copyArgs,
    CodeCopyArgs.sourceOffsetNat, CodeCopyArgs.sizeNat]

theorem copiedBytesFromArgs_get
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    (copiedBytesFromArgs code args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = Code.byte code (args.codeOffset.toNat + i) := by
  unfold copiedBytesFromArgs CodeCopyArgs.sourceOffsetNat CodeCopyArgs.sizeNat
  exact Code.copyBytes_get h

theorem copiedBytesFromArgs_get_of_in_bounds
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : args.codeOffset.toNat + i < code.length) :
    (copiedBytesFromArgs code args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = code[args.codeOffset.toNat + i] := by
  rw [copiedBytesFromArgs_get h, Code.byte_of_lt hsrc]

theorem copiedBytesFromArgs_get_of_out_of_bounds
    {code : List (BitVec 8)} {args : CodeCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : code.length ≤ args.codeOffset.toNat + i) :
    (copiedBytesFromArgs code args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = 0 := by
  rw [copiedBytesFromArgs_get h, Code.byte_of_ge hsrc]

@[simp] theorem copiedBytesFromArgs_nil
    (args : CodeCopyArgs.Args) :
    copiedBytesFromArgs [] args = List.replicate args.size.toNat 0 := by
  simp [copiedBytesFromArgs_eq]

end CodeCopyExec
end EvmAsm.Evm64
