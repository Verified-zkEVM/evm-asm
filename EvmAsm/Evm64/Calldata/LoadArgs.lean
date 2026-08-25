/-
  EvmAsm.Evm64.Calldata.LoadArgs

  Pure stack-argument record for CALLDATALOAD (GH #104).
-/

module

public import EvmAsm.Evm64.Calldata.Basic

@[expose] public section

namespace EvmAsm.Evm64
namespace CallDataLoadArgs

/-- CALLDATALOAD stack arguments: the calldata byte offset to load from. -/
structure Args where
  offset : EvmWord
  deriving Repr

/-- CALLDATALOAD pops one stack word. -/
def stackArgumentCount : Nat := 1

/-- CALLDATALOAD pushes one result word. -/
def resultCount : Nat := 1

/-- Convenience builder for CALLDATALOAD stack arguments. -/
def loadArgs (offset : EvmWord) : Args :=
  { offset := offset }

/-- Calldata source offset as a host `Nat` for executable calldata helpers. -/
def offsetNat (args : Args) : Nat :=
  args.offset.toNat

/-- CALLDATALOAD executable helper specialized to decoded stack arguments.
    Distinctive token: CallDataLoadArgs.loadedWordFromArgs. -/
def loadedWordFromArgs (data : List (BitVec 8)) (args : Args) : EvmWord :=
  Calldata.callDataLoadWord data (offsetNat args)

/-- The `i`th byte in the 32-byte CALLDATALOAD window selected by decoded
    stack arguments.  This keeps later stack specs phrased through `Args`
    instead of separately threading host offsets. -/
def windowByteFromArgs
    (data : List (BitVec 8)) (args : Args) (i : Nat) : BitVec 8 :=
  Calldata.callDataByte data (offsetNat args + i)

theorem stackArgumentCount_eq_one : stackArgumentCount = 1 := rfl

theorem resultCount_eq_one : resultCount = 1 := rfl

theorem loadArgs_offset (offset : EvmWord) :
    (loadArgs offset).offset = offset := rfl

theorem offsetNat_eq (args : Args) :
    offsetNat args = args.offset.toNat := rfl

theorem loadedWordFromArgs_eq
    (data : List (BitVec 8)) (args : Args) :
    loadedWordFromArgs data args =
      Calldata.callDataLoadWord data args.offset.toNat := rfl

theorem windowByteFromArgs_eq
    (data : List (BitVec 8)) (args : Args) (i : Nat) :
    windowByteFromArgs data args i =
      Calldata.callDataByte data (args.offset.toNat + i) := rfl

theorem windowByteFromArgs_loadArgs
    (data : List (BitVec 8)) (offset : EvmWord) (i : Nat) :
    windowByteFromArgs data (loadArgs offset) i =
      Calldata.callDataByte data (offset.toNat + i) := rfl

theorem windowByteFromArgs_of_in_bounds
    {data : List (BitVec 8)} {args : Args} {i : Nat}
    (h : offsetNat args + i < data.length) :
    windowByteFromArgs data args i = data[offsetNat args + i] := by
  rw [windowByteFromArgs, Calldata.callDataByte_of_lt h]

theorem windowByteFromArgs_of_out_of_bounds
    {data : List (BitVec 8)} {args : Args} {i : Nat}
    (h : data.length ≤ offsetNat args + i) :
    windowByteFromArgs data args i = 0 := by
  rw [windowByteFromArgs, Calldata.callDataByte_of_ge h]

theorem loadedWordFromArgs_eq_window_fold
    (data : List (BitVec 8)) (args : Args) :
    loadedWordFromArgs data args =
      BitVec.ofNat 256
        ((List.range 32).foldl
          (fun acc i => Calldata.appendByte acc (windowByteFromArgs data args i))
          0) := by
  rfl

@[simp] theorem loadedWordFromArgs_nil (offset : EvmWord) :
    loadedWordFromArgs [] (loadArgs offset) = 0 := by
  simp [loadedWordFromArgs, loadArgs, offsetNat, Calldata.callDataLoadWord_nil]

theorem loadedWordFromArgs_of_ge_length
    {data : List (BitVec 8)} {args : Args}
    (h : data.length ≤ offsetNat args) :
    loadedWordFromArgs data args = 0 := by
  exact Calldata.callDataLoadWord_of_ge_length h

theorem loadedWordFromArgs_loadArgs_of_ge_length
    {data : List (BitVec 8)} {offset : EvmWord}
    (h : data.length ≤ offset.toNat) :
    loadedWordFromArgs data (loadArgs offset) = 0 := by
  exact loadedWordFromArgs_of_ge_length h

theorem loadedWordFromArgs_toNat
    (data : List (BitVec 8)) (args : Args) :
    (loadedWordFromArgs data args).toNat =
      Calldata.callDataLoadNat data args.offset.toNat := by
  exact Calldata.callDataLoadWord_toNat data args.offset.toNat

end CallDataLoadArgs
end EvmAsm.Evm64
