/-
  EvmAsm.Evm64.Calldata.Basic

  Pure calldata helpers for CALLDATALOAD/CALLDATACOPY work (GH #104 slice 1).
  CALLDATALOAD reads 32 bytes starting at a byte offset, interprets them as a
  big-endian 256-bit word, and pads reads past the calldata length with zero.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64
namespace Calldata

/-- Read one calldata byte, returning zero past the end of the buffer. -/
def callDataByte (data : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < data.length then data[idx] else 0

/-- Fold one big-endian byte into an accumulator. -/
def appendByte (acc : Nat) (b : BitVec 8) : Nat :=
  acc * 256 + b.toNat

/-- Natural-number assembly of the 32-byte CALLDATALOAD window. This is the
    executable mathematical target; `callDataLoadWord` reduces it modulo
    `2^256` through `BitVec.ofNat 256`. -/
def callDataLoadNat (data : List (BitVec 8)) (offset : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => appendByte acc (callDataByte data (offset + i)))
    0

/-- CALLDATALOAD result word: 32 bytes from calldata, big-endian, zero-padded. -/
def callDataLoadWord (data : List (BitVec 8)) (offset : Nat) : EvmWord :=
  BitVec.ofNat 256 (callDataLoadNat data offset)

theorem callDataByte_of_lt {data : List (BitVec 8)} {idx : Nat}
    (h : idx < data.length) :
    callDataByte data idx = data[idx] := by
  simp [callDataByte, h]

theorem callDataByte_of_ge {data : List (BitVec 8)} {idx : Nat}
    (h : data.length ≤ idx) :
    callDataByte data idx = 0 := by
  simp [callDataByte, show ¬idx < data.length from by omega]

@[simp] theorem callDataByte_nil (idx : Nat) :
    callDataByte [] idx = 0 := by
  exact callDataByte_of_ge (data := []) (idx := idx) (by simp)

@[simp] theorem appendByte_zero :
    appendByte 0 0 = 0 := rfl

theorem callDataLoadNat_nil (offset : Nat) :
    callDataLoadNat [] offset = 0 := by
  have hmul : ∀ xs : List Nat, List.foldl (fun acc (_ : Nat) => acc * 256) 0 xs = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ xs ih => simpa [List.foldl_cons] using ih
  simpa [callDataLoadNat, appendByte] using hmul (List.range 32)

theorem callDataLoadWord_nil (offset : Nat) :
    callDataLoadWord [] offset = 0 := by
  rw [callDataLoadWord, callDataLoadNat_nil]
  rfl

end Calldata
end EvmAsm.Evm64
