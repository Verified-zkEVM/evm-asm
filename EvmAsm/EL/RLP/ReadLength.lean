/-
  EvmAsm.EL.RLP.ReadLength

  Branch lemmas for the executable RLP length decoder.
-/
module

public import EvmAsm.EL.RLP.Decode

@[expose] public section

namespace EvmAsm.EL.RLP

/-! ## readLength branch bridges -/

theorem readLength_eq_of_takeBytes {bs lenBytes rest : List Byte} {n : Nat}
    (h : takeBytes bs n = some (lenBytes, rest)) :
    readLength bs n =
      match lenBytes with
      | [] => some (0, rest)
      | b :: _ =>
          if lenBytes.length > 1 && b == (0 : Byte) then none
          else some (Nat.fromBytesBE lenBytes, rest) := by
  cases lenBytes with
  | nil => simp [readLength, h]
  | cons b tail => simp [readLength, h]

theorem readLength_none_of_takeBytes_none {bs : List Byte} {n : Nat}
    (h : takeBytes bs n = none) :
    readLength bs n = none := by
  simp [readLength, h]

theorem readLength_some_of_takeBytes_nil {bs rest : List Byte} {n : Nat}
    (h : takeBytes bs n = some ([], rest)) :
    readLength bs n = some (0, rest) := by
  simp [readLength, h]

theorem readLength_none_of_takeBytes_leading_zero {bs rest tail : List Byte}
    {b : Byte} {n : Nat}
    (h : takeBytes bs n = some ((0 : Byte) :: b :: tail, rest)) :
    readLength bs n = none := by
  simp [readLength, h]

theorem readLength_some_of_takeBytes_single {bs rest : List Byte}
    {b : Byte} {n : Nat}
    (h : takeBytes bs n = some ([b], rest)) :
    readLength bs n = some (b.toNat, rest) := by
  simp [readLength, h, Nat.fromBytesBE]

theorem readLength_some_of_takeBytes_nonzero {bs rest tail : List Byte}
    {b : Byte} {n : Nat}
    (h : takeBytes bs n = some (b :: tail, rest))
    (hne : b ≠ (0 : Byte)) :
    readLength bs n = some (Nat.fromBytesBE (b :: tail), rest) := by
  cases tail with
  | nil => simp [readLength, h, Nat.fromBytesBE]
  | cons c tail =>
      have hb : ¬ b = (0#8 : Byte) := by
        intro hz
        exact hne hz
      simp [readLength, h, hb]

end EvmAsm.EL.RLP
