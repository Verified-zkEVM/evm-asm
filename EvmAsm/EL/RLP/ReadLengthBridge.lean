/-
  EvmAsm.EL.RLP.ReadLengthBridge

  Reusable result bridge for RLP long-form length-field decoding (GH #120).
-/

module

public import EvmAsm.EL.RLP.ReadLength

@[expose] public section

namespace EvmAsm.EL.RLP

namespace ReadLengthBridge

/-- Decoded long-form RLP length field plus the input remainder after the
    length bytes. -/
structure LengthFieldResult where
  length : Nat
  rest : List Byte
  deriving Repr

/--
Decode exactly `n` bytes as a canonical big-endian RLP length field.

This is a small executable-spec bridge over `readLength`: later RISC-V
decoder phases can target this result object without duplicating the
leading-zero rejection and remainder plumbing.

Distinctive token: RLP.ReadLengthBridge.decodeLengthField? #120.
-/
def decodeLengthField? (bs : List Byte) (n : Nat) :
    Option LengthFieldResult := do
  let (lenVal, rest) ← readLength bs n
  some { length := lenVal, rest := rest }

theorem decodeLengthField?_eq_some_iff
    {bs : List Byte} {n lenVal : Nat} {rest : List Byte} :
    decodeLengthField? bs n = some { length := lenVal, rest := rest } ↔
      readLength bs n = some (lenVal, rest) := by
  constructor
  · unfold decodeLengthField?
    cases readLength bs n with
    | none => simp
    | some decoded =>
        cases decoded with
        | mk lenVal' rest' =>
            intro h
            injection h with h_result
            cases h_result
            rfl
  · intro h
    simp [decodeLengthField?, h]

theorem decodeLengthField?_none_of_readLength_none
    {bs : List Byte} {n : Nat} (h_read : readLength bs n = none) :
    decodeLengthField? bs n = none := by
  simp [decodeLengthField?, h_read]

theorem decodeLengthField?_eq_none_iff (bs : List Byte) (n : Nat) :
    decodeLengthField? bs n = none ↔ readLength bs n = none := by
  unfold decodeLengthField?
  cases h_read : readLength bs n with
  | none => simp
  | some decoded =>
      cases decoded
      simp

theorem decodeLengthField?_some_of_readLength
    {bs rest : List Byte} {n lenVal : Nat}
    (h_read : readLength bs n = some (lenVal, rest)) :
    decodeLengthField? bs n = some { length := lenVal, rest := rest } := by
  exact (decodeLengthField?_eq_some_iff).2 h_read

theorem decodeLengthField?_none_of_takeBytes_none
    {bs : List Byte} {n : Nat} (h_take : takeBytes bs n = none) :
    decodeLengthField? bs n = none := by
  exact decodeLengthField?_none_of_readLength_none
    (readLength_none_of_takeBytes_none h_take)

theorem decodeLengthField?_none_of_leading_zero
    {bs rest tail : List Byte} {b : Byte} {n : Nat}
    (h_take : takeBytes bs n = some ((0 : Byte) :: b :: tail, rest)) :
    decodeLengthField? bs n = none := by
  exact decodeLengthField?_none_of_readLength_none
    (readLength_none_of_takeBytes_leading_zero h_take)

theorem decodeLengthField?_some_of_takeBytes_nil
    {bs rest : List Byte} {n : Nat}
    (h_take : takeBytes bs n = some ([], rest)) :
    decodeLengthField? bs n = some { length := 0, rest := rest } := by
  exact decodeLengthField?_some_of_readLength
    (readLength_some_of_takeBytes_nil h_take)

theorem decodeLengthField?_some_of_takeBytes_single
    {bs rest : List Byte} {b : Byte} {n : Nat}
    (h_take : takeBytes bs n = some ([b], rest)) :
    decodeLengthField? bs n = some { length := b.toNat, rest := rest } := by
  exact decodeLengthField?_some_of_readLength
    (readLength_some_of_takeBytes_single h_take)

theorem decodeLengthField?_some_of_takeBytes_nonzero
    {bs rest tail : List Byte} {b : Byte} {n : Nat}
    (h_take : takeBytes bs n = some (b :: tail, rest))
    (hne : b ≠ (0 : Byte)) :
    decodeLengthField? bs n =
      some { length := Nat.fromBytesBE (b :: tail), rest := rest } := by
  exact decodeLengthField?_some_of_readLength
    (readLength_some_of_takeBytes_nonzero h_take hne)

theorem decodeLengthField?_rest_of_some
    {bs : List Byte} {n : Nat} {out : LengthFieldResult}
    (h_decode : decodeLengthField? bs n = some out) :
    ∃ lenVal rest, readLength bs n = some (lenVal, rest) ∧
      out.length = lenVal ∧ out.rest = rest := by
  unfold decodeLengthField? at h_decode
  cases h_read : readLength bs n with
  | none => simp [h_read] at h_decode
  | some decoded =>
      cases decoded with
      | mk lenVal rest =>
          simp [h_read] at h_decode
          cases h_decode
          exact ⟨lenVal, rest, rfl, rfl, rfl⟩

end ReadLengthBridge

end EvmAsm.EL.RLP
