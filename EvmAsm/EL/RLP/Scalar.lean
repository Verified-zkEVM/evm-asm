/-
  EvmAsm.EL.RLP.Scalar

  RLP **scalar** encoding (ACL2 `rlp-encode-scalar`): a nonnegative integer is
  encoded as its minimal big-endian byte representation (no leading zeros), then
  byte-string-encoded. Scalars are how Ethereum encodes nonces, balances, gas
  values, and lengths. The round-trip and injectivity fall out of the merged
  byte-string round-trip (`decode_encode_bytes`) and the big-endian bijection
  (`Nat.fromBytesBE_toBytesBE`).
-/

import EvmAsm.EL.RLP.Properties

namespace EvmAsm.EL.RLP

/-- Encode a scalar (nonnegative integer) as RLP: minimal big-endian bytes, then
    a byte string. `0 ↦ [0x80]` (the empty byte string). -/
def encodeScalar (n : Nat) : List Byte :=
  encodeBytes (Nat.toBytesBE n)

/-- Decode an RLP **scalar** (canonical nonnegative integer): decode one item; if it
    is a byte string with **no leading zero** (`data.headD 1 ≠ 0` — the empty string is
    the canonical `0`, and a nonzero value's high byte must be nonzero) read it as a
    big-endian natural; otherwise **reject** as non-canonical. (A `.list` head is not a
    scalar.) Matches execution-specs `ethereum_rlp._deserialize_to_uint`
    (`len(decoded) > 0 ∧ decoded[0] == 0 ⇒ DecodingError "non-canonical integer"`). -/
def decodeScalar (bs : List Byte) : Option (Nat × List Byte) := do
  let (item, rest) ← decode bs
  match item with
  | .bytes data => if data.headD 1 = 0 then none else some (Nat.fromBytesBE data, rest)
  | .list _ => none

/-- Scalar round-trip: decoding a scalar's encoding recovers the value, for any
    scalar whose minimal encoding fits the decoder's 8-byte length field
    (`(Nat.toBytesBE n).length < 256 ^ 8` — astronomically permissive). -/
theorem decodeScalar_encodeScalar (n : Nat) (h : (Nat.toBytesBE n).length < 256 ^ 8) :
    decodeScalar (encodeScalar n) = some (n, []) := by
  have hd : decode (encodeScalar n) = some (.bytes (Nat.toBytesBE n), []) :=
    decode_encode_bytes (Nat.toBytesBE n) h
  have hhead : (Nat.toBytesBE n).headD 1 ≠ 0 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [Nat.toBytesBE_zero]; decide
    · obtain ⟨b, tl, hbtl, hb⟩ := Nat.toBytesBE_eq_cons_of_pos n hn
      rw [hbtl]; simpa using hb
  unfold decodeScalar
  rw [hd]
  simp only [Option.bind_eq_bind, Option.bind_some, if_neg hhead, Nat.fromBytesBE_toBytesBE]

/-- `encodeScalar` is injective (within the length bound): distinct scalars have
    distinct encodings. A corollary of the round-trip. -/
theorem encodeScalar_injective {n₁ n₂ : Nat}
    (h₁ : (Nat.toBytesBE n₁).length < 256 ^ 8)
    (h₂ : (Nat.toBytesBE n₂).length < 256 ^ 8)
    (heq : encodeScalar n₁ = encodeScalar n₂) : n₁ = n₂ := by
  have r₁ := decodeScalar_encodeScalar n₁ h₁
  have r₂ := decodeScalar_encodeScalar n₂ h₂
  rw [heq, r₂] at r₁
  simp only [Option.some.injEq, Prod.mk.injEq] at r₁
  exact r₁.1.symm

/-- Right inverse for scalars: a successful scalar decode consumed exactly a
    byte-string encoding whose payload is the scalar's big-endian digits. -/
theorem decodeScalar_eq_some_imp {bs rest : List Byte} {n : Nat}
    (h : decodeScalar bs = some (n, rest)) :
    ∃ data, bs = encodeBytes data ++ rest ∧ Nat.fromBytesBE data = n := by
  unfold decodeScalar at h
  cases hdec : decode bs with
  | none => rw [hdec] at h; simp at h
  | some pair =>
    obtain ⟨item, r⟩ := pair
    rw [hdec] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases item with
    | bytes data =>
      simp only at h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hn, hr⟩ := h
        subst hn; subst hr
        exact ⟨data, by simpa using decode_eq_some_imp_encode bs (.bytes data) r hdec, rfl⟩
    | list items => simp at h

/-! ### Cross-checks

(`Nat.toBytesBE` is well-founded recursive, so it does not reduce under `decide`;
these go through the lemmas / the length bound instead.) -/

/-- The zero scalar encodes to the empty byte string `[0x80]`. -/
example : encodeScalar 0 = [0x80] := by
  rw [encodeScalar, Nat.toBytesBE_zero]; decide

/-- A concrete scalar round-trips (bound discharged via `toBytesBE_length_le`). -/
example : decodeScalar (encodeScalar 1000000) = some (1000000, []) :=
  decodeScalar_encodeScalar 1000000
    (Nat.lt_of_le_of_lt (Nat.toBytesBE_length_le 1000000 8 (by decide)) (by decide))

end EvmAsm.EL.RLP

