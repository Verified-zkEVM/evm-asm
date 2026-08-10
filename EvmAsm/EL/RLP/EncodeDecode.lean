/-
  EvmAsm.EL.RLP.EncodeDecode

  **Canonicality: `decode` only ever accepts an encoding** (GH #11896).

      encode_decode : decode bs = some (item, []) → encode item = bs

  ## Why this direction is the one that was missing

  `Properties.lean` proves `decode_encode` — every encoding re-decodes to itself. That
  says nothing about bytes that are *not* an encoding. This module proves the converse:
  a successful decode identifies its input **as** the encoding of the decoded item, so
  the decoder has no non-canonical accepts.

  ⚠️ `encode_injective` is not a substitute: it relates two *encodings* to each other
  (`encode i₁ = encode i₂ → i₁ = i₂`). The content here is about an arbitrary decodable
  byte string.

  ## What it unlocks

  A whole class of `Correspondence` upgrades. The recurring `.machineOnly` reason is
  "SpecRef carries ENCODE but no decoder, so there is nothing to bridge to". Composing
  a SpecRef encoder with `decode_encode` yields a reference *decoder* — but only for
  bytes already known to be an encoding. Transferring the differential for **arbitrary
  input** is exactly this theorem. #11692 (`withdrawal_decode`) is the worked instance:
  from a successful decode you can build the `Withdrawal` and get
  `withdrawalToRlpItem w = .list [...]`; what remains is `bs = encode (.list [...])`,
  i.e. this.

  ## Where the canonicality actually lives

  The theorem is true because `decodeAux`/`readLength` reject every non-minimal
  encoding, and it is worth naming the four checks since the proof is exactly the
  bookkeeping that each one is enough:

  1. a single byte `< 0x80` **must** use the one-byte form — the short-string branch
     returns `none` for `data = [b]` with `b < 0x80` (`Decode.lean:78`);
  2. long forms **must not** encode a length `≤ 55` (`Decode.lean:85`, `:101`), so the
     short form is mandatory below 56;
  3. a multi-byte length field **must not** have a leading zero
     (`readLength`, `Decode.lean:25`) — this is what makes the length field minimal,
     and it is what `Nat.toBytesBE_fromBytesBE_of_canonical` needs;
  4. a list payload must be consumed **exactly** (`leftover.isEmpty`).

  Drop any one and the theorem is false. (2) is why `Nat.toBytesBE` of the recovered
  length reproduces the original length bytes rather than a shorter field.

  ## Shape

  Mutual and fuel-parametric, mirroring `decode_encode_mutual` in the other direction:
  one induction on the shared budget carries the `decodeAux` and `decodeItems`
  statements together, since both step it down by one. The `rest` generalisation is
  essential — `decodeAux` returns a remainder, so the honest statement is
  `encode item ++ rest = bs`, and only the top-level wrapper specialises `rest := []`.
-/

import EvmAsm.EL.RLP.Properties

namespace EvmAsm.EL.RLP

/-- Long byte-string encoder shape (`payload > 55`), the `encodeBytes` counterpart of
    the existing `encode_list_long`. Not present in `Properties.lean`, which has
    `encodeBytes_nil` / `_single_small` / `_single_large` / `_pair` / `_triple` and the
    short generic form but no long one. -/
private theorem encodeBytes_long (data : List Byte) (h : 55 < data.length) :
    encodeBytes data
      = BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)
          :: (Nat.toBytesBE data.length ++ data) := by
  match data with
  | [] => simp at h
  | [_] => exact absurd h (by simp)
  | b :: c :: tl =>
    simp only [encodeBytes]
    rw [if_neg (Nat.not_le.mpr h)]
    rfl

/-- **Canonicality, mutual form.** A successful decode identifies its input as the
    encoding of what it produced, followed by the returned remainder. -/
theorem encode_decode_mutual : ∀ n : Nat,
    (∀ (bs : List Byte) (item : RLPItem) (rest : List Byte),
        decodeAux n bs = some (item, rest) → encode item ++ rest = bs)
    ∧ (∀ (bs : List Byte) (items : List RLPItem) (rest : List Byte),
        decodeItems n bs = some (items, rest) → encode.encodeItems items ++ rest = bs) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro bs item rest hsome
      rw [decodeAux_zero_fuel] at hsome
      exact absurd hsome (by simp)
    · intro bs items rest hsome
      match bs with
      | [] =>
        simp only [decodeItems] at hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨hi, hr⟩ := hsome
        subst hi; subst hr
        simp [encode.encodeItems]
      | b :: bs' =>
        simp only [decodeItems] at hsome
        exact absurd hsome (by simp)
  | succ n ih =>
    obtain ⟨ihAux, ihItems⟩ := ih
    refine ⟨?_, ?_⟩
    · -- `decodeAux (n+1)`
      intro bs item rest hsome
      match bs with
      | [] =>
        rw [decodeAux_nil] at hsome
        exact absurd hsome (by simp)
      | pfx :: bs' =>
        simp only [decodeAux] at hsome
        by_cases h1 : pfx.toNat < 0x80
        · -- Single byte: `encodeBytes [pfx] = [pfx]` exactly because `pfx < 0x80`.
          simp only [h1, if_true, Option.some.injEq, Prod.mk.injEq] at hsome
          obtain ⟨hi, hr⟩ := hsome
          subst hi; subst hr
          simp [encode, encodeBytes, h1]
        · simp only [h1, if_false] at hsome
          by_cases h2 : pfx.toNat ≤ 0xB7
          · -- Short string.
            simp only [h2, if_true] at hsome
            cases htb : takeBytes bs' (pfx.toNat - 0x80) with
            | none => rw [htb] at hsome; simp at hsome
            | some pr =>
              obtain ⟨data, rest'⟩ := pr
              rw [htb] at hsome
              simp only [Option.bind_eq_bind, Option.bind_some] at hsome
              obtain ⟨hcat, hlen⟩ := takeBytes_eq_some_imp htb
              -- The canonicality check on a length-1 payload.
              match data with
              | [b] =>
                by_cases hb : b.toNat < 0x80
                · simp only [hb, if_true] at hsome; simp at hsome
                · simp only [hb, if_false, Option.some.injEq, Prod.mk.injEq] at hsome
                  obtain ⟨hi, hr⟩ := hsome
                  subst hi; subst hr
                  -- `len = 1`, so `pfx = 0x81`, matching `encodeBytes [b]`'s else-branch.
                  have hlen1 : pfx.toNat - 0x80 = 1 := by simp at hlen; omega
                  have hpfx : pfx = BitVec.ofNat 8 0x81 := by
                    have hp : pfx.toNat = 0x81 := by omega
                    have := pfx.isLt
                    apply BitVec.eq_of_toNat_eq
                    simp [hp]
                  subst hcat
                  simp [encode, encodeBytes, hb, hpfx]
              | [] =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hsome
                obtain ⟨hi, hr⟩ := hsome
                subst hi; subst hr
                have hlen0 : pfx.toNat - 0x80 = 0 := by simp at hlen; omega
                have hpfx : pfx = BitVec.ofNat 8 0x80 := by
                  have hp : pfx.toNat = 0x80 := by omega
                  apply BitVec.eq_of_toNat_eq
                  simp [hp]
                subst hcat
                simp [encode, encodeBytes, hpfx]
              | b :: c :: tl =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hsome
                obtain ⟨hi, hr⟩ := hsome
                subst hi; subst hr
                have hlenN : (b :: c :: tl).length = pfx.toNat - 0x80 := hlen
                have hle55 : (b :: c :: tl).length ≤ 55 := by rw [hlenN]; omega
                have hne1 : (b :: c :: tl).length ≠ 1 := by simp
                have hpfx : BitVec.ofNat 8 (0x80 + (b :: c :: tl).length) = pfx := by
                  rw [hlenN]
                  apply BitVec.eq_of_toNat_eq
                  have := pfx.isLt
                  simp only [BitVec.toNat_ofNat]
                  omega
                subst hcat
                simp only [encode]
                rw [encodeBytes_short_of_length_ne_one _ hle55 hne1, hpfx]
                simp
          · simp only [h2, if_false] at hsome
            by_cases h3 : pfx.toNat ≤ 0xBF
            · -- Long string. `readLength`'s minimality is what closes this.
              simp only [h3, if_true] at hsome
              cases hrl : readLength bs' (pfx.toNat - 0xB7) with
              | none => rw [hrl] at hsome; simp at hsome
              | some lr =>
                obtain ⟨lenVal, restL⟩ := lr
                rw [hrl] at hsome
                simp only [Option.bind_eq_bind, Option.bind_some] at hsome
                by_cases h55 : lenVal ≤ 55
                · simp only [h55, if_true] at hsome; simp at hsome
                · simp only [h55, if_false] at hsome
                  cases htb : takeBytes restL lenVal with
                  | none => rw [htb] at hsome; simp at hsome
                  | some pr =>
                    obtain ⟨data, restD⟩ := pr
                    rw [htb] at hsome
                    simp only [Option.bind_some,
                      Option.some.injEq, Prod.mk.injEq] at hsome
                    obtain ⟨hi, hr⟩ := hsome
                    subst hi; subst hr
                    obtain ⟨lenBytes, hsplit, hlenB, _, hmin⟩ := readLength_eq_some_imp hrl
                    obtain ⟨hcat, hdlen⟩ := takeBytes_eq_some_imp htb
                    have htoB : Nat.toBytesBE lenVal = lenBytes := hmin (by omega)
                    have hdgt : 55 < data.length := by rw [hdlen]; omega
                    simp only [encode]
                    rw [encodeBytes_long data hdgt, hdlen, htoB, hlenB]
                    have hpfx : BitVec.ofNat 8 (0xB7 + (pfx.toNat - 0xB7)) = pfx := by
                      apply BitVec.eq_of_toNat_eq
                      have := pfx.isLt
                      simp only [BitVec.toNat_ofNat]
                      omega
                    rw [hpfx]
                    subst hsplit; subst hcat
                    simp [List.append_assoc]
            · simp only [h3, if_false] at hsome
              by_cases h4 : pfx.toNat ≤ 0xF7
              · -- Short list. The payload IS `encodeItems items`, by the inner IH.
                simp only [h4, if_true] at hsome
                cases htb : takeBytes bs' (pfx.toNat - 0xC0) with
                | none => rw [htb] at hsome; simp at hsome
                | some pr =>
                  obtain ⟨payload, restP⟩ := pr
                  rw [htb] at hsome
                  simp only [Option.bind_eq_bind, Option.bind_some] at hsome
                  cases hdi : decodeItems n payload with
                  | none => rw [hdi] at hsome; simp at hsome
                  | some ir =>
                    obtain ⟨items, leftover⟩ := ir
                    rw [hdi] at hsome
                    simp only [Option.bind_some] at hsome
                    cases leftover with
                    | cons c cs => simp at hsome
                    | nil =>
                      simp only [List.isEmpty_nil, if_true,
                        Option.some.injEq, Prod.mk.injEq] at hsome
                      obtain ⟨hi, hr⟩ := hsome
                      subst hi; subst hr
                      obtain ⟨hcat, hplen⟩ := takeBytes_eq_some_imp htb
                      have hB : encode.encodeItems items = payload := by
                        have := ihItems payload items [] hdi
                        simpa using this
                      have hpl : (encode.encodeItems items).length ≤ 55 := by
                        rw [hB, hplen]; omega
                      rw [encode_list_short items hpl, hB]
                      have hpfx : BitVec.ofNat 8 (0xC0 + payload.length) = pfx := by
                        apply BitVec.eq_of_toNat_eq
                        have := pfx.isLt
                        simp only [BitVec.toNat_ofNat, hplen]
                        omega
                      rw [hpfx]
                      subst hcat
                      simp
              · -- Long list: the long-string bookkeeping plus the inner IH.
                simp only [h4, if_false] at hsome
                cases hrl : readLength bs' (pfx.toNat - 0xF7) with
                | none => rw [hrl] at hsome; simp at hsome
                | some lr =>
                  obtain ⟨lenVal, restL⟩ := lr
                  rw [hrl] at hsome
                  simp only [Option.bind_eq_bind, Option.bind_some] at hsome
                  by_cases h55 : lenVal ≤ 55
                  · simp only [h55, if_true] at hsome; simp at hsome
                  · simp only [h55, if_false] at hsome
                    cases htb : takeBytes restL lenVal with
                    | none => rw [htb] at hsome; simp at hsome
                    | some pr =>
                      obtain ⟨payload, restP⟩ := pr
                      rw [htb] at hsome
                      simp only [Option.bind_some] at hsome
                      cases hdi : decodeItems n payload with
                      | none => rw [hdi] at hsome; simp at hsome
                      | some ir =>
                        obtain ⟨items, leftover⟩ := ir
                        rw [hdi] at hsome
                        simp only [Option.bind_some] at hsome
                        cases leftover with
                        | cons c cs => simp at hsome
                        | nil =>
                          simp only [List.isEmpty_nil, if_true,
                            Option.some.injEq, Prod.mk.injEq] at hsome
                          obtain ⟨hi, hr⟩ := hsome
                          subst hi; subst hr
                          obtain ⟨lenBytes, hsplit, hlenB, _, hmin⟩ :=
                            readLength_eq_some_imp hrl
                          obtain ⟨hcat, hplen⟩ := takeBytes_eq_some_imp htb
                          have htoB : Nat.toBytesBE lenVal = lenBytes := hmin (by omega)
                          have hB : encode.encodeItems items = payload := by
                            have := ihItems payload items [] hdi
                            simpa using this
                          have hpgt : 55 < (encode.encodeItems items).length := by
                            rw [hB, hplen]; omega
                          rw [encode_list_long items hpgt, hB, hplen, htoB, hlenB]
                          have hpfx : BitVec.ofNat 8 (0xF7 + (pfx.toNat - 0xF7)) = pfx := by
                            apply BitVec.eq_of_toNat_eq
                            have := pfx.isLt
                            simp only [BitVec.toNat_ofNat]
                            omega
                          rw [hpfx]
                          subst hsplit; subst hcat
                          simp [List.append_assoc]

    · -- `decodeItems (n+1)`: the clean case — append-associativity plus both IHs.
      intro bs items rest hsome
      match bs with
      | [] =>
        simp only [decodeItems, Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨hi, hr⟩ := hsome
        subst hi; subst hr
        simp [encode.encodeItems]
      | b :: bs' =>
        simp only [decodeItems] at hsome
        cases hda : decodeAux n (b :: bs') with
        | none => rw [hda] at hsome; simp at hsome
        | some ar =>
          obtain ⟨itm, rst⟩ := ar
          rw [hda] at hsome
          simp only [Option.bind_eq_bind, Option.bind_some] at hsome
          cases hdi : decodeItems n rst with
          | none => rw [hdi] at hsome; simp at hsome
          | some ir =>
            obtain ⟨itms, rst'⟩ := ir
            rw [hdi] at hsome
            simp only [Option.bind_some,
              Option.some.injEq, Prod.mk.injEq] at hsome
            obtain ⟨hi, hr⟩ := hsome
            subst hi; subst hr
            have hA := ihAux (b :: bs') itm rst hda
            have hB := ihItems rst itms rst' hdi
            calc encode.encodeItems (itm :: itms) ++ rst'
                = encode itm ++ (encode.encodeItems itms ++ rst') := by
                  simp [encode.encodeItems, List.append_assoc]
              _ = encode itm ++ rst := by rw [hB]
              _ = b :: bs' := hA

/-- **Canonicality for `decodeAux`.** The fuel-parametric single-item form. -/
theorem encode_decodeAux {n : Nat} {bs : List Byte} {item : RLPItem} {rest : List Byte}
    (h : decodeAux n bs = some (item, rest)) : encode item ++ rest = bs :=
  (encode_decode_mutual n).1 bs item rest h

/-- **Canonicality for `decodeItems`.** -/
theorem encode_decodeItems {n : Nat} {bs : List Byte} {items : List RLPItem}
    {rest : List Byte} (h : decodeItems n bs = some (items, rest)) :
    encode.encodeItems items ++ rest = bs :=
  (encode_decode_mutual n).2 bs items rest h

/-- ⭐ **`encode_decode` — the theorem #11896 asks for.** A byte string that decodes
    completely IS the encoding of what it decoded to. Equivalently: `decode` has no
    non-canonical accepts.

    Note there is **no length side condition**, unlike `decode_encode`'s
    `(encode item).length < 256 ^ 8`. That bound exists because encoding must fit the
    decoder's 8-byte length field; here the input is *given* to decode successfully, so
    the bound is already implied by the run rather than assumed. -/
theorem encode_decode {bs : List Byte} {item : RLPItem}
    (h : decode bs = some (item, [])) : encode item = bs := by
  rw [decode_eq_decodeAux_length] at h
  have := encode_decodeAux h
  simpa using this

/-- The `decodeFully` form, which is the shape most callers hold. -/
theorem encode_decodeFully {bs : List Byte} {item : RLPItem}
    (h : decodeFully bs = some item) : encode item = bs :=
  encode_decode ((decodeFully_eq_some_iff bs item).1 h)

/-- ⭐ **`decode` is injective.** Two byte strings that decode to the same item are
    equal — the dual of `encode_injective`, and the property a differential transfer
    actually needs: it says the decoder cannot map two distinct inputs to one item, so
    agreeing with the reference on decoded *items* pins agreement on *bytes*. -/
theorem decode_injective {bs₁ bs₂ : List Byte} {item : RLPItem}
    (h₁ : decode bs₁ = some (item, [])) (h₂ : decode bs₂ = some (item, [])) :
    bs₁ = bs₂ := by
  rw [← encode_decode h₁, ← encode_decode h₂]

/-- The round trip in the other order, completing the pair with `decode_encode`:
    `encode ∘ decode = id` on completely-decodable input, `decode ∘ encode = id` on
    encodings within the length bound. -/
theorem encode_decode_encode {bs : List Byte} {item : RLPItem}
    (h : decode bs = some (item, [])) : decode (encode item) = some (item, []) := by
  rw [encode_decode h]; exact h

/-! ## Non-vacuity and the canonicality checks, kernel-checked

    The interesting content is the **negative** cases: each is a byte string the
    decoder rejects *because* accepting it would break `encode_decode`. Together they
    show the theorem is not true by accident of a weak decoder. -/

section NonVacuity

/-- Positive: a short string round-trips, and `encode_decode` returns the input. -/
example : decode [BitVec.ofNat 8 0x83, 1, 2, 3] = some (.bytes [1, 2, 3], []) := by decide

example : encode (.bytes [1, 2, 3]) = [BitVec.ofNat 8 0x83, 1, 2, 3] := by decide

/-- ⭐ **Check 1** — a single byte below `0x80` may not use the short-string form.
    `0x81 0x01` is rejected; accepting it would break the theorem, since
    `encode (.bytes [1]) = [1]` and `[1] ≠ [0x81, 1]`. -/
example : decode [BitVec.ofNat 8 0x81, 1] = none := by decide

example : encode (.bytes [1]) = [(1 : BitVec 8)] := by decide

/-- ⭐ **Check 2** — the long form may not encode a length `≤ 55`. `0xB8 0x01 0xFF`
    would say "long string, length 1"; rejected, because `encode` would emit the short
    form `0x81 0xFF`. -/
example : decode [BitVec.ofNat 8 0xB8, 1, 0xFF] = none := by decide

/-- ⭐ **Check 3** — a multi-byte length field may not carry a leading zero. This is
    the `readLength` check, and the one `Nat.toBytesBE_fromBytesBE_of_canonical`
    consumes: `0xB9 0x00 0x38` names length 56 in two bytes where one suffices. -/
example : decode ([BitVec.ofNat 8 0xB9, 0, 0x38] ++ List.replicate 56 7) = none := by
  decide

/-- ⭐ **Check 4** — a list payload must be consumed exactly. `0xC1` claims a 1-byte
    payload, but `0x83` opens a 3-byte string that overruns it. -/
example : decode [BitVec.ofNat 8 0xC1, BitVec.ofNat 8 0x83] = none := by decide

/-- An empty list and an empty string are distinct encodings, both canonical — so the
    theorem is not vacuous on the degenerate cases either. -/
example : decode [BitVec.ofNat 8 0xC0] = some (.list [], []) := by decide

example : decode [BitVec.ofNat 8 0x80] = some (.bytes [], []) := by decide

/-- A nested list, to exercise the `decodeItems` half of the mutual induction. -/
example :
    decode [BitVec.ofNat 8 0xC2, BitVec.ofNat 8 0xC1, BitVec.ofNat 8 0x80]
      = some (.list [.list [.bytes []]], []) := by decide

end NonVacuity

end EvmAsm.EL.RLP
