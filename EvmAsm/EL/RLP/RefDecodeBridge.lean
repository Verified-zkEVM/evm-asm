/-
  EvmAsm.EL.RLP.RefDecodeBridge

  The reference-shaped RLP decoder (`Ref.decode`, an exact-slicing port of the
  pinned `ethereum_rlp` 0.1.6 — see `RefDecode.lean`) agrees with the streaming
  decoder actually used by SpecRef consumers (`decodeFully`) on every input the
  streaming decoder's 8-byte length field can express:

      Ref.decode bs = decodeFully bs        (bs.length < 256 ^ 8)

  The proof factors into
  * **soundness** (no side conditions): a `Ref.*` accept *is* an encoding —
    `Ref.decode bs = some item → bs = encode item` (and the `decodeToBytes` /
    `decodeToSequence` / `decodeJoinedEncodings` companions), by induction on
    the reference recursion's own measure `3 * bs.length + phase`;
  * **completeness** (bounded): every encoding is accepted —
    `Ref.decode (encode item) = some item` for `(encode item).length < 256 ^ 8`,
    mutually with `Ref.decodeJoinedEncodings (encode.encodeItems items) = some
    items`, again by measure induction;
  and the transfer then cases on `decodeFully bs`, using `encode_decodeFully`
  (streaming accepts are canonical) one way and `decodeFully_encode` (streaming
  round-trip) the other.
-/

import EvmAsm.EL.RLP.RefDecode
import EvmAsm.EL.RLP.Properties
import EvmAsm.EL.RLP.EncodeDecode

namespace EvmAsm.EL.RLP

set_option maxRecDepth 8000

/-! ## Sanity vectors

Computational spot checks of the statements proved below, on both sides of the
short/long boundaries and on nesting. -/

#guard Ref.decode (encode (.list [.bytes [5]])) = some (.list [.bytes [5]])
#guard Ref.decode (encode (.list [.list [.bytes [0x80#8, 1]], .bytes []]))
  = some (.list [.list [.bytes [0x80#8, 1]], .bytes []])
#guard Ref.decodeToBytes (encodeBytes (List.replicate 56 (7 : Byte)))
  = some (List.replicate 56 (7 : Byte))
#guard Ref.decodeItemLength (encode (.bytes [5]) ++ [1, 2]) = some 1
#guard Ref.decodeItemLength (encode (.bytes (List.replicate 56 (7 : Byte))) ++ [1])
  = some 58
#guard Ref.decode [] = decodeFully []
#guard Ref.decode [0x81#8, 0x05#8] = decodeFully [0x81#8, 0x05#8]  -- both reject
#guard Ref.decode (0xc0#8 :: []) = decodeFully [0xc0#8]

/-! ## Byte helpers -/

/-- 8-bit `ofNat` round-trip below 256. -/
private theorem toNat_ofNat8 {x : Nat} (h : x < 256) :
    (BitVec.ofNat 8 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

/-- A byte whose `toNat` is a known value `< 256` is that `ofNat` literal. -/
private theorem byte_eq_ofNat {b : Byte} {x : Nat} (hx : x < 256) (h : b.toNat = x) :
    b = BitVec.ofNat 8 x :=
  BitVec.eq_of_toNat_eq (by rw [h, toNat_ofNat8 hx])

/-! ## Soundness: a `Ref.*` accept is an encoding -/

/-- **Soundness of `Ref.decodeToBytes`** (no side conditions): a byte-string
    accept is exactly `encodeBytes` of the decoded payload.  The passed frame
    checks pin `bs.length` exactly, so the payload slice is exact, and the
    canonicality checks force the header byte `encodeBytes` would emit. -/
theorem Ref.decodeToBytes_sound {bs raw : List Byte}
    (h : Ref.decodeToBytes bs = some raw) : bs = encodeBytes raw := by
  cases bs with
  | nil => simp [Ref.decodeToBytes] at h
  | cons b0 rest =>
    have hb0 : b0.toNat < 256 := b0.isLt
    simp only [Ref.decodeToBytes] at h
    split at h
    · -- single small byte: `bs = [b0]`, `b0 < 0x80`, its own encoding
      rename_i hc
      obtain ⟨hlen, hsmall⟩ := hc
      injection h with h
      subst h
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst hrest
      simp [encodeBytes, hsmall]
    · rename_i hc1
      split at h
      · exact absurd h (by simp)
      rename_i hc2
      split at h
      · -- short form: header `0x80 + len`, payload = the rest of the window
        rename_i hc3
        split at h
        · exact absurd h (by simp)
        rename_i hc4
        split at h
        · exact absurd h (by simp)
        rename_i hc5
        split at h
        · exact absurd h (by simp)
        rename_i hc6
        injection h with h
        simp only [List.length_cons] at hc4 hc5
        have hrl : rest.length = b0.toNat - 128 := by omega
        have htake : rest.take (b0.toNat - 128) = rest :=
          List.take_of_length_le (by omega)
        rw [htake] at h
        subst h
        by_cases hone : rest.length = 1
        · -- singleton payload: canonicality check forces `raw ≥ 0x80`
          obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hone
          have hclarge : ¬ c.toNat < 128 := by
            intro hcl
            exact hc6 ⟨by omega, by rw [htake]; simpa using hcl⟩
          rw [encodeBytes_single_large c hclarge]
          have hb : b0 = BitVec.ofNat 8 0x81 :=
            byte_eq_ofNat (by omega) (by simp only [List.length_singleton] at hrl; omega)
          rw [hb]
        · have hle : rest.length ≤ 55 := by omega
          rw [encodeBytes_short_of_length_ne_one rest hle hone]
          have hb : b0 = BitVec.ofNat 8 (0x80 + rest.length) :=
            byte_eq_ofNat (by omega) (by omega)
          rw [hb, List.singleton_append]
      · -- long form: header `0xB7 + lenLen`, canonical big-endian length field
        rename_i hc3
        split at h
        · exact absurd h (by simp)
        rename_i hc7
        split at h
        · exact absurd h (by simp)
        rename_i hc8
        split at h
        · exact absurd h (by simp)
        rename_i hc9
        split at h
        · exact absurd h (by simp)
        rename_i hc10
        split at h
        · exact absurd h (by simp)
        rename_i hc11
        injection h with h
        simp only [List.length_cons] at hc7 hc10 hc11
        have hk1 : 1 ≤ b0.toNat - 183 := by omega
        have hkle : b0.toNat - 183 ≤ rest.length := by omega
        have htakelen : (rest.take (b0.toNat - 183)).length = b0.toNat - 183 := by
          rw [List.length_take]; omega
        have hrl : rest.length
            = (b0.toNat - 183) + Nat.fromBytesBE (rest.take (b0.toNat - 183)) := by omega
        have hdroplen : (rest.drop (b0.toNat - 183)).length
            = Nat.fromBytesBE (rest.take (b0.toNat - 183)) := by
          rw [List.length_drop]; omega
        have htake2 : (rest.drop (b0.toNat - 183)).take
              (Nat.fromBytesBE (rest.take (b0.toNat - 183)))
            = rest.drop (b0.toNat - 183) :=
          List.take_of_length_le (by omega)
        rw [htake2] at h
        subst h
        -- the length field is canonical: nonzero head, so `toBytesBE` recovers it
        have hhead : (rest.take (b0.toNat - 183)).headD 1 ≠ 0 := by
          cases rest with
          | nil => simp at hkle; omega
          | cons r rest' =>
            obtain ⟨k', hk'⟩ : ∃ k', b0.toNat - 183 = k' + 1 := ⟨b0.toNat - 184, by omega⟩
            rw [hk', List.take_succ_cons, List.headD_cons]
            simpa using hc8
        have hcanon : Nat.toBytesBE (Nat.fromBytesBE (rest.take (b0.toNat - 183)))
            = rest.take (b0.toNat - 183) :=
          Nat.toBytesBE_fromBytesBE_of_canonical _ hhead
        have hlong : 55 < (rest.drop (b0.toNat - 183)).length := by omega
        rw [encodeBytes_long_of_length _ hlong, hdroplen, hcanon, htakelen,
            List.append_assoc, List.take_append_drop, List.singleton_append]
        have hb : b0 = BitVec.ofNat 8 (0xB7 + (b0.toNat - 183)) :=
          byte_eq_ofNat (by omega) (by omega)
        exact congrArg (· :: rest) hb

/-- The three mutual soundness statements, proved together by induction on the
    reference recursion's own termination measure `3 * bs.length + phase`
    (phase 0 = `decodeToSequence`, 1 = `decode`, 2 = `decodeJoinedEncodings`);
    every recursive call strictly decreases it, so the plain-successor IH
    covers each callee. -/
private theorem Ref.sound_aux : ∀ n : Nat,
    (∀ bs : List Byte, 3 * bs.length + 1 ≤ n → ∀ item : RLPItem,
        Ref.decode bs = some item → bs = encode item)
    ∧ (∀ bs : List Byte, 3 * bs.length ≤ n → ∀ items : List RLPItem,
        Ref.decodeToSequence bs = some items → bs = encode (.list items))
    ∧ (∀ bs : List Byte, 3 * bs.length + 2 ≤ n → ∀ items : List RLPItem,
        Ref.decodeJoinedEncodings bs = some items → bs = encode.encodeItems items) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun bs hn => by omega, fun bs hn items h => ?_, fun bs hn => by omega⟩
    have hbs : bs = [] := by
      cases bs with
      | nil => rfl
      | cons _ _ => simp at hn
    subst hbs
    simp [Ref.decodeToSequence] at h
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · -- `decode`: dispatch on the header byte, then `decodeToBytes_sound` / IH₂
      intro bs hn item h
      cases bs with
      | nil => simp [Ref.decode] at h
      | cons b0 tail =>
        simp only [Ref.decode] at h
        split at h
        · cases hx : Ref.decodeToBytes (b0 :: tail) with
          | none => rw [hx] at h; simp at h
          | some raw =>
            rw [hx] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            simpa [encode] using Ref.decodeToBytes_sound hx
        · cases hx : Ref.decodeToSequence (b0 :: tail) with
          | none => rw [hx] at h; simp at h
          | some items =>
            rw [hx] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            exact ih2 _ (by omega) items hx
    · -- `decodeToSequence`: the frame checks pin the window; IH₃ on the payload
      intro bs hn items h
      cases bs with
      | nil => simp [Ref.decodeToSequence] at h
      | cons b0 rest =>
        have hb0 : b0.toNat < 256 := b0.isLt
        simp only [Ref.decodeToSequence] at h
        split at h
        · exact absurd h (by simp)
        rename_i hc1
        split at h
        · -- short list: header `0xC0 + len`, payload = the rest of the window
          rename_i hc2
          split at h
          · exact absurd h (by simp)
          rename_i hc3
          split at h
          · exact absurd h (by simp)
          rename_i hc4
          simp only [List.length_cons] at hc3 hc4
          have hrl : rest.length = b0.toNat - 192 := by omega
          have htake : rest.take (b0.toNat - 192) = rest :=
            List.take_of_length_le (by omega)
          rw [htake] at h
          have hpayload : rest = encode.encodeItems items :=
            ih3 rest (by simp only [List.length_cons] at hn; omega) items h
          have hlen : (encode.encodeItems items).length ≤ 55 := by
            rw [← hpayload]; omega
          rw [encode_list_short items hlen, ← hpayload]
          exact congrArg (· :: rest) (byte_eq_ofNat (by omega) (by omega))
        · -- long list: canonical big-endian payload length, then IH₃
          rename_i hc2
          split at h
          · exact absurd h (by simp)
          rename_i hc5
          split at h
          · exact absurd h (by simp)
          rename_i hc6
          split at h
          · exact absurd h (by simp)
          rename_i hc7
          split at h
          · exact absurd h (by simp)
          rename_i hc8
          split at h
          · exact absurd h (by simp)
          rename_i hc9
          simp only [List.length_cons] at hc5 hc8 hc9
          have hk1 : 1 ≤ b0.toNat - 247 := by omega
          have hkle : b0.toNat - 247 ≤ rest.length := by omega
          have htakelen : (rest.take (b0.toNat - 247)).length = b0.toNat - 247 := by
            rw [List.length_take]; omega
          have hdroplen : (rest.drop (b0.toNat - 247)).length
              = Nat.fromBytesBE (rest.take (b0.toNat - 247)) := by
            rw [List.length_drop]; omega
          have htake2 : (rest.drop (b0.toNat - 247)).take
                (Nat.fromBytesBE (rest.take (b0.toNat - 247)))
              = rest.drop (b0.toNat - 247) :=
            List.take_of_length_le (by omega)
          rw [htake2] at h
          have hpayload : rest.drop (b0.toNat - 247) = encode.encodeItems items :=
            ih3 _ (by rw [List.length_drop]
                      simp only [List.length_cons] at hn; omega) items h
          have hlen_items : (encode.encodeItems items).length
              = Nat.fromBytesBE (rest.take (b0.toNat - 247)) := by
            rw [← hpayload, hdroplen]
          have hlong : 55 < (encode.encodeItems items).length := by
            rw [hlen_items]; omega
          have hhead : (rest.take (b0.toNat - 247)).headD 1 ≠ 0 := by
            cases rest with
            | nil => simp at hkle; omega
            | cons r rest' =>
              obtain ⟨k', hk'⟩ : ∃ k', b0.toNat - 247 = k' + 1 :=
                ⟨b0.toNat - 248, by omega⟩
              rw [hk', List.take_succ_cons, List.headD_cons]
              simpa using hc6
          have hcanon : Nat.toBytesBE (Nat.fromBytesBE (rest.take (b0.toNat - 247)))
              = rest.take (b0.toNat - 247) :=
            Nat.toBytesBE_fromBytesBE_of_canonical _ hhead
          rw [encode_list_long items hlong, hlen_items, hcanon, htakelen,
              ← hpayload, List.take_append_drop]
          exact congrArg (· :: rest) (byte_eq_ofNat (by omega) (by omega))
    · -- `decodeJoinedEncodings`: `take L ++ drop L` reassembles the window
      intro bs hn items h
      cases bs with
      | nil =>
        simp only [Ref.decodeJoinedEncodings] at h
        injection h with h
        subst h
        rfl
      | cons b0 tail =>
        simp only [Ref.decodeJoinedEncodings] at h
        split at h
        · exact absurd h (by simp)
        rename_i L hL
        split at h
        case isFalse => exact absurd h (by simp)
        rename_i hle
        split at h
        · exact absurd h (by simp)
        rename_i item' hitem
        split at h
        · exact absurd h (by simp)
        rename_i items' hitems
        injection h with h
        subst h
        have hLpos : 1 ≤ L := Ref.decodeItemLength_pos hL
        have h1 : (b0 :: tail).take L = encode item' :=
          ih1 _ (by rw [List.length_take]; omega) item' hitem
        have h2 : (b0 :: tail).drop L = encode.encodeItems items' :=
          ih3 _ (by rw [List.length_drop]
                    simp only [List.length_cons] at hn ⊢; omega) items' hitems
        show b0 :: tail = encode.encodeItems (item' :: items')
        rw [show encode.encodeItems (item' :: items')
              = encode item' ++ encode.encodeItems items' from rfl,
            ← h1, ← h2, List.take_append_drop]

/-- **Soundness of `Ref.decode`** (no side conditions): an accept is exactly
    the RLP encoding of the decoded item. -/
theorem Ref.decode_sound {bs : List Byte} {item : RLPItem}
    (h : Ref.decode bs = some item) : bs = encode item :=
  (Ref.sound_aux (3 * bs.length + 1)).1 bs (Nat.le_refl _) item h

/-- **Soundness of `Ref.decodeToSequence`** (no side conditions). -/
theorem Ref.decodeToSequence_sound {bs : List Byte} {items : List RLPItem}
    (h : Ref.decodeToSequence bs = some items) : bs = encode (.list items) :=
  (Ref.sound_aux (3 * bs.length)).2.1 bs (Nat.le_refl _) items h

/-- **Soundness of `Ref.decodeJoinedEncodings`** (no side conditions): an
    accepted window is exactly the concatenation of the decoded items'
    encodings. -/
theorem Ref.decodeJoinedEncodings_sound {bs : List Byte} {items : List RLPItem}
    (h : Ref.decodeJoinedEncodings bs = some items) : bs = encode.encodeItems items :=
  (Ref.sound_aux (3 * bs.length + 2)).2.2 bs (Nat.le_refl _) items h

/-! ## Completeness: every (8-byte-length-field-expressible) encoding is accepted -/

/-- Completeness of `Ref.decodeToBytes`: every `encodeBytes` output decodes to
    its payload.  The bound keeps the long form's length-of-length within the
    `0xB8..0xBF` header range (`≤ 8` length bytes). -/
theorem Ref.decodeToBytes_encodeBytes (data : List Byte) (hlen : data.length < 256 ^ 8) :
    Ref.decodeToBytes (encodeBytes data) = some data := by
  by_cases hone : data.length = 1
  · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hone
    by_cases hb : b.toNat < 0x80
    · rw [encodeBytes_single_small b hb]
      simp [Ref.decodeToBytes, hb]
    · rw [encodeBytes_single_large b hb]
      simp [Ref.decodeToBytes, hb]
  · by_cases hsh : data.length ≤ 55
    · rw [encodeBytes_short_of_length_ne_one data hsh hone, List.singleton_append]
      simp only [Ref.decodeToBytes, List.length_cons]
      rw [toNat_ofNat8 (show 0x80 + data.length < 256 by omega),
          show 0x80 + data.length - 128 = data.length from by omega, List.take_length]
      split
      · rename_i hcond; exact absurd hcond.2 (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · split
        · rename_i hcond; exact absurd hcond (by omega)
        split
        · rename_i hcond; exact absurd hcond (by omega)
        split
        · rename_i hcond; exact absurd hcond.1 hone
        rfl
      · rename_i hcond; exact absurd (show 0x80 + data.length ≤ 0xB7 by omega) hcond
    · have hlong : 55 < data.length := by omega
      have hk8 : (Nat.toBytesBE data.length).length ≤ 8 := Nat.toBytesBE_length_le _ _ hlen
      obtain ⟨c, tl, hcons, hc0⟩ := Nat.toBytesBE_eq_cons_of_pos data.length (by omega)
      have hk1 : 1 ≤ (Nat.toBytesBE data.length).length := by rw [hcons]; simp
      rw [encodeBytes_long_of_length data hlong, List.singleton_append, List.cons_append]
      simp only [Ref.decodeToBytes, List.length_cons, List.length_append]
      rw [toNat_ofNat8 (show 0xB7 + (Nat.toBytesBE data.length).length < 256 by omega),
          show 0xB7 + (Nat.toBytesBE data.length).length - 183
            = (Nat.toBytesBE data.length).length from by omega,
          List.take_left, Nat.fromBytesBE_toBytesBE, List.drop_left, List.take_length]
      split
      · rename_i hcond; exact absurd hcond.2 (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond
        rw [hcons] at hcond
        simp only [List.cons_append, List.getD_cons_zero] at hcond
        exact absurd hcond hc0
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      rfl

/-- The head byte of `encodeBytes` output is a byte-string header (`≤ 0xBF`),
    so `Ref.decode` dispatches it to `Ref.decodeToBytes`. -/
private theorem encodeBytes_head (data : List Byte) (hlen : data.length < 256 ^ 8) :
    ∃ e0 etail, encodeBytes data = e0 :: etail ∧ e0.toNat ≤ 0xBF := by
  by_cases hone : data.length = 1
  · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hone
    by_cases hb : b.toNat < 0x80
    · exact ⟨b, [], encodeBytes_single_small b hb, by omega⟩
    · exact ⟨BitVec.ofNat 8 0x81, [b], encodeBytes_single_large b hb,
        by rw [toNat_ofNat8 (by omega)]; omega⟩
  · by_cases hsh : data.length ≤ 55
    · exact ⟨BitVec.ofNat 8 (0x80 + data.length), data,
        by rw [encodeBytes_short_of_length_ne_one data hsh hone]; rfl,
        by rw [toNat_ofNat8 (by omega)]; omega⟩
    · have hlong : 55 < data.length := by omega
      have hk8 : (Nat.toBytesBE data.length).length ≤ 8 := Nat.toBytesBE_length_le _ _ hlen
      exact ⟨BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length),
        Nat.toBytesBE data.length ++ data,
        by rw [encodeBytes_long_of_length data hlong]; rfl,
        by rw [toNat_ofNat8 (by omega)]; omega⟩

/-- **`Ref.decodeItemLength` reads off exactly the encoding's length** from the
    header, for any trailer: the exact slice point `decodeJoinedEncodings`
    needs.  The bound keeps a long form's length-of-length `≤ 8`, so the header
    byte stays in its intended range. -/
theorem Ref.decodeItemLength_encode (item : RLPItem) (rest : List Byte)
    (h : (encode item).length < 256 ^ 8) :
    Ref.decodeItemLength (encode item ++ rest) = some (encode item).length := by
  cases item with
  | bytes data =>
    simp only [encode] at h ⊢
    have hdlen : data.length < 256 ^ 8 :=
      Nat.lt_of_le_of_lt (le_encodeBytes_length data) h
    by_cases hone : data.length = 1
    · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hone
      by_cases hb : b.toNat < 0x80
      · rw [encodeBytes_single_small b hb]
        simp [Ref.decodeItemLength, hb]
      · rw [encodeBytes_single_large b hb]
        simp [Ref.decodeItemLength]
    · by_cases hsh : data.length ≤ 55
      · rw [encodeBytes_short_of_length_ne_one data hsh hone, List.singleton_append,
            List.cons_append]
        simp only [Ref.decodeItemLength, List.length_cons]
        rw [toNat_ofNat8 (show 0x80 + data.length < 256 by omega)]
        split
        · rename_i hcond; exact absurd hcond (by omega)
        split
        · simp only [Option.some.injEq]; omega
        · rename_i hcond; exact absurd (show 0x80 + data.length ≤ 0xB7 by omega) hcond
      · have hlong : 55 < data.length := by omega
        have hk8 : (Nat.toBytesBE data.length).length ≤ 8 :=
          Nat.toBytesBE_length_le _ _ hdlen
        obtain ⟨c, tl, hcons, hc0⟩ := Nat.toBytesBE_eq_cons_of_pos data.length (by omega)
        have hk1 : 1 ≤ (Nat.toBytesBE data.length).length := by rw [hcons]; simp
        rw [encodeBytes_long_of_length data hlong]
        simp only [List.cons_append, List.nil_append, List.append_assoc]
        simp only [Ref.decodeItemLength, List.length_cons, List.length_append]
        rw [toNat_ofNat8 (show 0xB7 + (Nat.toBytesBE data.length).length < 256 by omega),
            show 0xB7 + (Nat.toBytesBE data.length).length - 183
              = (Nat.toBytesBE data.length).length from by omega,
            List.take_left, Nat.fromBytesBE_toBytesBE]
        split
        · rename_i hcond; exact absurd hcond (by omega)
        split
        · rename_i hcond; exact absurd hcond (by omega)
        split
        · split
          · rename_i hcond; exact absurd hcond (by omega)
          split
          · rename_i hcond
            rw [hcons] at hcond
            simp only [List.cons_append, List.getD_cons_zero] at hcond
            exact absurd hcond hc0
          simp only [Option.some.injEq]; omega
        · rename_i hcond
          exact absurd (show 0xB7 + (Nat.toBytesBE data.length).length ≤ 0xBF by omega) hcond
  | list items =>
    by_cases h55 : (encode.encodeItems items).length ≤ 55
    · rw [encode_list_short items h55, List.cons_append]
      simp only [Ref.decodeItemLength, List.length_cons]
      rw [toNat_ofNat8 (show 0xC0 + (encode.encodeItems items).length < 256 by omega)]
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · simp only [Option.some.injEq]; omega
      · rename_i hcond
        exact absurd (show 0xC0 + (encode.encodeItems items).length ≤ 0xF7 by omega) hcond
    · have hlong : 55 < (encode.encodeItems items).length := by omega
      have hplen : (encode.encodeItems items).length < 256 ^ 8 := by
        rw [encode_list_long items hlong] at h
        simp only [List.length_cons, List.length_append] at h
        omega
      have hk8 : (Nat.toBytesBE (encode.encodeItems items).length).length ≤ 8 :=
        Nat.toBytesBE_length_le _ _ hplen
      obtain ⟨c, tl, hcons, hc0⟩ :=
        Nat.toBytesBE_eq_cons_of_pos (encode.encodeItems items).length (by omega)
      have hk1 : 1 ≤ (Nat.toBytesBE (encode.encodeItems items).length).length := by
        rw [hcons]; simp
      rw [encode_list_long items hlong, List.cons_append]
      simp only [Ref.decodeItemLength, List.length_cons, List.length_append,
        List.append_assoc]
      rw [toNat_ofNat8
            (show 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length < 256
              by omega),
          show 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length - 247
            = (Nat.toBytesBE (encode.encodeItems items).length).length from by omega,
          List.take_left, Nat.fromBytesBE_toBytesBE]
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond; exact absurd hcond (by omega)
      split
      · rename_i hcond
        rw [hcons] at hcond
        simp only [List.cons_append, List.getD_cons_zero] at hcond
        exact absurd hcond hc0
      simp only [Option.some.injEq]; omega

/-- One accepted step of `Ref.decodeJoinedEncodings` on a nonempty window with
    a known in-range item length. -/
private theorem Ref.decodeJoinedEncodings_step {bs : List Byte} {L : Nat}
    (hbs : bs ≠ []) (hL : Ref.decodeItemLength bs = some L) (hle : L ≤ bs.length) :
    Ref.decodeJoinedEncodings bs =
      match Ref.decode (bs.take L) with
      | none => none
      | some item =>
        match Ref.decodeJoinedEncodings (bs.drop L) with
        | none => none
        | some items => some (item :: items) := by
  obtain ⟨b0, tail, rfl⟩ := List.exists_cons_of_ne_nil hbs
  simp only [Ref.decodeJoinedEncodings]
  split
  · rename_i heq
    rw [heq] at hL
    exact absurd hL (by simp)
  · rename_i L' heq
    rw [heq] at hL
    injection hL with hL
    subst hL
    rw [if_pos hle]
    rfl

/-- The two mutual completeness statements, proved together by induction on the
    same measure the soundness induction uses (`3 * window + phase`): the list
    payload is at least one byte smaller than its encoding, and every joined
    sub-window is a strict sub-slice. -/
private theorem Ref.complete_aux : ∀ n : Nat,
    (∀ item : RLPItem, 3 * (encode item).length + 1 ≤ n →
        (encode item).length < 256 ^ 8 → Ref.decode (encode item) = some item)
    ∧ (∀ items : List RLPItem, 3 * (encode.encodeItems items).length + 2 ≤ n →
        (encode.encodeItems items).length < 256 ^ 8 →
        Ref.decodeJoinedEncodings (encode.encodeItems items) = some items) := by
  intro n
  induction n with
  | zero => exact ⟨fun item hn => absurd hn (by omega), fun items hn => absurd hn (by omega)⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro item hn hb
      cases item with
      | bytes data =>
        simp only [encode] at hb ⊢
        have hdlen : data.length < 256 ^ 8 :=
          Nat.lt_of_le_of_lt (le_encodeBytes_length data) hb
        obtain ⟨e0, etail, hshape, hle⟩ := encodeBytes_head data hdlen
        rw [hshape]
        simp only [Ref.decode]
        rw [if_pos hle, ← hshape, Ref.decodeToBytes_encodeBytes data hdlen]
        rfl
      | list items =>
        by_cases h55 : (encode.encodeItems items).length ≤ 55
        · rw [encode_list_short items h55] at hn hb ⊢
          simp only [List.length_cons] at hn hb
          have hseq : Ref.decodeToSequence
              (BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)
                :: encode.encodeItems items) = some items := by
            simp only [Ref.decodeToSequence, List.length_cons]
            rw [toNat_ofNat8 (show 0xC0 + (encode.encodeItems items).length < 256 by omega),
                show 0xC0 + (encode.encodeItems items).length - 192
                  = (encode.encodeItems items).length from by omega,
                List.take_length]
            split
            · rename_i hcond; exact absurd hcond (by omega)
            split
            · split
              · rename_i hcond; exact absurd hcond (by omega)
              split
              · rename_i hcond; exact absurd hcond (by omega)
              exact ih2 items (by omega) (by omega)
            · rename_i hcond
              exact absurd (show 0xC0 + (encode.encodeItems items).length ≤ 247 by omega)
                hcond
          simp only [Ref.decode]
          rw [toNat_ofNat8 (show 0xC0 + (encode.encodeItems items).length < 256 by omega)]
          rw [if_neg (by omega), hseq]
          rfl
        · have hlong : 55 < (encode.encodeItems items).length := by omega
          rw [encode_list_long items hlong] at hn hb ⊢
          simp only [List.length_cons, List.length_append] at hn hb
          have hplen : (encode.encodeItems items).length < 256 ^ 8 := by omega
          have hk8 : (Nat.toBytesBE (encode.encodeItems items).length).length ≤ 8 :=
            Nat.toBytesBE_length_le _ _ hplen
          obtain ⟨c, tl, hcons, hc0⟩ :=
            Nat.toBytesBE_eq_cons_of_pos (encode.encodeItems items).length (by omega)
          have hk1 : 1 ≤ (Nat.toBytesBE (encode.encodeItems items).length).length := by
            rw [hcons]; simp
          have hseq : Ref.decodeToSequence
              (BitVec.ofNat 8
                  (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)
                :: (Nat.toBytesBE (encode.encodeItems items).length
                    ++ encode.encodeItems items)) = some items := by
            simp only [Ref.decodeToSequence, List.length_cons, List.length_append]
            rw [toNat_ofNat8
                  (show 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length
                      < 256 by omega),
                show 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length - 247
                  = (Nat.toBytesBE (encode.encodeItems items).length).length from by omega,
                List.take_left, Nat.fromBytesBE_toBytesBE, List.drop_left, List.take_length]
            split
            · rename_i hcond; exact absurd hcond (by omega)
            split
            · rename_i hcond; exact absurd hcond (by omega)
            split
            · rename_i hcond; exact absurd hcond (by omega)
            split
            · rename_i hcond
              rw [hcons] at hcond
              simp only [List.cons_append, List.getD_cons_zero] at hcond
              exact absurd hcond hc0
            split
            · rename_i hcond; exact absurd hcond (by omega)
            split
            · rename_i hcond; exact absurd hcond (by omega)
            split
            · rename_i hcond; exact absurd hcond (by omega)
            exact ih2 items (by omega) (by omega)
          simp only [Ref.decode]
          rw [toNat_ofNat8
                (show 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length < 256
                  by omega)]
          rw [if_neg (by omega), hseq]
          rfl
    · intro items hn hb
      cases items with
      | nil =>
        rw [show encode.encodeItems [] = ([] : List Byte) from rfl]
        simp [Ref.decodeJoinedEncodings]
      | cons item items' =>
        have hsplit : encode.encodeItems (item :: items')
            = encode item ++ encode.encodeItems items' := rfl
        have hlen_split : (encode.encodeItems (item :: items')).length
            = (encode item).length + (encode.encodeItems items').length := by
          rw [hsplit, List.length_append]
        have hipos : 0 < (encode item).length := encode_nonempty item
        have hbi : (encode item).length < 256 ^ 8 := by omega
        have hL := Ref.decodeItemLength_encode item (encode.encodeItems items') hbi
        rw [hsplit]
        rw [Ref.decodeJoinedEncodings_step
              (by intro hnil
                  have := congrArg List.length hnil
                  simp only [List.length_append, List.length_nil] at this
                  omega)
              hL (by rw [List.length_append]; omega),
            List.take_left, List.drop_left,
            ih1 item (by omega) hbi, ih2 items' (by omega) (by omega)]

/-- **Completeness of `Ref.decode`**: any encoding whose length fits the
    8-byte length field decodes to its item. -/
theorem Ref.decode_encode (item : RLPItem) (h : (encode item).length < 256 ^ 8) :
    Ref.decode (encode item) = some item :=
  (Ref.complete_aux (3 * (encode item).length + 1)).1 item (Nat.le_refl _) h

/-- **Completeness of `Ref.decodeJoinedEncodings`** on a concatenation of
    encodings. -/
theorem Ref.decodeJoinedEncodings_encodeItems (items : List RLPItem)
    (h : (encode.encodeItems items).length < 256 ^ 8) :
    Ref.decodeJoinedEncodings (encode.encodeItems items) = some items :=
  (Ref.complete_aux (3 * (encode.encodeItems items).length + 2)).2 items (Nat.le_refl _) h

/-! ## The transfer -/

/-- ⭐ **The reference-shaped decoder equals the streaming decoder** on every
    input the streaming decoder's 8-byte length field can express.  A
    `decodeFully` accept is canonical (`encode_decodeFully`), so `Ref.decode`
    accepts it too (completeness); a `Ref.decode` accept is canonical
    (`Ref.decode_sound`), so `decodeFully` accepts it too (`decodeFully_encode`)
    — hence the two decoders' `Option` results coincide outright. -/
theorem Ref.decode_eq_decodeFully (bs : List Byte) (h : bs.length < 256 ^ 8) :
    Ref.decode bs = decodeFully bs := by
  cases hd : decodeFully bs with
  | some item =>
    have henc : encode item = bs := encode_decodeFully hd
    rw [← henc] at h ⊢
    exact Ref.decode_encode item h
  | none =>
    cases hr : Ref.decode bs with
    | none => rfl
    | some item =>
      have hbs : bs = encode item := Ref.decode_sound hr
      have hfull : decodeFully bs = some item := by
        rw [hbs]
        exact decodeFully_encode item (by rw [← hbs]; exact h)
      rw [hd] at hfull
      exact absurd hfull (by simp)

end EvmAsm.EL.RLP
