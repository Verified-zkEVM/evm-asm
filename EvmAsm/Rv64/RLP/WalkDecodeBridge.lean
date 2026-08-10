/-
  EvmAsm.Rv64.RLP.WalkDecodeBridge

  Reusable pure bridge from the cursor-walk view used by `rlp_walk_next`
  to the EL RLP decoder.  The walk routines expose offsets into one byte
  buffer; these lemmas turn per-item offset facts into `decodeAux`,
  `decodeItems`, and finally `decodeFully` facts.
-/

import EvmAsm.EL.RLP.ByteStringDecodeBridge
import EvmAsm.EL.RLP.FullDecode
import EvmAsm.EL.RLP.ListDecodeBridge
import EvmAsm.EL.RLP.Properties
-- #11711: fuel monotonicity, which is what makes `DecodeChainFrom` below possible.
import EvmAsm.EL.RLP.FuelMono

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- A byte present at offset `off` peels off the front of `drop off`. -/
theorem drop_eq_cons_of_getElem? {bytes : List Byte} {off : Nat} {b : Byte}
    (hget : bytes[off]? = some b) :
    bytes.drop off = b :: bytes.drop (off + 1) := by
  have hlt : off < bytes.length := by
    rw [List.getElem?_eq_some_iff] at hget
    exact hget.1
  have hb : bytes[off] = b := by
    rw [List.getElem?_eq_getElem hlt] at hget
    exact Option.some.inj hget
  rw [List.drop_eq_getElem_cons hlt, hb]

/-- Single-byte bridge from offset facts to the pure decoder. -/
theorem decodeAux_singleByte_bridge (bytes : List Byte) (off : Nat) (b : Byte)
    (hget : bytes[off]? = some b) (hsingle : b.toNat < 0x80) (n : Nat) :
    decodeAux (n + 1) (bytes.drop off) = some (.bytes [b], bytes.drop (off + 1)) := by
  rw [drop_eq_cons_of_getElem? hget]
  exact decodeAux_cons_singleByte_of_classifyPrefix n b (bytes.drop (off + 1))
    ((classifyPrefix_singleByte_iff b).mpr hsingle)

/-- Short-byte-string bridge from offset facts to the pure decoder. -/
theorem decodeAux_shortBytes_bridge (bytes : List Byte) (off : Nat) (b : Byte)
    (hget : bytes[off]? = some b) (hlo : 0x80 ≤ b.toNat) (hhi : b.toNat ≤ 0xB7)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length)
    (hcanon : b.toNat - 0x80 = 1 →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80)
    (n : Nat) :
    decodeAux (n + 1) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)),
        bytes.drop (off + 1 + (b.toNat - 0x80))) := by
  rw [drop_eq_cons_of_getElem? hget]
  let len := b.toNat - 0x80
  have hclass : classifyPrefix b = .shortBytes :=
    (classifyPrefix_shortBytes_iff b).mpr ⟨hlo, hhi⟩
  have hpayloadLen : rlpPrefixShortBytesPayloadLen b = len := rfl
  have htake : takeBytes (bytes.drop (off + 1)) len =
      some ((bytes.drop (off + 1)).take len, bytes.drop (off + 1 + len)) := by
    have hge : len ≤ (bytes.drop (off + 1)).length := by
      rw [List.length_drop]
      omega
    rw [takeBytes_length_ge hge, List.drop_drop]
  refine (ByteStringDecodeBridge.decodeAux_cons_shortBytes_eq_some_iff
    n b (bytes.drop (off + 1)) hclass
    ((bytes.drop (off + 1)).take len) (bytes.drop (off + 1 + len))).mpr ?_
  refine ⟨(bytes.drop (off + 1)).take len, ?_, rfl, ?_⟩
  · simpa [len, hpayloadLen] using htake
  · cases hC : (bytes.drop (off + 1)).take len with
    | nil => trivial
    | cons b0 tail =>
        cases tail with
        | nil =>
            have hlen1 : len = 1 := by
              have hl := congrArg List.length hC
              simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at hl
              omega
            obtain ⟨c, hcget, hcge⟩ := hcanon hlen1
            have hcc : (bytes.drop (off + 1)).take len = [c] := by
              rw [hlen1, drop_eq_cons_of_getElem? hcget]
              rfl
            rw [hC] at hcc
            have hb0c : b0 = c := by
              simpa using hcc
            simpa [hb0c] using hcge
        | cons _ _ => trivial

/-! ## `decodeItems` composition -/

/-- Prepend one decoded item to a recursive `decodeItems` run. -/
theorem decodeItems_cons_of_decodeAux (bytes : List Byte) (off nextOff : Nat) (item : RLPItem)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hne : bytes.drop off ≠ [])
    (hitem : decodeAux (n + 1) (bytes.drop off) = some (item, bytes.drop nextOff))
    (hrest : decodeItems (n + 1) (bytes.drop nextOff) = some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) = some (item :: items, rest') := by
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne, hitem]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]

/-- A successful nonempty `decodeItems` run decomposes into one `decodeAux` step and the tail. -/
theorem decodeItems_cons_inv (bs : List Byte) (item : RLPItem) (items : List RLPItem)
    (rest' : List Byte) (n : Nat) (hne : bs ≠ [])
    (h : decodeItems (n + 1) bs = some (item :: items, rest')) :
    ∃ r, decodeAux n bs = some (item, r) ∧ decodeItems n r = some (items, rest') := by
  rw [decodeItems_succ_of_ne_nil n bs hne] at h
  rcases hd : decodeAux n bs with _ | ⟨i, r⟩
  · simp [hd] at h
  · simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
    rcases hr : decodeItems n r with _ | ⟨is, r''⟩
    · simp [hr] at h
    · simp only [hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq,
        List.cons.injEq] at h
      obtain ⟨⟨hi, his⟩, hr'⟩ := h
      subst hi
      subst his
      subst hr'
      exact ⟨r, rfl, hr⟩

/-- Four byte-string item decodes compose to a four-item list payload. -/
theorem decodeItems_four_of_decodeAux (bytes : List Byte)
    (off0 off1 off2 off3 off4 : Nat) (item0 item1 item2 item3 : RLPItem) (k : Nat)
    (h0 : ∀ m, decodeAux (m + 1) (bytes.drop off0) = some (item0, bytes.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (bytes.drop off1) = some (item1, bytes.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (bytes.drop off2) = some (item2, bytes.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (bytes.drop off3) = some (item3, bytes.drop off4))
    (hend : bytes.drop off4 = []) :
    decodeItems (k + 5) (bytes.drop off0) = some ([item0, item1, item2, item3], []) := by
  have hne : ∀ {o item r}, decodeAux 1 (bytes.drop o) = some (item, r) → bytes.drop o ≠ [] := by
    intro o item r h hnil
    rw [hnil, decodeAux_nil] at h
    simp at h
  have base : decodeItems (k + 1) (bytes.drop off4) = some ([], []) := by
    rw [hend]
    rfl
  have s3 := decodeItems_cons_of_decodeAux bytes off3 off4 item3 [] [] k
    (hne (h3 0)) (h3 k) base
  have s2 := decodeItems_cons_of_decodeAux bytes off2 off3 item2 _ [] (k + 1)
    (hne (h2 0)) (h2 (k + 1)) s3
  have s1 := decodeItems_cons_of_decodeAux bytes off1 off2 item1 _ [] (k + 2)
    (hne (h1 0)) (h1 (k + 2)) s2
  exact decodeItems_cons_of_decodeAux bytes off0 off1 item0 _ [] (k + 3)
    (hne (h0 0)) (h0 (k + 3)) s1

/-- Prepend one decoded item to a recursive `decodeItems` run, phrased as a
    direct remainder chain instead of byte-offset drops.  This is the shape
    produced by validating WP field posts. -/
theorem decodeItems_cons_of_decodeAux_chain (bs bsNext : List Byte)
    (item : RLPItem) (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hne : bs ≠ [])
    (hitem : decodeAux (n + 1) bs = some (item, bsNext))
    (hrest : decodeItems (n + 1) bsNext = some (items, rest')) :
    decodeItems (n + 2) bs = some (item :: items, rest') := by
  rw [decodeItems_succ_of_ne_nil (n + 1) bs hne, hitem]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]

/-- Four byte-string item decodes compose to a four-item list payload, using
    only the successor remainders.  This avoids exposing synthetic offsets in
    generated WP proofs. -/
theorem decodeItems_four_of_decodeAux_chain
    (bs0 bs1 bs2 bs3 bs4 : List Byte)
    (item0 item1 item2 item3 : RLPItem) (k : Nat)
    (h0 : ∀ m, decodeAux (m + 1) bs0 = some (item0, bs1))
    (h1 : ∀ m, decodeAux (m + 1) bs1 = some (item1, bs2))
    (h2 : ∀ m, decodeAux (m + 1) bs2 = some (item2, bs3))
    (h3 : ∀ m, decodeAux (m + 1) bs3 = some (item3, bs4))
    (hend : bs4 = []) :
    decodeItems (k + 5) bs0 = some ([item0, item1, item2, item3], []) := by
  have hne : ∀ {bs item r}, decodeAux 1 bs = some (item, r) → bs ≠ [] := by
    intro bs item r h hnil
    rw [hnil, decodeAux_nil] at h
    simp at h
  have base : decodeItems (k + 1) bs4 = some ([], []) := by
    rw [hend]
    rfl
  have s3 := decodeItems_cons_of_decodeAux_chain bs3 bs4 item3 [] [] k
    (hne (h3 0)) (h3 k) base
  have s2 := decodeItems_cons_of_decodeAux_chain bs2 bs3 item2 _ [] (k + 1)
    (hne (h2 0)) (h2 (k + 1)) s3
  have s1 := decodeItems_cons_of_decodeAux_chain bs1 bs2 item1 _ [] (k + 2)
    (hne (h1 0)) (h1 (k + 2)) s2
  exact decodeItems_cons_of_decodeAux_chain bs0 bs1 item0 _ [] (k + 3)
    (hne (h0 0)) (h0 (k + 3)) s1

/-- One `decodeItems` step over a single-byte item at offset `off`. -/
theorem decodeItems_cons_singleByte (bytes : List Byte) (off : Nat) (b : Byte)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hget : bytes[off]? = some b) (hsingle : b.toNat < 0x80)
    (hrest : decodeItems (n + 1) (bytes.drop (off + 1)) = some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) = some (.bytes [b] :: items, rest') := by
  have hne : bytes.drop off ≠ [] := by
    rw [drop_eq_cons_of_getElem? hget]
    simp
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne,
    decodeAux_singleByte_bridge bytes off b hget hsingle n]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]

/-- One `decodeItems` step over a short-byte-string item at offset `off`. -/
theorem decodeItems_cons_shortBytes (bytes : List Byte) (off : Nat) (b : Byte)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hget : bytes[off]? = some b) (hlo : 0x80 ≤ b.toNat) (hhi : b.toNat ≤ 0xB7)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length)
    (hcanon : b.toNat - 0x80 = 1 →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80)
    (hrest : decodeItems (n + 1) (bytes.drop (off + 1 + (b.toNat - 0x80))) =
      some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)) :: items, rest') := by
  have hne : bytes.drop off ≠ [] := by
    rw [drop_eq_cons_of_getElem? hget]
    simp
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne,
    decodeAux_shortBytes_bridge bytes off b hget hlo hhi hlen hcanon n]
  change Option.bind
      (some (RLPItem.bytes (List.take (BitVec.toNat b - 128) (List.drop (off + 1) bytes)),
        List.drop (off + 1 + (BitVec.toNat b - 128)) bytes))
      (fun p => Option.bind (decodeItems (n + 1) p.2)
        (fun q => some (p.1 :: q.1, q.2))) =
    some (RLPItem.bytes (List.take (BitVec.toNat b - 128) (List.drop (off + 1) bytes)) ::
      items, rest')
  rw [Option.bind_some]
  rw [hrest]
  rfl


/-! ## Bridges from WP field posts -/

/-- A successful single-byte `decode` result can be reused at any positive
    `decodeAux` fuel.  Validating WP field posts often expose `decode`, while
    the list-level bridge composes `decodeAux`; this theorem is the lossless
    adapter between those views. -/
theorem decodeAux_singleByte_all_fuel_of_decode
    (pfx : Byte) (rest data rest' : List Byte)
    (h_class : classifyPrefix pfx = .singleByte)
    (hdecode : decode (pfx :: rest) = some (.bytes data, rest')) :
    ∀ m, decodeAux (m + 1) (pfx :: rest) = some (.bytes data, rest') := by
  rw [decode_cons_eq_decodeAux_fuel] at hdecode
  have hdecode' :
      decodeAux ((2 * rest.length + 1) + 1) (pfx :: rest) =
        some (.bytes data, rest') := by
    have hfuel : (2 * rest.length + 1) + 1 = 2 * rest.length + 2 := by omega
    rw [hfuel]
    exact hdecode
  have hwitness :=
    (ByteStringDecodeBridge.decodeAux_cons_singleByte_eq_some_iff
      (2 * rest.length + 1) pfx rest h_class data rest').mp hdecode'
  intro m
  exact (ByteStringDecodeBridge.decodeAux_cons_singleByte_eq_some_iff
    m pfx rest h_class data rest').mpr hwitness

/-- A successful short-byte-string `decode` result can be reused at any
    positive `decodeAux` fuel.  This lets generated WP proofs turn the pure
    field-post fact from a validating branch into the shape consumed by
    `decodeItems_four_of_decodeAux` and `decodeFully_shortList_four`. -/
theorem decodeAux_shortBytes_all_fuel_of_decode
    (pfx : Byte) (rest data rest' : List Byte)
    (h_class : classifyPrefix pfx = .shortBytes)
    (hdecode : decode (pfx :: rest) = some (.bytes data, rest')) :
    ∀ m, decodeAux (m + 1) (pfx :: rest) = some (.bytes data, rest') := by
  rw [decode_cons_eq_decodeAux_fuel] at hdecode
  have hdecode' :
      decodeAux ((2 * rest.length + 1) + 1) (pfx :: rest) =
        some (.bytes data, rest') := by
    have hfuel : (2 * rest.length + 1) + 1 = 2 * rest.length + 2 := by omega
    rw [hfuel]
    exact hdecode
  have hwitness :=
    (ByteStringDecodeBridge.decodeAux_cons_shortBytes_eq_some_iff
      (2 * rest.length + 1) pfx rest h_class data rest').mp hdecode'
  intro m
  exact (ByteStringDecodeBridge.decodeAux_cons_shortBytes_eq_some_iff
    m pfx rest h_class data rest').mpr hwitness

/-- Any successful byte-string `decode` result is stable for every positive
    `decodeAux` fuel. This is the field-post adapter used by WP-generated
    validating walks; callers do not need to expose the precise byte prefix
    class at semantic joins. -/
theorem decodeAux_bytes_all_fuel_of_decode
    (pfx : Byte) (rest data rest' : List Byte)
    (hdecode : decode (pfx :: rest) = some (.bytes data, rest')) :
    ∀ m, decodeAux (m + 1) (pfx :: rest) = some (.bytes data, rest') := by
  intro m
  unfold decode at hdecode
  unfold decodeAux at hdecode ⊢
  by_cases h80 : pfx.toNat < 0x80
  · simp [h80] at hdecode ⊢
    exact hdecode
  · by_cases hB7 : pfx.toNat ≤ 0xB7
    · simp [h80, hB7] at hdecode ⊢
      exact hdecode
    · by_cases hBF : pfx.toNat ≤ 0xBF
      · simp [h80, hB7, hBF] at hdecode ⊢
        exact hdecode
      · by_cases hF7 : pfx.toNat ≤ 0xF7
        · simp [h80, hB7, hBF, hF7] at hdecode ⊢
          cases htake : takeBytes rest (pfx.toNat - 0xC0) with
          | none => simp [htake] at hdecode
          | some pair =>
              rcases pair with ⟨payload, tail⟩
              simp [htake] at hdecode
              cases hitems : decodeItems (2 * rest.length + 1) payload with
              | none => simp [hitems] at hdecode
              | some decoded =>
                  rcases decoded with ⟨items, leftover⟩
                  cases h_empty : List.isEmpty leftover <;> simp [hitems] at hdecode
        · simp [h80, hB7, hBF, hF7] at hdecode ⊢
          cases hread : readLength rest (pfx.toNat - 0xF7) with
          | none => simp [hread] at hdecode
          | some pair =>
              rcases pair with ⟨lenVal, rest1⟩
              by_cases hcanon : lenVal ≤ 55
              · simp [hread, hcanon] at hdecode
              · simp [hread, hcanon] at hdecode
                cases htake : takeBytes rest1 lenVal with
                | none => simp [htake] at hdecode
                | some pair2 =>
                    rcases pair2 with ⟨payload, tail⟩
                    simp [htake] at hdecode
                    cases hitems : decodeItems (2 * rest.length + 1) payload with
                    | none => simp [hitems] at hdecode
                    | some decoded =>
                        rcases decoded with ⟨items, leftover⟩
                        cases h_empty : List.isEmpty leftover <;> simp [hitems] at hdecode

/-- List-shaped facade for `decodeAux_bytes_all_fuel_of_decode`.  Generated
    chain witnesses usually expose the current remainder as one list, not as a
    syntactic `pfx :: rest`; this theorem hides the nonempty decomposition. -/
theorem decodeAux_bytes_all_fuel_of_decode_list
    (bs data rest' : List Byte)
    (hdecode : decode bs = some (.bytes data, rest')) :
    ∀ m, decodeAux (m + 1) bs = some (.bytes data, rest') := by
  cases bs with
  | nil =>
      simp [decode, decodeAux] at hdecode
  | cons pfx rest =>
      exact decodeAux_bytes_all_fuel_of_decode pfx rest data rest' hdecode

/-! ## Capstone: outer short list of four byte-string items -/

/-- A short-list payload made of four decoded items is a full four-item RLP list. -/
theorem decodeFully_shortList_four (pfx : Byte) (payload : List Byte)
    (off1 off2 off3 off4 : Nat) (item0 item1 item2 item3 : RLPItem)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (item0, payload.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (payload.drop off1) = some (item1, payload.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (payload.drop off2) = some (item2, payload.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (payload.drop off3) = some (item3, payload.drop off4))
    (hend : payload.drop off4 = [])
    (h_min : 2 ≤ payload.length) :
    decodeFully (pfx :: payload) = some (.list [item0, item1, item2, item3]) := by
  have hdec : decode (pfx :: payload) = some (.list [item0, item1, item2, item3], []) := by
    rw [decode_cons_eq_decodeAux_fuel,
      show 2 * payload.length + 2 = (2 * payload.length + 1) + 1 from by omega]
    refine (ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff
      (2 * payload.length + 1) pfx payload h_class
      [item0, item1, item2, item3] []).mpr ?_
    refine ⟨payload, ?_, ?_⟩
    · rw [h_len, takeBytes_length_ge (le_refl payload.length), List.take_length, List.drop_length]
    · apply ListDecodeBridge.decodeListPayload_eq_some_of_decodeItems_empty
      obtain ⟨k, hk⟩ : ∃ k, 2 * payload.length + 1 = k + 5 := ⟨2 * payload.length - 4, by omega⟩
      rw [hk]
      have h0' : ∀ m, decodeAux (m + 1) (payload.drop 0) =
          some (item0, payload.drop off1) := by
        simp only [List.drop_zero]
        exact h0
      have hfour := decodeItems_four_of_decodeAux payload 0 off1 off2 off3 off4
        item0 item1 item2 item3 k h0' h1 h2 h3 hend
      rwa [List.drop_zero] at hfour
  simp [decodeFully, hdec]

/-- A short-list payload made of four decoded items is a full four-item RLP
    list, phrased over a remainder chain rather than offset drops. -/
theorem decodeFully_shortList_four_chain (pfx : Byte) (payload r1 r2 r3 r4 : List Byte)
    (item0 item1 item2 item3 : RLPItem)
    (h_class : classifyPrefix pfx = .shortList)
    (h_len : rlpPrefixShortListPayloadLen pfx = payload.length)
    (h0 : ∀ m, decodeAux (m + 1) payload = some (item0, r1))
    (h1 : ∀ m, decodeAux (m + 1) r1 = some (item1, r2))
    (h2 : ∀ m, decodeAux (m + 1) r2 = some (item2, r3))
    (h3 : ∀ m, decodeAux (m + 1) r3 = some (item3, r4))
    (hend : r4 = [])
    (h_min : 2 ≤ payload.length) :
    decodeFully (pfx :: payload) = some (.list [item0, item1, item2, item3]) := by
  have hdec : decode (pfx :: payload) = some (.list [item0, item1, item2, item3], []) := by
    rw [decode_cons_eq_decodeAux_fuel,
      show 2 * payload.length + 2 = (2 * payload.length + 1) + 1 from by omega]
    refine (ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff
      (2 * payload.length + 1) pfx payload h_class
      [item0, item1, item2, item3] []).mpr ?_
    refine ⟨payload, ?_, ?_⟩
    · rw [h_len, takeBytes_length_ge (le_refl payload.length), List.take_length, List.drop_length]
    · apply ListDecodeBridge.decodeListPayload_eq_some_of_decodeItems_empty
      obtain ⟨k, hk⟩ : ∃ k, 2 * payload.length + 1 = k + 5 := ⟨2 * payload.length - 4, by omega⟩
      rw [hk]
      exact decodeItems_four_of_decodeAux_chain payload r1 r2 r3 r4
        item0 item1 item2 item3 k h0 h1 h2 h3 hend
  simp [decodeFully, hdec]

/-! ## Arity-N composition (GH #11351)

    The helpers above are hard-coded to **four** items, written for the withdrawal
    4-tuple. `_decode_header` walks 21 or 23, so the header rows need the general form.

    ⭐ The generalisation is stated **relationally** rather than by indexing the offsets
    with `getD`: an indexed form makes both the statement and every proof obligation
    unreadable, whereas a chain predicate lets one induction do the work and reuses
    `decodeItems_cons_of_decodeAux` unchanged as the step.

    ⚠️ Each link demands fuel-insensitivity (`∀ m`), which is sound only for
    **byte-string** items (`decodeAux_bytes_all_fuel_of_decode`). Header fields all are.
    This is the same restriction that makes the nested-list case of #11341 unprovable —
    a nested list's decode *is* fuel-sensitive. -/

/-- A chain of byte-string decodes: starting at `off`, each item advances the offset,
    ending exactly at `offEnd`. -/
def DecodeChain (bytes : List Byte) : Nat → List RLPItem → Nat → Prop
  | off, [], offEnd => off = offEnd
  | off, item :: rest, offEnd =>
      ∃ off', (∀ m, decodeAux (m + 1) (bytes.drop off) = some (item, bytes.drop off'))
        ∧ DecodeChain bytes off' rest offEnd

/-- ⭐ **Arity-N `decodeItems` composition.** A decode chain ending at the end of input
    composes to a full `decodeItems` run over exactly those items. Generalises
    `decodeItems_four_of_decodeAux` to any length. -/
theorem decodeItems_of_chain (bytes : List Byte) :
    ∀ (items : List RLPItem) (off offEnd : Nat),
      DecodeChain bytes off items offEnd → bytes.drop offEnd = [] →
      ∀ k, decodeItems (k + items.length + 1) (bytes.drop off) = some (items, []) := by
  intro items
  induction items with
  | nil =>
    intro off offEnd hc hend k
    subst hc
    rw [hend]
    rfl
  | cons item rest ih =>
    intro off offEnd hc hend k
    obtain ⟨off', hitem, hrest⟩ := hc
    have hne : bytes.drop off ≠ [] := by
      intro hnil
      have h0 := hitem 0
      rw [hnil, decodeAux_nil] at h0
      simp at h0
    have hIH := ih off' offEnd hrest hend k
    have hcomp := decodeItems_cons_of_decodeAux bytes off off' item rest []
      (k + rest.length) hne (hitem (k + rest.length)) hIH
    have harith : k + (item :: rest).length + 1 = k + rest.length + 2 := by
      simp [List.length_cons]
      omega
    rw [harith]
    exact hcomp

/-- **Non-vacuity: the existing arity-four helper is an instance.** Reproducing
    `decodeItems_four_of_decodeAux`'s exact statement from the general lemma is the
    strongest available check that the generalisation is faithful — a chain predicate
    that had drifted from what the four-item version means would fail here.

    The arity-four helpers are left in place; this only demonstrates they are now
    derivable, so they can be retired in a follow-up if that is wanted. -/
example (bytes : List Byte) (off0 off1 off2 off3 off4 : Nat)
    (item0 item1 item2 item3 : RLPItem) (k : Nat)
    (h0 : ∀ m, decodeAux (m + 1) (bytes.drop off0) = some (item0, bytes.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (bytes.drop off1) = some (item1, bytes.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (bytes.drop off2) = some (item2, bytes.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (bytes.drop off3) = some (item3, bytes.drop off4))
    (hend : bytes.drop off4 = []) :
    decodeItems (k + 5) (bytes.drop off0) = some ([item0, item1, item2, item3], []) := by
  have hc : DecodeChain bytes off0 [item0, item1, item2, item3] off4 :=
    ⟨off1, h0, off2, h1, off3, h2, off4, h3, rfl⟩
  have hgen := decodeItems_of_chain bytes [item0, item1, item2, item3] off0 off4 hc hend k
  simpa using hgen

/-! ## Fuel-sensitive chains (GH #11711)

    `DecodeChain` above states each link as `∀ m, decodeAux (m + 1) … = some …`.
    That is provable for byte-string items and **false** for a nested list, whose
    decode recurses into `decodeItems nDepth`. #11711 records the consequence:
    every nested-list bridge is blocked, and `rlp_list_count_items` cannot reach
    `.bridged` — which is not an edge case, because #11675 put that routine on the
    `mpt_node_kind` path, where an inline embedded branch child *is* a nested list.

    ⭐ The fix is not to thread arithmetic through the links, which is what the
    issue's sketch does and what its own warning calls "the whole difficulty".
    `EL.RLP.decodeAux_mono_fuel` (fuel monotonicity: extra budget never changes a
    successful decode) makes that bookkeeping unnecessary — a link need only be
    exhibited at **one** budget, and every larger budget follows. So the
    fuel-sensitive predicate below carries a single `floor` and its links are plain
    `decodeAux floor … = some …` obligations, with no per-link fuel algebra at all.

    `DecodeChain` is **not** weakened: #11711 is explicit that it is correct and
    must not be relaxed into silently accepting lists. `DecodeChainFrom` is a new,
    strictly more general predicate, and `DecodeChain` is recovered as its
    `floor = 1` instance (`decodeChainFrom_of_decodeChain`). -/

/-- A chain of decodes each witnessed at budget `floor`, starting at `off` and
    ending exactly at `offEnd`.

    Unlike `DecodeChain` this admits **nested-list** items: the link is a decode at
    one concrete budget rather than a claim about all budgets, which for a list is
    the difference between provable and false. -/
def DecodeChainFrom (bytes : List Byte) (floor : Nat) : Nat → List RLPItem → Nat → Prop
  | off, [], offEnd => off = offEnd
  | off, item :: rest, offEnd =>
      ∃ off', decodeAux floor (bytes.drop off) = some (item, bytes.drop off')
        ∧ DecodeChainFrom bytes floor off' rest offEnd

/-- `DecodeChain`'s links are `DecodeChainFrom`'s at `floor = 1`: instantiate the
    universally quantified budget at `m := 0`. Gives the faithfulness direction —
    everything the old predicate accepts, the new one accepts. -/
theorem decodeChainFrom_of_decodeChain (bytes : List Byte) :
    ∀ (items : List RLPItem) (off offEnd : Nat),
      DecodeChain bytes off items offEnd → DecodeChainFrom bytes 1 off items offEnd := by
  intro items
  induction items with
  | nil => intro off offEnd hc; exact hc
  | cons item rest ih =>
    intro off offEnd hc
    obtain ⟨off', hitem, hrest⟩ := hc
    exact ⟨off', hitem 0, ih off' offEnd hrest⟩

/-- ⭐ **Arity-N `decodeItems` composition, fuel-sensitive.** The `DecodeChain`
    analogue for `DecodeChainFrom`, and the theorem #11711 asks for.

    The side condition `floor ≤ k + 1` is the honest cost of admitting lists, and
    it is a *single* inequality rather than per-link bookkeeping: the composition
    consumes link `i` at budget `k + (items.length - i)`, whose minimum over the
    chain is `k + 1` at the last item, so one bound covers every link. Monotonicity
    supplies each link at the budget the composition actually wants. -/
theorem decodeItems_of_chainFrom (bytes : List Byte) (floor : Nat) :
    ∀ (items : List RLPItem) (off offEnd : Nat),
      DecodeChainFrom bytes floor off items offEnd → bytes.drop offEnd = [] →
      ∀ k, floor ≤ k + 1 →
        decodeItems (k + items.length + 1) (bytes.drop off) = some (items, []) := by
  intro items
  induction items with
  | nil =>
    intro off offEnd hc hend k _
    subst hc
    rw [hend]
    rfl
  | cons item rest ih =>
    intro off offEnd hc hend k hfloor
    obtain ⟨off', hitem, hrest⟩ := hc
    -- The link is witnessed at `floor`; lift it to the budget this step consumes.
    have hlift : decodeAux (k + rest.length + 1) (bytes.drop off)
        = some (item, bytes.drop off') :=
      EL.RLP.decodeAux_mono_fuel (by omega) hitem
    have hne : bytes.drop off ≠ [] := by
      intro hnil
      rw [hnil, decodeAux_nil] at hlift
      simp at hlift
    have hIH := ih off' offEnd hrest hend k hfloor
    have hcomp := decodeItems_cons_of_decodeAux bytes off off' item rest []
      (k + rest.length) hne hlift hIH
    have harith : k + (item :: rest).length + 1 = k + rest.length + 2 := by
      simp [List.length_cons]
      omega
    rw [harith]
    exact hcomp

/-- **Non-vacuity, and no loss against `DecodeChain`.** The old arity-N
    composition is an instance of the new one: a `DecodeChain` becomes a
    `DecodeChainFrom` at `floor = 1`, whose side condition `1 ≤ k + 1` is free. So
    `DecodeChainFrom` subsumes `decodeItems_of_chain` rather than trading one
    restriction for another. -/
example (bytes : List Byte) (items : List RLPItem) (off offEnd : Nat)
    (hc : DecodeChain bytes off items offEnd) (hend : bytes.drop offEnd = []) (k : Nat) :
    decodeItems (k + items.length + 1) (bytes.drop off) = some (items, []) :=
  decodeItems_of_chainFrom bytes 1 items off offEnd
    (decodeChainFrom_of_decodeChain bytes items off offEnd hc) hend k (by omega)

/-- **The gain, stated: a nested list is now a legal link.** A single-item chain
    whose item is a `.list` — the shape `DecodeChain` cannot express, because a
    list's decode is fuel-sensitive — composes exactly like a byte-string link.
    This is the statement `rlp_list_count_items`' bridge needs; discharging its
    `decodeAux` hypothesis for the guest's actual node bytes is the routine-side
    follow-on, not a model-side gap. -/
example (bytes : List Byte) (off offEnd floor : Nat) (inner : List RLPItem)
    (hitem : decodeAux floor (bytes.drop off) = some (.list inner, bytes.drop offEnd))
    (hend : bytes.drop offEnd = []) (k : Nat) (hfloor : floor ≤ k + 1) :
    decodeItems (k + 2) (bytes.drop off) = some ([.list inner], []) := by
  have hc : DecodeChainFrom bytes floor off [.list inner] offEnd := ⟨offEnd, hitem, rfl⟩
  have hgen := decodeItems_of_chainFrom bytes floor [.list inner] off offEnd hc hend k hfloor
  simpa using hgen

end EvmAsm.Rv64.RLP
