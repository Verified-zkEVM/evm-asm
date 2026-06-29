/-
  EvmAsm.Rv64.RLP.WalkDecodeBridge

  Bridges the machine-level RLP item view used by the verified walk routines
  (`rlp_walk_next` / `rlpItemDecode`: a byte list with a `Nat` offset, prefix-range
  guards, and a content slice) to the pure spec decoder `EvmAsm.EL.RLP.decodeAux`.

  These lemmas are the reusable heart of anchoring walk-based decoders (e.g. the
  verified `withdrawal_decode`) on the pure `decodeFully` / `decodeWithdrawal`.
  This file covers the **byte-string** item classes (single byte, short byte string)
  — the only forms a fixed `uint64` / 20-byte-address field can take.
-/

import EvmAsm.EL.RLP.PrefixDecode
import EvmAsm.EL.RLP.Properties
import EvmAsm.EL.RLP.FullDecode
import EvmAsm.EL.RLP.ListDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.EL.RLP

/-- A byte present at offset `off` peels off the front of `drop off`. -/
theorem drop_eq_cons_of_getElem? {bytes : List Byte} {off : Nat} {b : Byte}
    (hget : bytes[off]? = some b) :
    bytes.drop off = b :: bytes.drop (off + 1) := by
  have hlt : off < bytes.length := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.1
  have hb : bytes[off] = b := by
    rw [List.getElem?_eq_getElem hlt] at hget; exact Option.some.inj hget
  rw [List.drop_eq_getElem_cons hlt, hb]

/-- **Single-byte bridge.** A byte `b < 0x80` at offset `off` decodes (with any positive
    fuel) to the single-byte item `.bytes [b]`, consuming exactly one byte. -/
theorem decodeAux_singleByte_bridge (bytes : List Byte) (off : Nat) (b : Byte)
    (hget : bytes[off]? = some b) (hsingle : b.toNat < 0x80) (n : Nat) :
    decodeAux (n + 1) (bytes.drop off) = some (.bytes [b], bytes.drop (off + 1)) := by
  rw [drop_eq_cons_of_getElem? hget]
  exact decodeAux_cons_singleByte_of_classifyPrefix n b (bytes.drop (off + 1))
    ((classifyPrefix_singleByte_iff b).mpr hsingle)

set_option maxRecDepth 8000 in
/-- **Short-byte-string bridge.** A prefix `b ∈ [0x80, 0xB7]` at offset `off`, with the
    declared `len = b - 0x80` content bytes available and (for `len = 1`) a canonical
    content byte `≥ 0x80`, decodes (with any positive fuel) to `.bytes content` where
    `content = (drop (off+1)).take len`, consuming `1 + len` bytes total. -/
theorem decodeAux_shortBytes_bridge (bytes : List Byte) (off : Nat) (b : Byte)
    (hget : bytes[off]? = some b) (hlo : 0x80 ≤ b.toNat) (hhi : b.toNat ≤ 0xB7)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length)
    (hcanon : b.toNat - 0x80 = 1 →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80)
    (n : Nat) :
    decodeAux (n + 1) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)),
        bytes.drop (off + 1 + (b.toNat - 0x80))) := by
  rw [drop_eq_cons_of_getElem? hget,
    decodeAux_cons_shortBytes_of_classifyPrefix n b (bytes.drop (off + 1))
      ((classifyPrefix_shortBytes_iff b).mpr ⟨hlo, hhi⟩)]
  -- The payload length encoded in the prefix is `b - 0x80`.
  have hpl : rlpPrefixShortBytesPayloadLen b = b.toNat - 0x80 := rfl
  rw [hpl]
  -- `takeBytes (drop (off+1)) len` succeeds: enough bytes remain.
  have htk : takeBytes (bytes.drop (off + 1)) (b.toNat - 0x80) =
      some ((bytes.drop (off + 1)).take (b.toNat - 0x80),
        bytes.drop (off + 1 + (b.toNat - 0x80))) := by
    have hge : b.toNat - 0x80 ≤ (bytes.drop (off + 1)).length := by
      rw [List.length_drop]; omega
    rw [takeBytes_length_ge hge, List.drop_drop]
  rw [htk]
  -- Generalize the content list to a variable, then case on it: the monadic bind and the
  -- single-byte canonicality `match` reduce concretely per case (no `simp` recursion into
  -- the symbolic `take`/`drop`).
  generalize hC : (bytes.drop (off + 1)).take (b.toNat - 0x80) = C
  rcases C with _ | ⟨b0, _ | ⟨c0, t⟩⟩
  · rfl
  · -- singleton content `[b0]` ⇒ `len = 1` ⇒ canonical content byte `≥ 0x80`.
    have hlen1 : b.toNat - 0x80 = 1 := by
      have hl := congrArg List.length hC
      simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at hl
      omega
    obtain ⟨c, hcget, hcge⟩ := hcanon hlen1
    have hcc : (bytes.drop (off + 1)).take (b.toNat - 0x80) = [c] := by
      rw [hlen1, drop_eq_cons_of_getElem? hcget]; rfl
    rw [hcc] at hC
    have hbc' : b0.toNat = c.toNat := by rw [(by simpa using hC.symm : b0 = c)]
    simp only [Nat.not_lt] at hcge
    simp only [Option.bind_eq_bind, Option.bind_some, if_neg (by omega : ¬ b0.toNat < 0x80)]
  · rfl

/-! ### `decodeItems` composition steps

These chain a byte-string item bridge with the recursive item decoder, so a payload that is a
run of byte-string items (as the verified walk produces them) decodes as the corresponding
`.bytes` item list. Fuel is `n + 2` at the outer level so the inner `decodeAux` runs at `n + 1`
(the bridge's positive-fuel form) and the recursive `decodeItems` continues at `n + 1`. -/

/-- **Unified `decodeItems` step.** Given any item whose `decodeAux` consumes
    `[off, nextOff)` and the recursive decode of the tail from `nextOff`, prepend the item.
    Single-byte and short-byte-string items are the instances (via the bridges above); this
    form lets the 4-field assembly treat them uniformly. -/
theorem decodeItems_cons_of_decodeAux (bytes : List Byte) (off nextOff : Nat) (item : RLPItem)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hne : bytes.drop off ≠ [])
    (hitem : decodeAux (n + 1) (bytes.drop off) = some (item, bytes.drop nextOff))
    (hrest : decodeItems (n + 1) (bytes.drop nextOff) = some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) = some (item :: items, rest') := by
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne, hitem]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]

/-- **Reverse of `decodeItems_cons_of_decodeAux`.** A nonempty `decodeItems` run yielding a cons
    decomposes into the head `decodeAux` step (leaving some rest `r`) followed by a `decodeItems`
    run over `r`. Monadic-bind inversion of `decodeItems_succ_of_ne_nil`; a backbone of the reverse
    walk↔`decodeFully` bridge (decomposing a 4-item list back into its per-item `decodeAux` steps,
    which the capstone success case needs to discharge `wd_decode_successLeaf`'s hypotheses). -/
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
      subst hi his hr'
      exact ⟨r, rfl, hr⟩

/-- **Four-byte-string-item assembly.** A run of four byte-string items at `off0 < off1 < off2 <
    off3`, each consuming up to the next offset (`hi`, fuel-parametric as the bridges provide),
    and ending exactly at `off4` (`hend`), decodes as the four-item `.bytes` list with no
    leftover — for any fuel `≥ 5` (always met: a withdrawal payload is well over 3 bytes). -/
theorem decodeItems_four_of_decodeAux (bytes : List Byte)
    (off0 off1 off2 off3 off4 : Nat) (item0 item1 item2 item3 : RLPItem) (k : Nat)
    (h0 : ∀ m, decodeAux (m + 1) (bytes.drop off0) = some (item0, bytes.drop off1))
    (h1 : ∀ m, decodeAux (m + 1) (bytes.drop off1) = some (item1, bytes.drop off2))
    (h2 : ∀ m, decodeAux (m + 1) (bytes.drop off2) = some (item2, bytes.drop off3))
    (h3 : ∀ m, decodeAux (m + 1) (bytes.drop off3) = some (item3, bytes.drop off4))
    (hend : bytes.drop off4 = []) :
    decodeItems (k + 5) (bytes.drop off0) = some ([item0, item1, item2, item3], []) := by
  have hne : ∀ {o item r}, decodeAux 1 (bytes.drop o) = some (item, r) → bytes.drop o ≠ [] := by
    intro o item r h hnil; rw [hnil, decodeAux_nil] at h; simp at h
  have base : decodeItems (k + 1) (bytes.drop off4) = some ([], []) := by rw [hend]; rfl
  have s3 := decodeItems_cons_of_decodeAux bytes off3 off4 item3 [] [] k
    (hne (h3 0)) (h3 k) base
  have s2 := decodeItems_cons_of_decodeAux bytes off2 off3 item2 _ [] (k + 1)
    (hne (h2 0)) (h2 (k + 1)) s3
  have s1 := decodeItems_cons_of_decodeAux bytes off1 off2 item1 _ [] (k + 2)
    (hne (h1 0)) (h1 (k + 2)) s2
  exact decodeItems_cons_of_decodeAux bytes off0 off1 item0 _ [] (k + 3)
    (hne (h0 0)) (h0 (k + 3)) s1

/-- One `decodeItems` step over a single-byte item at offset `off`. -/
theorem decodeItems_cons_singleByte (bytes : List Byte) (off : Nat) (b : Byte)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hget : bytes[off]? = some b) (hsingle : b.toNat < 0x80)
    (hrest : decodeItems (n + 1) (bytes.drop (off + 1)) = some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) = some (.bytes [b] :: items, rest') := by
  have hne : bytes.drop off ≠ [] := by rw [drop_eq_cons_of_getElem? hget]; simp
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne,
    decodeAux_singleByte_bridge bytes off b hget hsingle n]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]

set_option maxRecDepth 8000 in
/-- One `decodeItems` step over a short-byte-string item at offset `off`. -/
theorem decodeItems_cons_shortBytes (bytes : List Byte) (off : Nat) (b : Byte)
    (items : List RLPItem) (rest' : List Byte) (n : Nat)
    (hget : bytes[off]? = some b) (hlo : 0x80 ≤ b.toNat) (hhi : b.toNat ≤ 0xB7)
    (hlen : off + 1 + (b.toNat - 0x80) ≤ bytes.length)
    (hcanon : b.toNat - 0x80 = 1 →
      ∃ c : Byte, bytes[off + 1]? = some c ∧ ¬ c.toNat < 0x80)
    (hrest : decodeItems (n + 1) (bytes.drop (off + 1 + (b.toNat - 0x80))) = some (items, rest')) :
    decodeItems (n + 2) (bytes.drop off) =
      some (.bytes ((bytes.drop (off + 1)).take (b.toNat - 0x80)) :: items, rest') := by
  have hne : bytes.drop off ≠ [] := by rw [drop_eq_cons_of_getElem? hget]; simp
  rw [decodeItems_succ_of_ne_nil (n + 1) (bytes.drop off) hne,
    decodeAux_shortBytes_bridge bytes off b hget hlo hhi hlen hcanon n]
  simp only [Option.bind_eq_bind, Option.bind_some, hrest]

/-! ### Capstone: outer short-list of four byte-string items ⟹ `decodeFully` -/

/-- **M2 capstone (short-list).** If `pfx` is a short-list prefix whose declared payload length
    equals `|payload|`, and `payload` is exactly a run of four byte-string items (each consuming
    up to the next offset, fuel-parametric; ending at `off4` with `payload.drop off4 = []`), then
    the full input `pfx :: payload` decodes (no trailing bytes) to the four-item `.bytes` list.
    A withdrawal's outer list is always short (payload `< 55` bytes), so this is the only outer
    form needed. -/
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
    refine (ListDecodeBridge.decodeAux_cons_shortList_eq_some_iff (2 * payload.length + 1) pfx
      payload h_class [item0, item1, item2, item3] []).mpr ?_
    refine ⟨payload, ?_, ?_⟩
    · rw [h_len, takeBytes_length_ge (le_refl payload.length), List.take_length, List.drop_length]
    · apply ListDecodeBridge.decodeListPayload_eq_some_of_decodeItems_empty
      obtain ⟨k, hk⟩ : ∃ k, 2 * payload.length + 1 = k + 5 := ⟨2 * payload.length - 4, by omega⟩
      rw [hk]
      have h0' : ∀ m, decodeAux (m + 1) (payload.drop 0) = some (item0, payload.drop off1) := by
        simp only [List.drop_zero]; exact h0
      have hfour := decodeItems_four_of_decodeAux payload 0 off1 off2 off3 off4
        item0 item1 item2 item3 k h0' h1 h2 h3 hend
      rwa [List.drop_zero] at hfour
  simp [decodeFully, hdec]
