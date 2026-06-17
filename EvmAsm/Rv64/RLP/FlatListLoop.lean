/-
  EvmAsm.Rv64.RLP.FlatListLoop

  EL.3 — foundations for the RV64 RLP flat-item list-decode loop closure: the
  `isFlatItem` predicate and the **stride-equivalence** linking the operational
  per-item stride to the pure encoding length.

  A flat item (singleByte / short byte-string / short list) is decoded by the
  loop body (`fll_body_spec_within`) in one pass, advancing the pointer by
  `itemTotalLen` of the item's first byte. `encode_head_eq_itemTotalLen` proves
  this stride equals `(encode item).length` — the bridge between the machine
  loop and the pure `encode`/`decodeItems` round-trip. The n-iteration closure
  (count-induction over a list of flat items, threading the variable byte
  offset) and the `decodeItems` bridge build on these (next PR).
-/

import EvmAsm.Rv64.RLP.FlatListLoopBody
import EvmAsm.Rv64.RLP.SingleByteListLoop
import EvmAsm.EL.RLP.Properties
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_1)

/-- `(BitVec.ofNat 8 k).toNat = k` for a byte-sized `k`. -/
private theorem toNat_ofNat8 {k : Nat} (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]; omega

-- ============================================================================
-- Flat items + the stride-equivalence
-- ============================================================================

/-- An RLP item whose encoding's first byte is a FLAT prefix
    (`singleByte`/`shortBytes`/`shortList`) — i.e. a short-form byte string
    (`≤ 55` bytes) or a short-form list (payload `≤ 55` bytes). -/
def isFlatItem : RLPItem → Prop
  | .bytes data => data.length ≤ 55
  | .list items => (encode.encodeItems items).length ≤ 55

/-- The head byte of `encode (.bytes data)` for a non-singleton short string. -/
private theorem encode_bytes_multi_head {b c : Byte} {rest : List Byte}
    (hlen : (b :: c :: rest).length ≤ 55) :
    (encode (.bytes (b :: c :: rest)))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0x80 + (b :: c :: rest).length)
    ∧ (encode (.bytes (b :: c :: rest))).length = 1 + (b :: c :: rest).length := by
  have henc : encode (.bytes (b :: c :: rest))
      = [BitVec.ofNat 8 (0x80 + (b :: c :: rest).length)] ++ (b :: c :: rest) :=
    encodeBytes_short_of_length_ne_one _ hlen (by simp)
  exact ⟨by simp [henc], by simp [henc, Nat.add_comm]⟩

/-- The head byte of `encode (.list items)` for a short list. -/
private theorem encode_list_head {items : List RLPItem}
    (hflat : (encode.encodeItems items).length ≤ 55) :
    (encode (.list items))[0]'(encode_nonempty _)
      = BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)
    ∧ (encode (.list items)).length = 1 + (encode.encodeItems items).length := by
  have henc : encode (.list items)
      = [BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)] ++ encode.encodeItems items := by
    simp only [encode, hflat, if_true]
  exact ⟨by simp [henc], by simp [henc, Nat.add_comm]⟩

/-- The first byte of a flat item's encoding classifies as a flat prefix. -/
theorem classifyPrefix_encode_head_flat (item : RLPItem) (hflat : isFlatItem item) :
    classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .singleByte
      ∨ classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .shortBytes
      ∨ classifyPrefix ((encode item)[0]'(encode_nonempty item)) = .shortList := by
  cases item with
  | bytes data =>
    simp only [isFlatItem] at hflat
    cases data with
    | nil =>
      right; left
      have hh : (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x80 := by
        simp [encode, encodeBytes]
      rw [hh, classifyPrefix_shortBytes_iff, toNat_ofNat8 (by omega)]; omega
    | cons b tail =>
      cases tail with
      | nil =>
        by_cases hb : b.toNat < 0x80
        · left
          have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = b := by
            simp [encode, encodeBytes, hb]
          rw [hh, classifyPrefix_singleByte_iff]; exact hb
        · right; left
          have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x81 := by
            simp [encode, encodeBytes, hb]
          rw [hh, classifyPrefix_shortBytes_iff, toNat_ofNat8 (by omega)]; omega
      | cons c rest =>
        right; left
        obtain ⟨hh, _⟩ := encode_bytes_multi_head (b := b) (c := c) (rest := rest) hflat
        rw [hh, classifyPrefix_shortBytes_iff, toNat_ofNat8 (by simp only [List.length_cons] at hflat ⊢; omega)]
        simp only [List.length_cons] at hflat ⊢; omega
  | list items =>
    right; right
    simp only [isFlatItem] at hflat
    obtain ⟨hh, _⟩ := encode_list_head hflat
    rw [hh, classifyPrefix_shortList_iff, toNat_ofNat8 (by omega)]; omega

/-- **Stride-equivalence.** For a flat item, the operational per-item stride
    `itemTotalLen` of its encoding's first byte equals the encoding length. -/
theorem encode_head_eq_itemTotalLen (item : RLPItem) (hflat : isFlatItem item) :
    itemTotalLen ((encode item)[0]'(encode_nonempty item))
      = BitVec.ofNat 64 (encode item).length := by
  cases item with
  | bytes data =>
    simp only [isFlatItem] at hflat
    cases data with
    | nil =>
      have hh : (encode (.bytes ([] : List Byte)))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x80 := by
        simp [encode, encodeBytes]
      have hl : (encode (.bytes ([] : List Byte))).length = 1 := by simp [encode, encodeBytes]
      have hk : (0x80 : Nat) < 256 := by omega
      have hcls : classifyPrefix (BitVec.ofNat 8 0x80) = .shortBytes := by
        rw [classifyPrefix_shortBytes_iff, toNat_ofNat8 hk]; omega
      rw [hh, hl]; simp only [itemTotalLen, hcls, rlpPrefixShortBytesPayloadLen, toNat_ofNat8 hk, se12_1]
      decide
    | cons b tail =>
      cases tail with
      | nil =>
        by_cases hb : b.toNat < 0x80
        · have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = b := by
            simp [encode, encodeBytes, hb]
          have hl : (encode (.bytes [b])).length = 1 := by simp [encode, encodeBytes, hb]
          rw [hh, hl]; simp only [itemTotalLen, (classifyPrefix_singleByte_iff b).mpr hb]; decide
        · have hh : (encode (.bytes [b]))[0]'(encode_nonempty _) = BitVec.ofNat 8 0x81 := by
            simp [encode, encodeBytes, hb]
          have hl : (encode (.bytes [b])).length = 2 := by simp [encode, encodeBytes, hb]
          have hk : (0x81 : Nat) < 256 := by omega
          have hcls : classifyPrefix (BitVec.ofNat 8 0x81) = .shortBytes := by
            rw [classifyPrefix_shortBytes_iff, toNat_ofNat8 hk]; omega
          rw [hh, hl]; simp only [itemTotalLen, hcls, rlpPrefixShortBytesPayloadLen, toNat_ofNat8 hk, se12_1]
          decide
      | cons c rest =>
        obtain ⟨hh, hl⟩ := encode_bytes_multi_head (b := b) (c := c) (rest := rest) hflat
        have hk : 0x80 + (b :: c :: rest).length < 256 := by
          simp only [List.length_cons] at hflat ⊢; omega
        have hcls : classifyPrefix (BitVec.ofNat 8 (0x80 + (b :: c :: rest).length)) = .shortBytes := by
          rw [classifyPrefix_shortBytes_iff, toNat_ofNat8 hk]; omega
        rw [hh, hl]
        simp only [itemTotalLen, hcls, rlpPrefixShortBytesPayloadLen, toNat_ofNat8 hk, se12_1]
        have hsub : (0x80 + (b :: c :: rest).length) - 0x80 = (b :: c :: rest).length := by omega
        rw [hsub]; bv_omega
  | list items =>
    simp only [isFlatItem] at hflat
    obtain ⟨hh, hl⟩ := encode_list_head hflat
    have hk : 0xC0 + (encode.encodeItems items).length < 256 := by omega
    have hcls : classifyPrefix (BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)) = .shortList := by
      rw [classifyPrefix_shortList_iff, toNat_ofNat8 hk]; omega
    rw [hh, hl]
    simp only [itemTotalLen, hcls, rlpPrefixShortListPayloadLen, toNat_ofNat8 hk, se12_1]
    have hsub : (0xC0 + (encode.encodeItems items).length) - 0xC0 = (encode.encodeItems items).length := by omega
    rw [hsub]; bv_omega

-- Sanity: representative flat items, and the stride-equivalence instantiated.
example : isFlatItem (.bytes [(0x05 : Byte)]) := by simp [isFlatItem]
example : isFlatItem (.bytes [(0xAB : Byte)]) := by simp [isFlatItem]
example : isFlatItem (.list ([] : List RLPItem)) := by simp [isFlatItem, encode.encodeItems]
example :
    itemTotalLen ((encode (.bytes [(0x05 : Byte)]))[0]'(encode_nonempty _))
      = BitVec.ofNat 64 (encode (.bytes [(0x05 : Byte)])).length :=
  encode_head_eq_itemTotalLen _ (by simp [isFlatItem])

end EvmAsm.Rv64.RLP
