/-
  EvmAsm.Rv64.RLP.NestedDescendOne

  EL.3 / Phase 5 (nested decode) — the descend-one-level kernel. The single-item
  decoder, applied to a `.list` item, leaves `x13 = itemPtrRegion` (payload start
  pointer) and `x11 = itemLenRegion` (payload byte length). `list_item_payload_window`
  proves that this operational window is EXACTLY the `encode.encodeItems items`
  payload — the bytes the pure `decodeAux` hands to `decodeItems` when it recurses
  into a list. This is the all-class analog, for the payload window, of the 5a
  stride lemma (`encode_head_eq_itemNextPtrRegion`), and the inductive kernel a
  recursive-descent decoder rests on: a caller can frame the payload sub-window
  `bs.drop payloadOff = encode.encodeItems items (++ tail)` and run the list loop on
  it to descend one level.
-/

import EvmAsm.Rv64.RLP.UnifiedItemStride
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

set_option maxRecDepth 4000

/-- `(BitVec.ofNat 8 k).toNat = k` for a byte-sized `k`. -/
private theorem toNat_ofNat8' {k : Nat} (h : k < 256) : (BitVec.ofNat 8 k).toNat = k := by
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]; omega

/-- **List-item payload window.** For a `.list items` item at byte offset `off` of
    the region, the single-item decoder's window — `itemPtrRegion` (the `x13`
    payload pointer) and `itemLenRegion` (the `x11` payload length) — points exactly
    at the `encode.encodeItems items` payload. The third conjunct
    (`bs.drop payloadOff = encode.encodeItems items ++ tail`) is precisely the
    precondition the list loop consumes, so a caller can descend into the sub-list. -/
theorem list_item_payload_window (items : List RLPItem) (tail : List Byte)
    (regionBase : Word) (off : Nat) (bs : List Byte)
    (hdrop : bs.drop off = encode (.list items) ++ tail)
    (hsize : (encode.encodeItems items).length < 256 ^ 8) :
    ∃ payloadOff,
      itemPtrRegion ((encode (.list items))[0]'(encode_nonempty _)) regionBase off
        = regionBase + BitVec.ofNat 64 payloadOff
      ∧ itemLenRegion ((encode (.list items))[0]'(encode_nonempty _)) bs off
        = BitVec.ofNat 64 (encode.encodeItems items).length
      ∧ bs.drop payloadOff = encode.encodeItems items ++ tail := by
  by_cases h55 : (encode.encodeItems items).length ≤ 55
  · -- short list: header is one prefix byte; payload starts at `off + 1`
    have henc : encode (.list items)
        = BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length)
            :: encode.encodeItems items :=
      encode_list_short items h55
    have hb : (encode (.list items))[0]'(encode_nonempty _)
        = BitVec.ofNat 8 (0xC0 + (encode.encodeItems items).length) := by simp [henc]
    have hcls : classifyPrefix ((encode (.list items))[0]'(encode_nonempty _)) = .shortList := by
      rw [hb, classifyPrefix_shortList_iff, toNat_ofNat8' (by omega)]; omega
    refine ⟨off + 1, ?_, ?_, ?_⟩
    · simp only [itemPtrRegion, hcls]
    · simp only [itemLenRegion, hcls]
      rw [hb, rlpPrefixShortListPayloadLen, toNat_ofNat8' (by omega)]
      congr 1; omega
    · have hdd : bs.drop (off + 1) = (bs.drop off).drop 1 := by rw [List.drop_drop]
      rw [hdd, hdrop, henc]
      simp only [List.cons_append, List.drop_succ_cons, List.drop_zero]
  · -- long list: header is prefix + `lenOfLen` length bytes; payload after them
    rw [Nat.not_le] at h55
    have hle : (Nat.toBytesBE (encode.encodeItems items).length).length ≤ 8 :=
      Nat.toBytesBE_length_le _ 8 hsize
    have henc : encode (.list items)
        = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)
            :: (Nat.toBytesBE (encode.encodeItems items).length ++ encode.encodeItems items) :=
      encode_list_long items h55
    have hb : (encode (.list items))[0]'(encode_nonempty _)
        = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length) := by
      simp [henc]
    have hcls : classifyPrefix ((encode (.list items))[0]'(encode_nonempty _)) = .longList := by
      rcases classifyPrefix_encode_head_long (.list items) (by simp [isLongItem]; omega)
        (by simpa [itemPayloadCount] using hsize) with h | h
      · exfalso; rw [hb, classifyPrefix_longBytes_iff, toNat_ofNat8' (by omega)] at h; omega
      · exact h
    have hlol : rlpPrefixLongListLenOfLen ((encode (.list items))[0]'(encode_nonempty _))
        = (Nat.toBytesBE (encode.encodeItems items).length).length := by
      rw [hb, rlpPrefixLongListLenOfLen, toNat_ofNat8' (by omega)]; omega
    refine ⟨(off + 1) + (Nat.toBytesBE (encode.encodeItems items).length).length, ?_, ?_, ?_⟩
    · simp only [itemPtrRegion, hcls, hlol]
    · -- the read length bytes round-trip to the payload count
      simp only [itemLenRegion, hcls, hlol]
      have hlenbytes : (bs.drop (off + 1)).take (Nat.toBytesBE (encode.encodeItems items).length).length
          = Nat.toBytesBE (encode.encodeItems items).length := by
        have hdd : bs.drop (off + 1) = (bs.drop off).drop 1 := by rw [List.drop_drop]
        rw [hdd, hdrop, henc]
        simp only [List.cons_append, List.append_assoc, List.drop_succ_cons, List.drop_zero]
        exact List.take_left' rfl
      rw [hlenbytes, Nat.fromBytesBE_toBytesBE]
    · -- skip the prefix + length bytes to reach the payload
      have hdd : bs.drop ((off + 1) + (Nat.toBytesBE (encode.encodeItems items).length).length)
          = ((bs.drop off).drop 1).drop (Nat.toBytesBE (encode.encodeItems items).length).length := by
        rw [List.drop_drop, List.drop_drop]; congr 1; omega
      rw [hdd, hdrop, henc]
      simp only [List.cons_append, List.append_assoc, List.drop_succ_cons, List.drop_zero]
      exact List.drop_left' rfl

/-- **Descend connection (top-level).** A top-level list decodes to its items, and
    the operational payload window points at exactly the bytes `decodeItems`
    consumes — so the list loop applied to `bs.drop payloadOff = encode.encodeItems
    items` descends one level, matching the pure `decode`/`decodeAux` recursion. -/
theorem decode_list_descend (items : List RLPItem)
    (hsize : (encode (.list items)).length < 256 ^ 8) :
    decode (encode (.list items)) = some (.list items, []) :=
  decode_encode (.list items) hsize

-- Sanity: a two-item nested list. The window points at the payload `[0x01, 0x02]`
-- (the encoded sub-items), and the pure decoder recovers the nested structure.
example (regionBase : Word) :=
  list_item_payload_window [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]] []
    regionBase 0 (encode (.list [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]))
    (by simp) (by decide)

example :
    decode (encode (.list [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]))
      = some (.list [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]], []) :=
  decode_list_descend _ (by decide)

-- A genuinely nested example (a list containing an empty list and a sub-list).
example :
    decode (encode (.list [.list [], .bytes [(0x01 : Byte)], .list [.bytes [(0x02 : Byte)]]]))
      = some (.list [.list [], .bytes [(0x01 : Byte)], .list [.bytes [(0x02 : Byte)]]], []) :=
  decode_list_descend _ (by decide)

end EvmAsm.Rv64.RLP
