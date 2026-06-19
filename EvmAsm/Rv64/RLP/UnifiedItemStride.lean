/-
  EvmAsm.Rv64.RLP.UnifiedItemStride

  EL.3 — the UNIFIED stride-equivalence for the long-capable list loop: the
  per-item pointer advance `itemNextPtrRegion` (= `itemPtrRegion + itemLenRegion`,
  the `ADD x13,x13,x11` result of the unified body) equals `regionBase + ofNat
  (off + (encode item).length)` for ANY item (all 5 classes). The all-class
  analog of the flat `encode_head_eq_itemTotalLen` (`FlatListLoop.lean`).

  Flat items reuse the flat stride (`encode_head_eq_itemTotalLen`, prefix-only).
  Long items need the runtime-read length tied back to the encoding: the length
  bytes the decoder reads from the region (`(bs.drop (off+1)).take lenOfLen`) ARE
  the encoding's `Nat.toBytesBE payloadCount`, so they round-trip to `payloadCount`.
  The unified loop closure (next PR) re-indexes its pointer with this lemma.
-/

import EvmAsm.Rv64.RLP.UnifiedListLoopBody
import EvmAsm.Rv64.RLP.LongItemStride
import EvmAsm.Rv64.RLP.FlatListLoop

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_1)

/-- `(regionBase + ofNat a) + ofNat b = regionBase + ofNat (a + b)`. -/
private theorem region_ptr_add' (regionBase : Word) (a b : Nat) :
    (regionBase + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = regionBase + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]

/-- Every RLP item is flat (`≤ 55`) or long (`> 55`). -/
theorem flat_or_long (item : RLPItem) : isFlatItem item ∨ isLongItem item := by
  cases item with
  | bytes data =>
    simp only [isFlatItem, isLongItem]; omega
  | list items =>
    simp only [isFlatItem, isLongItem]; omega

/-- The `lenOfLen` length bytes the decoder reads from the region (starting at
    `off+1`) are exactly the encoding's `Nat.toBytesBE payloadCount`. -/
private theorem long_lenBytes_in_region (head : RLPItem) (rest : List Byte)
    (bs : List Byte) (off : Nat) (hlong : isLongItem head)
    (hdrop : bs.drop off = encode head ++ rest) :
    (bs.drop (off + 1)).take (itemLenOfLen head) = Nat.toBytesBE (itemPayloadCount head) := by
  have hdd : bs.drop (off + 1) = (bs.drop off).drop 1 := by
    rw [List.drop_drop]
  cases head with
  | bytes data =>
    simp only [isLongItem] at hlong
    have henc : encode (.bytes data)
        = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)]
            ++ Nat.toBytesBE data.length ++ data :=
      encodeBytes_long_of_length data hlong
    rw [hdd, hdrop, henc]
    simp only [itemLenOfLen, itemPayloadCount, List.cons_append,
      List.append_assoc, List.drop_succ_cons, List.drop_zero]
    exact List.take_left' rfl
  | list items =>
    simp only [isLongItem] at hlong
    have henc : encode (.list items)
        = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)
            :: (Nat.toBytesBE (encode.encodeItems items).length ++ encode.encodeItems items) :=
      encode_list_long items hlong
    rw [hdd, hdrop, henc]
    simp only [itemLenOfLen, itemPayloadCount, List.cons_append,
      List.append_assoc, List.drop_succ_cons, List.drop_zero]
    exact List.take_left' rfl

/-- **Unified stride-equivalence.** For any item whose encoding sits at byte
    offset `off` of the region, the body's per-item advance lands at
    `regionBase + ofNat (off + (encode item).length)`. -/
theorem encode_head_eq_itemNextPtrRegion (head : RLPItem) (rest : List Byte)
    (regionBase : Word) (off : Nat) (bs : List Byte)
    (hdrop : bs.drop off = encode head ++ rest)
    (hsize : itemPayloadCount head < 256 ^ 8) :
    itemNextPtrRegion ((encode head)[0]'(encode_nonempty head)) regionBase off bs
      = regionBase + BitVec.ofNat 64 (off + (encode head).length) := by
  rw [itemNextPtrRegion]
  rcases flat_or_long head with hflat | hlong
  · -- flat: bridge through `itemTotalLen`
    have key : itemPtrRegion ((encode head)[0]'(encode_nonempty head)) regionBase off
        + itemLenRegion ((encode head)[0]'(encode_nonempty head)) bs off
        = (regionBase + BitVec.ofNat 64 off)
            + itemTotalLen ((encode head)[0]'(encode_nonempty head)) := by
      rcases classifyPrefix_encode_head_flat head hflat with h | h | h <;>
        simp only [itemPtrRegion, itemLenRegion, itemTotalLen, h, se12_1] <;> bv_omega
    rw [key, encode_head_eq_itemTotalLen head hflat, region_ptr_add']
  · -- long: tie the read length bytes back to the encoding
    cases head with
    | bytes data =>
      simp only [isLongItem] at hlong
      have hsize' : data.length < 256 ^ 8 := by simpa [itemPayloadCount] using hsize
      have hle : (Nat.toBytesBE data.length).length ≤ 8 := Nat.toBytesBE_length_le data.length 8 hsize'
      -- the head byte classifies as `longBytes` (refute the `longList` disjunct)
      have hcls : classifyPrefix ((encode (.bytes data))[0]'(encode_nonempty _)) = .longBytes := by
        rcases classifyPrefix_encode_head_long (.bytes data) (by simp [isLongItem]; omega) hsize
          with h | h
        · exact h
        · exfalso
          have henc : encode (.bytes data)
              = [BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)]
                  ++ Nat.toBytesBE data.length ++ data :=
            encodeBytes_long_of_length data hlong
          have hb : (encode (.bytes data))[0]'(encode_nonempty _)
              = BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length) := by
            simp [henc]
          have htn : (BitVec.ofNat 8 (0xB7 + (Nat.toBytesBE data.length).length)).toNat
              = 0xB7 + (Nat.toBytesBE data.length).length := by
            rw [BitVec.toNat_ofNat, show (2:Nat)^8 = 256 from rfl, Nat.mod_eq_of_lt (by omega)]
          rw [hb, classifyPrefix_longList_iff, htn] at h; omega
      simp only [itemPtrRegion, itemLenRegion, hcls]
      rw [encode_long_lenOfLen_eq_bytes hlong hsize',
          long_lenBytes_in_region (.bytes data) rest bs off (by simp [isLongItem]; omega) hdrop,
          encode_long_lenBytes_read (.bytes data), region_ptr_add',
          encode_long_length_eq (.bytes data) (by simp [isLongItem]; omega)]
      have harg : (off + 1) + itemLenOfLen (.bytes data) + itemPayloadCount (.bytes data)
          = off + (1 + itemLenOfLen (.bytes data) + itemPayloadCount (.bytes data)) := by omega
      rw [harg]
    | list items =>
      simp only [isLongItem] at hlong
      have hsize' : (encode.encodeItems items).length < 256 ^ 8 := by
        simpa [itemPayloadCount] using hsize
      have hle : (Nat.toBytesBE (encode.encodeItems items).length).length ≤ 8 :=
        Nat.toBytesBE_length_le _ 8 hsize'
      have hcls : classifyPrefix ((encode (.list items))[0]'(encode_nonempty _)) = .longList := by
        rcases classifyPrefix_encode_head_long (.list items) (by simp [isLongItem]; omega) hsize
          with h | h
        · exfalso
          have henc := encode_list_long items hlong
          have hb : (encode (.list items))[0]'(encode_nonempty _)
              = BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length) := by
            simp [henc]
          have htn : (BitVec.ofNat 8 (0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length)).toNat
              = 0xF7 + (Nat.toBytesBE (encode.encodeItems items).length).length := by
            rw [BitVec.toNat_ofNat, show (2:Nat)^8 = 256 from rfl, Nat.mod_eq_of_lt (by omega)]
          rw [hb, classifyPrefix_longBytes_iff, htn] at h; omega
        · exact h
      simp only [itemPtrRegion, itemLenRegion, hcls]
      rw [encode_long_lenOfLen_eq_list hlong hsize',
          long_lenBytes_in_region (.list items) rest bs off (by simp [isLongItem]; omega) hdrop,
          encode_long_lenBytes_read (.list items), region_ptr_add',
          encode_long_length_eq (.list items) (by simp [isLongItem]; omega)]
      have harg : (off + 1) + itemLenOfLen (.list items) + itemPayloadCount (.list items)
          = off + (1 + itemLenOfLen (.list items) + itemPayloadCount (.list items)) := by omega
      rw [harg]

-- ============================================================================
-- Sanity
-- ============================================================================

-- A short byte-string item (flat): the stride lands at `base + ofNat (encode length)`.
example (regionBase : Word) :
    itemNextPtrRegion ((encode (.bytes [1, 2, 3]))[0]'(encode_nonempty _))
        regionBase 0 (encode (.bytes [1, 2, 3]))
      = regionBase + BitVec.ofNat 64 (0 + (encode (.bytes [1, 2, 3])).length) :=
  encode_head_eq_itemNextPtrRegion (.bytes [1, 2, 3]) [] regionBase 0
    (encode (.bytes [1, 2, 3])) (by simp) (by decide)

-- A 56-byte string (long): exercises the runtime-read length path.
example (regionBase : Word) :
    itemNextPtrRegion ((encode (.bytes (List.replicate 56 (0 : Byte))))[0]'(encode_nonempty _))
        regionBase 0 (encode (.bytes (List.replicate 56 (0 : Byte))))
      = regionBase
          + BitVec.ofNat 64 (0 + (encode (.bytes (List.replicate 56 (0 : Byte)))).length) :=
  encode_head_eq_itemNextPtrRegion (.bytes (List.replicate 56 (0 : Byte))) [] regionBase 0
    (encode (.bytes (List.replicate 56 (0 : Byte)))) (by simp) (by decide)

end EvmAsm.Rv64.RLP
