/-
  Pure bridges: slice-relative addresses ↔ ambient abs offsets.

  Includes short-form `rlpItemDecode` transfer (single / short-string / short-list).
  Long-form arms need drop/take room hyps — residual for long outer lists.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.EL.RLP.Basic
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitLongAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressHonesty

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen.TxTypeDispatchSpec
open EvmAsm.Codegen.TxExtractToAddressHonesty
open EvmAsm.EL.RLP

theorem shortWalkCursor_loadPtr_eq
    (regionBase loadPtr : Word) (off listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan : regionBase.toNat + (off + listOff) < 2 ^ 64) :
    shortWalkCursor loadPtr listOff =
      shortWalkCursor regionBase (ambientAbsOff off listOff) := by
  simp only [shortWalkCursor, ambientAbsOff]
  have h := loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan
  rw [h]

theorem shortWalkEnd_loadPtr_eq
    (regionBase loadPtr listLen : Word) (off listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan : regionBase.toNat + (off + listOff) < 2 ^ 64) :
    shortWalkEnd loadPtr listLen listOff =
      shortWalkEnd regionBase listLen (ambientAbsOff off listOff) := by
  simp only [shortWalkEnd, ambientAbsOff]
  have h := loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan
  rw [h]

theorem txSlice_getElem?
    (bs : List (BitVec 8)) (off len k : Nat)
    (hbound : off + len ≤ bs.length) (hk : k < len) :
    (txSlice bs off len)[k]? = bs[off + k]? := by
  have hk' : k < (txSlice bs off len).length := by
    rw [txSlice_length bs off len hbound]; exact hk
  have habs : off + k < bs.length := by omega
  rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem habs,
    txSlice_getElem bs off len k hk hbound]

/-- Drop past a slice-relative index stays a prefix of the ambient drop. -/
theorem txSlice_drop
    (bs : List (BitVec 8)) (off len k : Nat) (_hk : k ≤ len) :
    (txSlice bs off len).drop k = (bs.drop (off + k)).take (len - k) := by
  simp only [txSlice]
  rw [List.drop_take, List.drop_drop]

/-- Long-form length payload: equal when room `k + n ≤ len` in the slice. -/
theorem txSlice_drop_take
    (bs : List (BitVec 8)) (off len k n : Nat)
    (hkn : k + n ≤ len) :
    ((txSlice bs off len).drop k).take n = (bs.drop (off + k)).take n := by
  have hk : k ≤ len := by omega
  rw [txSlice_drop bs off len k hk, List.take_take, Nat.min_eq_left (by omega)]

private theorem getElem?_some_lt {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  rw [List.getElem?_eq_some_iff] at h
  exact h.1

/-- Short-form slice→abs transfer: single / short-string / short-list only.
    Rejects long-string/list arms (caller gates via item encode ≤55). -/
theorem rlpItemDecode_txSlice_to_abs_short
    (bs : List (BitVec 8)) (off len rel : Nat)
    (cursor endPtr next lenW : Word)
    (hbound : off + len ≤ bs.length) (hrel : rel < len)
    (h : rlpItemDecode (txSlice bs off len) rel cursor endPtr next lenW)
    (hshort : ¬ (∃ b, (txSlice bs off len)[rel]? = some b ∧
      ((¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
          BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) ∨
        ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true))) :
    rlpItemDecode bs (ambientAbsOff off rel) cursor endPtr next lenW := by
  simp only [rlpItemDecode, ambientAbsOff] at h ⊢
  obtain ⟨b, hb, hrest⟩ := h
  have hb' : bs[off + rel]? = some b := by
    rw [← txSlice_getElem? bs off len rel hbound hrel]; exact hb
  refine ⟨b, hb', ?_⟩
  rcases hrest with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · -- short string
    rcases h2 with ⟨hu80, huB8, hcan, hfit, hnext, hlen⟩
    refine Or.inr (Or.inl ⟨hu80, huB8, ?_, hfit, hnext, hlen⟩)
    intro hlen1
    obtain ⟨c, hc, hcc⟩ := hcan hlen1
    have hrel1 : rel + 1 < len := by
      have := getElem?_some_lt hc
      rwa [txSlice_length bs off len hbound] at this
    refine ⟨c, ?_, hcc⟩
    have := txSlice_getElem? bs off len (rel + 1) hbound hrel1
    -- off + (rel + 1) = off + rel + 1
    simpa [Nat.add_assoc] using this.symm ▸ hc
  · -- long string — excluded by hshort
    exact False.elim (hshort ⟨b, hb, Or.inl ⟨h3.1, h3.2.1⟩⟩)
  · -- short list
    exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · -- long list — excluded by hshort
    exact False.elim (hshort ⟨b, hb, Or.inr h5.1⟩)

/-- Short-form abs→slice transfer. `hroom1` covers short-string canonicity byte. -/
theorem rlpItemDecode_abs_to_txSlice_short
    (bs : List (BitVec 8)) (off len rel : Nat)
    (cursor endPtr next lenW : Word)
    (hbound : off + len ≤ bs.length) (hrel : rel < len)
    (hroom1 : rel + 1 < len)
    (h : rlpItemDecode bs (ambientAbsOff off rel) cursor endPtr next lenW)
    (hshort : ¬ (∃ b, bs[off + rel]? = some b ∧
      ((¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
          BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) ∨
        ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true))) :
    rlpItemDecode (txSlice bs off len) rel cursor endPtr next lenW := by
  simp only [rlpItemDecode, ambientAbsOff] at h ⊢
  obtain ⟨b, hb, hrest⟩ := h
  have hb' : (txSlice bs off len)[rel]? = some b := by
    rw [txSlice_getElem? bs off len rel hbound hrel]; exact hb
  refine ⟨b, hb', ?_⟩
  rcases hrest with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · rcases h2 with ⟨hu80, huB8, hcan, hfit, hnext, hlen⟩
    refine Or.inr (Or.inl ⟨hu80, huB8, ?_, hfit, hnext, hlen⟩)
    intro hlen1
    obtain ⟨c, hc, hcc⟩ := hcan hlen1
    refine ⟨c, ?_, hcc⟩
    have hge := txSlice_getElem? bs off len (rel + 1) hbound hroom1
    have hc' : bs[off + (rel + 1)]? = some c := by simpa [Nat.add_assoc] using hc
    exact hge.symm ▸ hc'
  · exact False.elim (hshort ⟨b, hb, Or.inl ⟨h3.1, h3.2.1⟩⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact False.elim (hshort ⟨b, hb, Or.inr h5.1⟩)

/-- Lift decode-gated hnext: slice next equation → ambient abs next equation. -/
theorem hnext_ambient_of_loadPtr
    (regionBase loadPtr : Word) (off rel' : Nat)
    (next : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan : regionBase.toNat + (off + rel') < 2 ^ 64)
    (hnext : next = loadPtr + BitVec.ofNat 64 rel') :
    next = regionBase + BitVec.ofNat 64 (ambientAbsOff off rel') := by
  simp only [ambientAbsOff]
  rw [hnext, loadPtr_add_rel_eq regionBase loadPtr off rel' hptr hspan]

/-- Packaging hnext on loadPtr/txSlice lifts to regionBase/bs abs offsets (short forms). -/
theorem packaging_hnext_ambient
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len rel rel' : Nat)
    (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hrel : rel < len) (hroom1 : rel + 1 < len)
    (hspan_rel : regionBase.toNat + (off + rel) < 2 ^ 64)
    (hspan_rel' : regionBase.toNat + (off + rel') < 2 ^ 64)
    (hshort_abs : ¬ (∃ b, bs[off + rel]? = some b ∧
      ((¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
          BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) ∨
        ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true)))
    (hnext_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW →
      next = loadPtr + BitVec.ofNat 64 rel') :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off rel)
        (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW →
      next = regionBase + BitVec.ofNat 64 (ambientAbsOff off rel') := by
  intro next lenW hdec_abs
  have hcur :
      loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off rel hptr hspan_rel
  have hdec_sl :
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW := by
    rw [hcur]
    exact rlpItemDecode_abs_to_txSlice_short bs off len rel
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW
      hbound hrel hroom1 hdec_abs hshort_abs
  have hnext0 := hnext_sl next lenW hdec_sl
  exact hnext_ambient_of_loadPtr regionBase loadPtr off rel' next hptr hspan_rel' hnext0

/-- When slice.drop listOff = encode list (short), ambient drop has that encode as prefix. -/
theorem bs_drop_encode_prefix_of_txSlice
    (bs : List (BitVec 8)) (off len listOff : Nat)
    (enc : List (BitVec 8))
    (_hbound : off + len ≤ bs.length)
    (hlo : listOff ≤ len)
    (h : (txSlice bs off len).drop listOff = enc)
    (henc_le : enc.length ≤ len - listOff) :
    bs.drop (off + listOff) = enc ++ bs.drop (off + listOff + enc.length) := by
  have htake :
      (bs.drop (off + listOff)).take enc.length = enc := by
    have hdrop := txSlice_drop bs off len listOff hlo
    have hm : (bs.drop (off + listOff)).take (len - listOff) = enc := by
      rw [← hdrop, h]
    have hswap :
        (bs.drop (off + listOff)).take enc.length =
          ((bs.drop (off + listOff)).take (len - listOff)).take enc.length := by
      rw [List.take_take, Nat.min_eq_left henc_le]
    rw [hswap, hm, List.take_length]
  calc
    bs.drop (off + listOff)
        = (bs.drop (off + listOff)).take enc.length ++
            (bs.drop (off + listOff)).drop enc.length :=
          (List.take_append_drop enc.length _).symm
    _ = enc ++ (bs.drop (off + listOff)).drop enc.length := by rw [htake]
    _ = enc ++ bs.drop (off + listOff + enc.length) := by
          rw [List.drop_drop]

/-- Absolute offset in-bounds from relative field offset in slice. -/
theorem absOff_lt_bs
    (bs : List (BitVec 8)) (off len rel : Nat)
    (hbound : off + len ≤ bs.length) (hrel : rel < len) :
    ambientAbsOff off rel < bs.length := by
  simp only [ambientAbsOff]; omega

/-- Field head at shortListSrcOff is not a long-form RLP prefix (for packaging_hnext_ambient). -/
theorem hshort_abs_at_short_list_field
    (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < (txSlice bs off len).length) :
    ¬ (∃ b, bs[off + shortListSrcOff listOff items n]? = some b ∧
      ((¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
          BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) ∨
        ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true)) := by
  intro hEx
  obtain ⟨b, hb, hlong⟩ := hEx
  set slice := txSlice bs off len
  set rel := shortListSrcOff listOff items n
  have hrel : rel < len := by
    have hlen := txSlice_length bs off len hbound
    have : rel < slice.length := hoff
    rwa [hlen] at this
  have hbsl : slice[rel]? = some b := by
    rw [txSlice_getElem? bs off len rel hbound hrel]; exact hb
  have hhead := short_list_item_head_eq slice listOff items n henc hshort hn hoff
  have hle : (encode (items[n]'hn)).length ≤ 55 :=
    encode_item_length_le_55_of_short_list items n hn hshort
  have hpos := encode_item_length_pos (items[n]'hn)
  have hb0 : b = (encode (items[n]'hn))[0]'hpos := by
    have hget : slice[rel]'hoff = b := by
      rw [List.getElem?_eq_getElem hoff] at hbsl
      exact Option.some.inj hbsl
    rw [← hget, hhead]
  rcases hlong with hls | hll
  · have hnot := encode_item_head_not_long_string (items[n]'hn) hle
    exact hnot ⟨by simpa [hb0] using hls.1, by simpa [hb0] using hls.2⟩
  · have hlt := encode_item_head_lt_f8 (items[n]'hn) hle
    have : BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true := by simpa [hb0] using hlt
    exact hll this

/-- Packaging hnext for one short-list field: slice pure → ambient abs. -/
theorem packaging_hnext_ambient_field
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n n' : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan_rel : regionBase.toNat +
        (off + shortListSrcOff listOff items n) < 2 ^ 64)
    (hspan_rel' : regionBase.toNat +
        (off + shortListSrcOff listOff items n') < 2 ^ 64)
    (hroom1 : shortListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hnext_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (shortListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items n))
        endPtr next lenW →
      next = loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items n')) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (shortListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items n)))
        endPtr next lenW →
      next = regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items n')) := by
  let rel := shortListSrcOff listOff items n
  let rel' := shortListSrcOff listOff items n'
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_short_list_field bs off len listOff items n
      hbound henc hshort hn hoff
  exact packaging_hnext_ambient regionBase loadPtr bs off len rel rel' endPtr
    hptr hbound hrel hroom1' hspan_rel hspan_rel' hshort_abs hnext_sl

/-- Concrete getElem equality: slice[rel] = bs[off+rel]. -/
theorem txSlice_getElem_eq
    (bs : List (BitVec 8)) (off len k : Nat)
    (hbound : off + len ≤ bs.length) (hk : k < len)
    (hk_sl : k < (txSlice bs off len).length)
    (hk_bs : off + k < bs.length) :
    (txSlice bs off len)[k]'hk_sl = bs[off + k]'hk_bs := by
  have h := txSlice_getElem bs off len k hk hbound
  exact h

/-- Ambient hcur: short walk cursor at list header = regionBase+absOff0. -/
theorem hcur_ambient_short_srcOff0
    (regionBase loadPtr : Word) (off listOff : Nat) (items : List RLPItem)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan_list : regionBase.toNat + (off + listOff) < 2 ^ 64)
    (hspan_src0 : regionBase.toNat + (off + (listOff + 1)) < 2 ^ 64) :
    shortWalkCursor regionBase (ambientAbsOff off listOff) =
      regionBase + BitVec.ofNat 64
        (ambientAbsOff off (shortListSrcOff listOff items 0)) := by
  have hoverC : loadPtr.toNat + (listOff + 1) < 2 ^ 64 := by
    have hlp : loadPtr.toNat = regionBase.toNat + off := by
      have hoff : off < 2 ^ 64 := by omega
      rw [hptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff,
        Nat.mod_eq_of_lt (by omega : regionBase.toNat + off < 2 ^ 64)]
    omega
  have hcur_sl :
      shortWalkCursor loadPtr listOff =
        loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items 0) :=
    shortWalkCursor_eq_srcOff0 loadPtr listOff items hoverC
  have hcur_eq :=
    shortWalkCursor_loadPtr_eq regionBase loadPtr off listOff hptr hspan_list
  have hnext :=
    loadPtr_add_rel_eq regionBase loadPtr off (shortListSrcOff listOff items 0)
      hptr (by simp only [shortListSrcOff_zero]; exact hspan_src0)
  calc
    shortWalkCursor regionBase (ambientAbsOff off listOff)
        = shortWalkCursor loadPtr listOff := hcur_eq.symm
    _ = loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items 0) := hcur_sl
    _ = regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items 0)) := by
        simpa [ambientAbsOff] using hnext

/-- Ambient hinb at short-list end for field k. -/
theorem hinb_ambient_short_list_end
    (regionBase : Word) (off listOff : Nat) (items : List RLPItem) (k : Nat)
    (hn : k < items.length)
    (hoverEnd : regionBase.toNat +
        (off + (listOff + 1 + (encode.encodeItems items).length)) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr =
      regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + (encode.encodeItems items).length))) :
    BitVec.ult
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items k)))
        endPtr = true := by
  have hlt := encodeItemsPrefixLen_lt_total items k hn
  have hsrc : shortListSrcOff listOff items k =
      listOff + 1 + encodeItemsPrefixLen items k := rfl
  have hendN : endPtr.toNat =
      regionBase.toNat +
        (off + (listOff + 1 + (encode.encodeItems items).length)) := by
    rw [hend, ambientAbsOff, toNat_add_ofNat_lt regionBase _ hoverEnd]
  have hcurN :
      (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items k))).toNat =
        regionBase.toNat + ambientAbsOff off (shortListSrcOff listOff items k) := by
    have hover' : regionBase.toNat +
        ambientAbsOff off (shortListSrcOff listOff items k) < 2 ^ 64 := by
      simp only [ambientAbsOff, hsrc]; omega
    exact toNat_add_ofNat_lt regionBase _ hover'
  apply (BitVec.ult_iff_lt).mpr
  rw [BitVec.lt_def, hcurN, hendN]
  simp only [ambientAbsOff, hsrc]
  omega

/-- Ambient hss for one short-list field (room+hover+hvalid1). -/
theorem hss_ambient_of_short_list_field
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff_sl : shortListSrcOff listOff items n < (txSlice bs off len).length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hnext : n + 1 < items.length ∨ 2 ≤ (encode (items[n]'hn)).length)
    (hvalid1 : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (shortListSrcOff listOff items n) + 1)) = true)
    (hoff_bs : ambientAbsOff off (shortListSrcOff listOff items n) < bs.length) :
    ¬ BitVec.ult
        ((bs[ambientAbsOff off (shortListSrcOff listOff items n)]'hoff_bs
          ).zeroExtend 64)
        (0x80 : Word) = true →
      BitVec.ult
        ((bs[ambientAbsOff off (shortListSrcOff listOff items n)]'hoff_bs
          ).zeroExtend 64)
        (0xb8 : Word) = true →
      ambientAbsOff off (shortListSrcOff listOff items n) + 1 < bs.length ∧
        regionBase.toNat +
            (ambientAbsOff off (shortListSrcOff listOff items n) + 1) < 2 ^ 64 ∧
        isValidByteAccess
          (regionBase + BitVec.ofNat 64
            (ambientAbsOff off (shortListSrcOff listOff items n) + 1)) = true := by
  intro hlo hhi
  set slice := txSlice bs off len
  set rel := shortListSrcOff listOff items n
  set absOff := ambientAbsOff off rel
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < slice.length := hoff_sl
    rwa [hlen] at this
  have heq :
      bs[absOff]'hoff_bs = slice[rel]'hoff_sl := by
    simp only [absOff, ambientAbsOff]
    exact (txSlice_getElem_eq bs off len rel hbound hrel hoff_sl hoff_bs).symm
  have hlo_sl :
      ¬ BitVec.ult ((slice[rel]'hoff_sl).zeroExtend 64) (0x80 : Word) = true := by
    have hlo' := hlo
    rw [heq] at hlo'
    exact hlo'
  have hhi_sl :
      BitVec.ult ((slice[rel]'hoff_sl).zeroExtend 64) (0xb8 : Word) = true := by
    have hhi' := hhi
    rw [heq] at hhi'
    exact hhi'
  have hroom :=
    hss_room_of_short_string_ante slice listOff items n henc hshort hn hoff_sl
      hlo_sl hhi_sl hnext
  have hlp : loadPtr.toNat = regionBase.toNat + off := by
    have hoffN : off < 2 ^ 64 := by omega
    rw [hptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffN,
      Nat.mod_eq_of_lt (by omega : regionBase.toNat + off < 2 ^ 64)]
  have hover_sl : loadPtr.toNat + slice.length < 2 ^ 64 := by
    rw [hlen, hlp]; omega
  have hspan1 : regionBase.toNat + (off + (rel + 1)) < 2 ^ 64 := by
    have : rel + 1 < slice.length := hroom
    rw [hlen] at this; omega
  have heqAddr :
      loadPtr + BitVec.ofNat 64 (rel + 1) =
        regionBase + BitVec.ofNat 64 (absOff + 1) := by
    have h := loadPtr_add_rel_eq regionBase loadPtr off (rel + 1) hptr hspan1
    -- h: loadPtr + ofNat (rel+1) = regionBase + ofNat (off+(rel+1))
    -- absOff + 1 = off + rel + 1 = off + (rel + 1)
    have habs : absOff + 1 = off + (rel + 1) := by
      simp only [absOff, ambientAbsOff]; omega
    simpa [habs] using h
  have hvalid1_sl : isValidByteAccess
      (loadPtr + BitVec.ofNat 64 (rel + 1)) = true := by
    rwa [heqAddr]
  have hss_sl :=
    hss_of_short_list_item slice loadPtr listOff items n henc hshort hn hoff_sl
      hover_sl hnext hvalid1_sl
  have hss' := hss_sl hlo_sl hhi_sl
  refine ⟨?_, ?_, ?_⟩
  · have hr : rel + 1 < slice.length := hss'.1
    have hr' : rel + 1 < len := by rwa [hlen] at hr
    simp only [absOff, ambientAbsOff]
    omega
  · have hr : loadPtr.toNat + (rel + 1) < 2 ^ 64 := hss'.2.1
    simp only [absOff, ambientAbsOff, hlp] at hr ⊢
    omega
  · exact hvalid1

/-- Lift decode-gated hcre (len=0) from slice/loadPtr to ambient abs. -/
theorem hcre_ambient_of_slice
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + shortListSrcOff listOff items n) < 2 ^ 64)
    (hroom1 : shortListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hcre_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (shortListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items n))
        endPtr next lenW →
      lenW = (0 : Word)) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (shortListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items n)))
        endPtr next lenW →
      lenW = (0 : Word) := by
  intro next lenW hdec_abs
  set rel := shortListSrcOff listOff items n
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_short_list_field bs off len listOff items n
      hbound henc hshort hn hoff
  have hcur :
      loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off rel hptr hspan
  have hdec_sl :
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW := by
    rw [hcur]
    exact rlpItemDecode_abs_to_txSlice_short bs off len rel
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW
      hbound hrel hroom1' hdec_abs hshort_abs
  exact hcre_sl next lenW hdec_sl

/-- Lift slice hlen20 (len=20) to abs decode at regionBase (same transfer as hcre). -/
theorem hlen20_ambient_of_slice
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + shortListSrcOff listOff items n) < 2 ^ 64)
    (hroom1 : shortListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hlen20_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (shortListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items n))
        endPtr next lenW →
      lenW = (20 : Word)) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (shortListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items n)))
        endPtr next lenW →
      lenW = (20 : Word) := by
  intro next lenW hdec_abs
  set rel := shortListSrcOff listOff items n
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_short_list_field bs off len listOff items n
      hbound henc hshort hn hoff
  have hcur :
      loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off rel hptr hspan
  have hdec_sl :
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW := by
    rw [hcur]
    exact rlpItemDecode_abs_to_txSlice_short bs off len rel
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW
      hbound hrel hroom1' hdec_abs hshort_abs
  exact hlen20_sl next lenW hdec_sl

/-- Lift slice hnext_content (next = loadPtr+ofNat(8*q)+20) to abs
    next = regionBase+ofNat(8*q)+20 when 8*q is absolute dword index in bs. -/
theorem hnext_content_ambient_of_slice
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n q : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hshort : (encode.encodeItems items).length ≤ 55)
    (hn : n < items.length)
    (hoff : shortListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + shortListSrcOff listOff items n) < 2 ^ 64)
    (hroom1 : shortListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hq_abs : ambientAbsOff off (shortListSrcOff listOff items n) + 1 = 8 * q)
    (hcover : regionBase.toNat + 8 * q + 20 < 2 ^ 64)
    (hnext_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (shortListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items n))
        endPtr next lenW →
      next = loadPtr + BitVec.ofNat 64 (shortListSrcOff listOff items n) +
        (1 : Word) + (20 : Word)) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (shortListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (shortListSrcOff listOff items n)))
        endPtr next lenW →
      next = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word) := by
  intro next lenW hdec_abs
  set rel := shortListSrcOff listOff items n
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_short_list_field bs off len listOff items n
      hbound henc hshort hn hoff
  have hcur :
      loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off rel hptr hspan
  have hdec_sl :
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW := by
    rw [hcur]
    exact rlpItemDecode_abs_to_txSlice_short bs off len rel
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW
      hbound hrel hroom1' hdec_abs hshort_abs
  have hnext0 := hnext_sl next lenW hdec_sl
  -- next = ((loadPtr + ofNat rel) + 1) + 20
  -- loadPtr + ofNat rel = regionBase + ofNat absRel
  -- need regionBase + ofNat (8*q) + 20 with absRel+1 = 8*q
  have hspan_c : regionBase.toNat + ambientAbsOff off rel + 1 < 2 ^ 64 := by
    simp only [ambientAbsOff] at hq_abs hspan ⊢
    omega
  have hcontent :
      loadPtr + BitVec.ofNat 64 rel + (1 : Word) =
        regionBase + BitVec.ofNat 64 (8 * q) := by
    have hbase : loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := hcur
    -- (regionBase + ofNat abs) + 1 = regionBase + ofNat (abs+1) when non-wrap
    have habs1 : ambientAbsOff off rel + 1 = 8 * q := by
      simpa [ambientAbsOff] using hq_abs
    have hs : ambientAbsOff off rel < 2 ^ 64 := by
      simp only [ambientAbsOff]; omega
    have hs1 : ambientAbsOff off rel + 1 < 2 ^ 64 := by
      simp only [ambientAbsOff] at hq_abs; omega
    have h1 : BitVec.ofNat 64 (ambientAbsOff off rel) + (1 : Word) =
        BitVec.ofNat 64 (8 * q) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
        show (1 : Word).toNat = 1 by decide, Nat.mod_eq_of_lt hs1,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * q < 2 ^ 64), habs1]
    calc
      loadPtr + BitVec.ofNat 64 rel + (1 : Word)
          = (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) + (1 : Word) := by
            rw [hbase]
      _ = regionBase + (BitVec.ofNat 64 (ambientAbsOff off rel) + (1 : Word)) := by
            rw [BitVec.add_assoc]
      _ = regionBase + BitVec.ofNat 64 (8 * q) := by rw [h1]
  have _ := hcover
  have hnext1 : next =
      loadPtr + BitVec.ofNat 64 rel + (1 : Word) + (20 : Word) := by
    simpa [rel] using hnext0
  rw [hnext1, hcontent]

/-- Ambient walk-init byte guards from slice pure + getElem bridge. -/
theorem walk_init_ge_hi_ambient
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hoff_sl : listOff < (txSlice bs off len).length)
    (h_ge_sl : ¬ BitVec.ult
        (((txSlice bs off len)[listOff]'hoff_sl).zeroExtend 64)
        (0xc0 : Word) = true)
    (h_hi_sl : BitVec.ult
        (((txSlice bs off len)[listOff]'hoff_sl).zeroExtend 64)
        (0xf8 : Word) = true)
    (hoff_bs : ambientAbsOff off listOff < bs.length) :
    ¬ BitVec.ult ((bs[ambientAbsOff off listOff]'hoff_bs).zeroExtend 64)
        (0xc0 : Word) = true ∧
      BitVec.ult ((bs[ambientAbsOff off listOff]'hoff_bs).zeroExtend 64)
        (0xf8 : Word) = true := by
  have hlen := txSlice_length bs off len hbound
  have hrel : listOff < len := by rwa [hlen] at hoff_sl
  have heq :
      bs[ambientAbsOff off listOff]'hoff_bs =
        (txSlice bs off len)[listOff]'hoff_sl := by
    simp only [ambientAbsOff]
    exact (txSlice_getElem_eq bs off len listOff hbound hrel hoff_sl hoff_bs).symm
  refine ⟨?_, ?_⟩
  · have h := h_ge_sl
    rw [← heq] at h
    exact h
  · have h := h_hi_sl
    rw [← heq] at h
    exact h

/-- Ambient walk-init h_exact from slice pure + address bridge. -/
theorem walk_init_exact_ambient
    (regionBase loadPtr listLen : Word) (bs : List (BitVec 8))
    (off len listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hoff_sl : listOff < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + listOff) < 2 ^ 64)
    (h_exact_sl :
      (loadPtr + BitVec.ofNat 64 listOff) +
          ((((txSlice bs off len)[listOff]'hoff_sl).zeroExtend 64 - (0xc0 : Word)) +
            signExtend12 (1 : BitVec 12)) =
        (loadPtr + BitVec.ofNat 64 listOff) + listLen)
    (hoff_bs : ambientAbsOff off listOff < bs.length) :
    (regionBase + BitVec.ofNat 64 (ambientAbsOff off listOff)) +
        (((bs[ambientAbsOff off listOff]'hoff_bs).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off listOff)) + listLen := by
  have hlen := txSlice_length bs off len hbound
  have hrel : listOff < len := by rwa [hlen] at hoff_sl
  have heq :
      bs[ambientAbsOff off listOff]'hoff_bs =
        (txSlice bs off len)[listOff]'hoff_sl := by
    simp only [ambientAbsOff]
    exact (txSlice_getElem_eq bs off len listOff hbound hrel hoff_sl hoff_bs).symm
  have hcur :
      loadPtr + BitVec.ofNat 64 listOff =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off listOff) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan
  have h := h_exact_sl
  rw [← heq, hcur] at h
  exact h

/-- Bridge long walk end: loadPtr-relative = regionBase + abs. -/
theorem longWalkEnd_loadPtr_eq
    (regionBase loadPtr listLen : Word) (off listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hspan : regionBase.toNat + (off + listOff) < 2 ^ 64) :
    longWalkEndAmbient loadPtr listLen listOff =
      longWalkEndAmbient regionBase listLen (ambientAbsOff off listOff) := by
  simp only [longWalkEndAmbient, ambientAbsOff]
  have h := loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan
  rw [h]

/-- Bridge long walk cursor when list header byte is shared via getElem. -/
theorem longWalkCursor_loadPtr_eq
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (hoff_sl : listOff < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + listOff) < 2 ^ 64)
    (hoff_bs : ambientAbsOff off listOff < bs.length) :
    longWalkCursorAmbient loadPtr (txSlice bs off len) listOff hoff_sl =
      longWalkCursorAmbient regionBase bs (ambientAbsOff off listOff) hoff_bs := by
  have hlen := txSlice_length bs off len hbound
  have hrel : listOff < len := by rwa [hlen] at hoff_sl
  have heq :
      (txSlice bs off len)[listOff]'hoff_sl =
        bs[ambientAbsOff off listOff]'hoff_bs := by
    simpa [ambientAbsOff] using
      (txSlice_getElem_eq bs off len listOff hbound hrel hoff_sl hoff_bs)
  have hcur :
      loadPtr + BitVec.ofNat 64 listOff =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off listOff) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off listOff hptr hspan
  simp only [longWalkCursorAmbient]
  rw [hcur, heq]

theorem long_list_item_head_eq
    (txBytes : List (BitVec 8)) (listOff : Nat) (items : List RLPItem) (n : Nat)
    (henc : txBytes.drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : n < items.length)
    (hoff : longListSrcOff listOff items n < txBytes.length) :
    txBytes[longListSrcOff listOff items n]'hoff =
      (encode (items[n]'hn))[0]'(encode_item_length_pos _) := by
  set srcOff := longListSrcOff listOff items n
  have hdrop := long_list_item_drop txBytes listOff items n henc hlong hn
  have hpos : 0 < (encode (items[n]'hn)).length := encode_item_length_pos _
  have hcons : ∃ b rest, encode (items[n]'hn) = b :: rest := by
    match h : encode (items[n]'hn) with
    | [] => exact absurd h (List.ne_nil_of_length_pos hpos)
    | b :: rest => exact ⟨b, rest, rfl⟩
  obtain ⟨b, rest, heq⟩ := hcons
  have hdrop' :
      txBytes.drop srcOff =
        b :: (rest ++ encode.encodeItems (items.drop (n + 1))) := by
    simpa [srcOff, longListSrcOff, heq] using hdrop
  obtain ⟨_, hb'⟩ := getElem_of_drop_cons txBytes srcOff b _ hdrop'
  simpa [heq] using hb'

theorem hshort_abs_at_long_list_field
    (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : n < items.length)
    (hitemLe : (encode (items[n]'hn)).length ≤ 55)
    (hoff : longListSrcOff listOff items n < (txSlice bs off len).length) :
    ¬ (∃ b, bs[off + longListSrcOff listOff items n]? = some b ∧
      ((¬ BitVec.ult (b.zeroExtend 64) (0xb8 : Word) = true ∧
          BitVec.ult (b.zeroExtend 64) (0xc0 : Word) = true) ∨
        ¬ BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true)) := by
  intro hEx
  obtain ⟨b, hb, hlongForm⟩ := hEx
  set slice := txSlice bs off len
  set rel := longListSrcOff listOff items n
  have hrel : rel < len := by
    have hlen := txSlice_length bs off len hbound
    have : rel < slice.length := hoff
    rwa [hlen] at this
  have hbsl : slice[rel]? = some b := by
    rw [txSlice_getElem? bs off len rel hbound hrel]; exact hb
  have hhead := long_list_item_head_eq slice listOff items n henc hlong hn hoff
  have hpos := encode_item_length_pos (items[n]'hn)
  have hb0 : b = (encode (items[n]'hn))[0]'hpos := by
    have hget : slice[rel]'hoff = b := by
      rw [List.getElem?_eq_getElem hoff] at hbsl
      exact Option.some.inj hbsl
    rw [← hget, hhead]
  rcases hlongForm with hls | hll
  · have hnot := encode_item_head_not_long_string (items[n]'hn) hitemLe
    exact hnot ⟨by simpa [hb0] using hls.1, by simpa [hb0] using hls.2⟩
  · have hlt := encode_item_head_lt_f8 (items[n]'hn) hitemLe
    have : BitVec.ult (b.zeroExtend 64) (0xf8 : Word) = true := by simpa [hb0] using hlt
    exact hll this

theorem packaging_hnext_ambient_field_long
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n n' : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : n < items.length)
    (hitemLe : (encode (items[n]'hn)).length ≤ 55)
    (hoff : longListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan_rel : regionBase.toNat +
        (off + longListSrcOff listOff items n) < 2 ^ 64)
    (hspan_rel' : regionBase.toNat +
        (off + longListSrcOff listOff items n') < 2 ^ 64)
    (hroom1 : longListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hnext_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (longListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items n))
        endPtr next lenW →
      next = loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items n')) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (longListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items n)))
        endPtr next lenW →
      next = regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items n')) := by
  let rel := longListSrcOff listOff items n
  let rel' := longListSrcOff listOff items n'
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_long_list_field bs off len listOff items n
      hbound henc hlong hn hitemLe hoff
  exact packaging_hnext_ambient regionBase loadPtr bs off len rel rel' endPtr
    hptr hbound hrel hroom1' hspan_rel hspan_rel' hshort_abs hnext_sl

theorem hcre_ambient_of_slice_long
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : n < items.length)
    (hitemLe : (encode (items[n]'hn)).length ≤ 55)
    (hoff : longListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + longListSrcOff listOff items n) < 2 ^ 64)
    (hroom1 : longListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hcre_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (longListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items n))
        endPtr next lenW →
      lenW = (0 : Word)) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (longListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items n)))
        endPtr next lenW →
      lenW = (0 : Word) := by
  intro next lenW hdec_abs
  set rel := longListSrcOff listOff items n
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_long_list_field bs off len listOff items n
      hbound henc hlong hn hitemLe hoff
  have hcur :
      loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off rel hptr hspan
  have hdec_sl :
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW := by
    rw [hcur]
    exact rlpItemDecode_abs_to_txSlice_short bs off len rel
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW
      hbound hrel hroom1' hdec_abs hshort_abs
  exact hcre_sl next lenW hdec_sl


/-- Long dual of `hlen20_ambient_of_slice` (outer long list; field short-encode). -/
theorem hlen20_ambient_of_slice_long
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : n < items.length)
    (hitemLe : (encode (items[n]'hn)).length ≤ 55)
    (hoff : longListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + longListSrcOff listOff items n) < 2 ^ 64)
    (hroom1 : longListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hlen20_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (longListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items n))
        endPtr next lenW →
      lenW = (20 : Word)) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (longListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items n)))
        endPtr next lenW →
      lenW = (20 : Word) := by
  intro next lenW hdec_abs
  set rel := longListSrcOff listOff items n
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_long_list_field bs off len listOff items n
      hbound henc hlong hn hitemLe hoff
  have hcur :
      loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off rel hptr hspan
  have hdec_sl :
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW := by
    rw [hcur]
    exact rlpItemDecode_abs_to_txSlice_short bs off len rel
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW
      hbound hrel hroom1' hdec_abs hshort_abs
  exact hlen20_sl next lenW hdec_sl

/-- Long dual of `hnext_content_ambient_of_slice`. -/
theorem hnext_content_ambient_of_slice_long
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n q : Nat) (endPtr : Word)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : n < items.length)
    (hitemLe : (encode (items[n]'hn)).length ≤ 55)
    (hoff : longListSrcOff listOff items n < (txSlice bs off len).length)
    (hspan : regionBase.toNat + (off + longListSrcOff listOff items n) < 2 ^ 64)
    (hroom1 : longListSrcOff listOff items n + 1 < (txSlice bs off len).length)
    (hq_abs : ambientAbsOff off (longListSrcOff listOff items n) + 1 = 8 * q)
    (hcover : regionBase.toNat + 8 * q + 20 < 2 ^ 64)
    (hnext_sl : ∀ (next lenW : Word),
      rlpItemDecode (txSlice bs off len) (longListSrcOff listOff items n)
        (loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items n))
        endPtr next lenW →
      next = loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items n) +
        (1 : Word) + (20 : Word)) :
    ∀ (next lenW : Word),
      rlpItemDecode bs (ambientAbsOff off (longListSrcOff listOff items n))
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items n)))
        endPtr next lenW →
      next = regionBase + BitVec.ofNat 64 (8 * q) + (20 : Word) := by
  intro next lenW hdec_abs
  set rel := longListSrcOff listOff items n
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < (txSlice bs off len).length := hoff
    rwa [hlen] at this
  have hroom1' : rel + 1 < len := by
    have : rel + 1 < (txSlice bs off len).length := hroom1
    rwa [hlen] at this
  have hshort_abs :=
    hshort_abs_at_long_list_field bs off len listOff items n
      hbound henc hlong hn hitemLe hoff
  have hcur :
      loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := by
    simpa [ambientAbsOff] using
      loadPtr_add_rel_eq regionBase loadPtr off rel hptr hspan
  have hdec_sl :
      rlpItemDecode (txSlice bs off len) rel
        (loadPtr + BitVec.ofNat 64 rel) endPtr next lenW := by
    rw [hcur]
    exact rlpItemDecode_abs_to_txSlice_short bs off len rel
      (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) endPtr next lenW
      hbound hrel hroom1' hdec_abs hshort_abs
  have hnext0 := hnext_sl next lenW hdec_sl
  have hspan_c : regionBase.toNat + ambientAbsOff off rel + 1 < 2 ^ 64 := by
    simp only [ambientAbsOff] at hq_abs hspan ⊢
    omega
  have hcontent :
      loadPtr + BitVec.ofNat 64 rel + (1 : Word) =
        regionBase + BitVec.ofNat 64 (8 * q) := by
    have hbase : loadPtr + BitVec.ofNat 64 rel =
        regionBase + BitVec.ofNat 64 (ambientAbsOff off rel) := hcur
    have habs1 : ambientAbsOff off rel + 1 = 8 * q := by
      simpa [ambientAbsOff] using hq_abs
    have hs : ambientAbsOff off rel < 2 ^ 64 := by
      simp only [ambientAbsOff]; omega
    have hs1 : ambientAbsOff off rel + 1 < 2 ^ 64 := by
      simp only [ambientAbsOff] at hq_abs; omega
    have h1 : BitVec.ofNat 64 (ambientAbsOff off rel) + (1 : Word) =
        BitVec.ofNat 64 (8 * q) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
        show (1 : Word).toNat = 1 by decide, Nat.mod_eq_of_lt hs1,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * q < 2 ^ 64), habs1]
    calc
      loadPtr + BitVec.ofNat 64 rel + (1 : Word)
          = (regionBase + BitVec.ofNat 64 (ambientAbsOff off rel)) + (1 : Word) := by
            rw [hbase]
      _ = regionBase + (BitVec.ofNat 64 (ambientAbsOff off rel) + (1 : Word)) := by
            rw [BitVec.add_assoc]
      _ = regionBase + BitVec.ofNat 64 (8 * q) := by rw [h1]
  have _ := hcover
  have hnext1 : next =
      loadPtr + BitVec.ofNat 64 rel + (1 : Word) + (20 : Word) := by
    simpa [rel] using hnext0
  rw [hnext1, hcontent]

theorem hcur_ambient_long_srcOff0
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hencBound : (encode.encodeItems items).length < 256 ^ 8)
    (hoff_sl : listOff < (txSlice bs off len).length)
    (hoff_bs : ambientAbsOff off listOff < bs.length)
    (hspan_list : regionBase.toNat + (off + listOff) < 2 ^ 64)
    (hspan_src0 : regionBase.toNat +
        (off + (listOff + 1 + longListLol items)) < 2 ^ 64) :
    longWalkCursorAmbient regionBase bs (ambientAbsOff off listOff) hoff_bs =
      regionBase + BitVec.ofNat 64
        (ambientAbsOff off (longListSrcOff listOff items 0)) := by
  have hoverC : loadPtr.toNat + (listOff + 1 + longListLol items) < 2 ^ 64 := by
    have hlp : loadPtr.toNat = regionBase.toNat + off := by
      have hoffN : off < 2 ^ 64 := by omega
      rw [hptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffN,
        Nat.mod_eq_of_lt (by omega : regionBase.toNat + off < 2 ^ 64)]
    omega
  have hcur_sl :
      longWalkCursorAmbient loadPtr (txSlice bs off len) listOff hoff_sl =
        loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items 0) := by
    simpa [longWalkCursorAmbient] using
      longWalkCursor_eq_srcOff0 (txSlice bs off len) loadPtr listOff items
        henc hlong hencBound hoff_sl hoverC
  have hcur_eq :=
    longWalkCursor_loadPtr_eq regionBase loadPtr bs off len listOff
      hptr hbound hoff_sl hspan_list hoff_bs
  have hnext :=
    loadPtr_add_rel_eq regionBase loadPtr off (longListSrcOff listOff items 0)
      hptr (by simp only [longListSrcOff_zero]; exact hspan_src0)
  calc
    longWalkCursorAmbient regionBase bs (ambientAbsOff off listOff) hoff_bs
        = longWalkCursorAmbient loadPtr (txSlice bs off len) listOff hoff_sl :=
          hcur_eq.symm
    _ = loadPtr + BitVec.ofNat 64 (longListSrcOff listOff items 0) := hcur_sl
    _ = regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items 0)) := by
        simpa [ambientAbsOff] using hnext

theorem hinb_ambient_long_list_end
    (regionBase : Word) (off listOff : Nat) (items : List RLPItem) (k : Nat)
    (hn : k < items.length)
    (hoverEnd : regionBase.toNat +
        (off + (listOff + 1 + longListLol items +
          (encode.encodeItems items).length)) < 2 ^ 64)
    (endPtr : Word)
    (hend : endPtr =
      regionBase + BitVec.ofNat 64
        (ambientAbsOff off (listOff + 1 + longListLol items +
          (encode.encodeItems items).length))) :
    BitVec.ult
        (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items k)))
        endPtr = true := by
  have hlt := encodeItemsPrefixLen_lt_total items k hn
  have hsrc : longListSrcOff listOff items k =
      listOff + 1 + longListLol items + encodeItemsPrefixLen items k := rfl
  have hendN : endPtr.toNat =
      regionBase.toNat +
        (off + (listOff + 1 + longListLol items +
          (encode.encodeItems items).length)) := by
    rw [hend, ambientAbsOff, toNat_add_ofNat_lt regionBase _ hoverEnd]
  have hcurN :
      (regionBase + BitVec.ofNat 64
          (ambientAbsOff off (longListSrcOff listOff items k))).toNat =
        regionBase.toNat + ambientAbsOff off (longListSrcOff listOff items k) := by
    have hover' : regionBase.toNat +
        ambientAbsOff off (longListSrcOff listOff items k) < 2 ^ 64 := by
      simp only [ambientAbsOff, hsrc]; omega
    exact toNat_add_ofNat_lt regionBase _ hover'
  apply (BitVec.ult_iff_lt).mpr
  rw [BitVec.lt_def, hcurN, hendN]
  simp only [ambientAbsOff, hsrc]
  omega

theorem hss_ambient_of_long_list_field
    (regionBase loadPtr : Word) (bs : List (BitVec 8)) (off len listOff : Nat)
    (items : List RLPItem) (n : Nat)
    (hptr : loadPtr = regionBase + BitVec.ofNat 64 off)
    (hbound : off + len ≤ bs.length)
    (henc : (txSlice bs off len).drop listOff = encode (.list items))
    (hlong : 55 < (encode.encodeItems items).length)
    (hn : n < items.length)
    (hitemLe : (encode (items[n]'hn)).length ≤ 55)
    (hoff_sl : longListSrcOff listOff items n < (txSlice bs off len).length)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hnext : n + 1 < items.length ∨ 2 ≤ (encode (items[n]'hn)).length)
    (hvalid1 : isValidByteAccess
      (regionBase + BitVec.ofNat 64
        (ambientAbsOff off (longListSrcOff listOff items n) + 1)) = true)
    (hoff_bs : ambientAbsOff off (longListSrcOff listOff items n) < bs.length) :
    ¬ BitVec.ult
        ((bs[ambientAbsOff off (longListSrcOff listOff items n)]'hoff_bs
          ).zeroExtend 64)
        (0x80 : Word) = true →
      BitVec.ult
        ((bs[ambientAbsOff off (longListSrcOff listOff items n)]'hoff_bs
          ).zeroExtend 64)
        (0xb8 : Word) = true →
      ambientAbsOff off (longListSrcOff listOff items n) + 1 < bs.length ∧
        regionBase.toNat +
            (ambientAbsOff off (longListSrcOff listOff items n) + 1) < 2 ^ 64 ∧
        isValidByteAccess
          (regionBase + BitVec.ofNat 64
            (ambientAbsOff off (longListSrcOff listOff items n) + 1)) = true := by
  intro hlo hhi
  set slice := txSlice bs off len
  set rel := longListSrcOff listOff items n
  set absOff := ambientAbsOff off rel
  have hlen := txSlice_length bs off len hbound
  have hrel : rel < len := by
    have : rel < slice.length := hoff_sl
    rwa [hlen] at this
  have heq :
      bs[absOff]'hoff_bs = slice[rel]'hoff_sl := by
    simp only [absOff, ambientAbsOff]
    exact (txSlice_getElem_eq bs off len rel hbound hrel hoff_sl hoff_bs).symm
  have hlo_sl :
      ¬ BitVec.ult ((slice[rel]'hoff_sl).zeroExtend 64) (0x80 : Word) = true := by
    have hlo' := hlo
    rw [heq] at hlo'
    exact hlo'
  have hhi_sl :
      BitVec.ult ((slice[rel]'hoff_sl).zeroExtend 64) (0xb8 : Word) = true := by
    have hhi' := hhi
    rw [heq] at hhi'
    exact hhi'
  have hlp : loadPtr.toNat = regionBase.toNat + off := by
    have hoffN : off < 2 ^ 64 := by omega
    rw [hptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoffN,
      Nat.mod_eq_of_lt (by omega : regionBase.toNat + off < 2 ^ 64)]
  have hover_sl : loadPtr.toNat + slice.length < 2 ^ 64 := by
    rw [hlen, hlp]; omega
  have hspan1 : regionBase.toNat + (off + (rel + 1)) < 2 ^ 64 := by
    have hroom : rel + 1 < slice.length := by
      cases hnext with
      | inl hsucc =>
        have hlt := longListSrcOff_lt_length slice listOff items (n + 1)
          henc hlong hsucc
        have hs := longListSrcOff_succ listOff items n hn
        have hpos : 0 < (encode (items[n]'hn)).length := encode_item_length_pos _
        omega
      | inr hge2 =>
        have hdrop := long_list_item_drop slice listOff items n henc hlong hn
        have hlen_drop :
            (slice.drop rel).length =
              (encode (items[n]'hn)).length +
                (encode.encodeItems (items.drop (n + 1))).length := by
          have := congrArg List.length hdrop
          simpa [rel, longListSrcOff, List.length_append] using this
        have hdl : (slice.drop rel).length = slice.length - rel := by
          simp [List.length_drop]
        omega
    rw [hlen] at hroom; omega
  have heqAddr :
      loadPtr + BitVec.ofNat 64 (rel + 1) =
        regionBase + BitVec.ofNat 64 (absOff + 1) := by
    have h := loadPtr_add_rel_eq regionBase loadPtr off (rel + 1) hptr hspan1
    have habs : absOff + 1 = off + (rel + 1) := by
      simp only [absOff, ambientAbsOff]; omega
    simpa [habs] using h
  have hvalid1_sl : isValidByteAccess
      (loadPtr + BitVec.ofNat 64 (rel + 1)) = true := by
    rwa [heqAddr]
  have hss_sl :=
    hss_of_long_list_item slice loadPtr listOff items n henc hlong hn hitemLe
      hoff_sl hover_sl hnext hvalid1_sl
  have hss' := hss_sl hlo_sl hhi_sl
  refine ⟨?_, ?_, ?_⟩
  · have hr : rel + 1 < slice.length := hss'.1
    have hr' : rel + 1 < len := by rwa [hlen] at hr
    simp only [absOff, ambientAbsOff]
    omega
  · have hr : loadPtr.toNat + (rel + 1) < 2 ^ 64 := hss'.2.1
    simp only [absOff, ambientAbsOff, hlp] at hr ⊢
    omega
  · exact hvalid1

#print axioms shortWalkCursor_loadPtr_eq
#print axioms shortWalkEnd_loadPtr_eq
#print axioms txSlice_getElem?
#print axioms txSlice_drop
#print axioms txSlice_drop_take
#print axioms rlpItemDecode_txSlice_to_abs_short
#print axioms rlpItemDecode_abs_to_txSlice_short
#print axioms hnext_ambient_of_loadPtr
#print axioms packaging_hnext_ambient
#print axioms bs_drop_encode_prefix_of_txSlice
#print axioms absOff_lt_bs
#print axioms hshort_abs_at_short_list_field
#print axioms packaging_hnext_ambient_field
#print axioms txSlice_getElem_eq
#print axioms hcur_ambient_short_srcOff0
#print axioms hinb_ambient_short_list_end
#print axioms hss_ambient_of_short_list_field
#print axioms hcre_ambient_of_slice
#print axioms hlen20_ambient_of_slice
#print axioms hnext_content_ambient_of_slice
#print axioms walk_init_ge_hi_ambient
#print axioms walk_init_exact_ambient
#print axioms longWalkEnd_loadPtr_eq
#print axioms longWalkCursor_loadPtr_eq
#print axioms long_list_item_head_eq
#print axioms hshort_abs_at_long_list_field
#print axioms packaging_hnext_ambient_field_long
#print axioms hcre_ambient_of_slice_long
#print axioms hlen20_ambient_of_slice_long
#print axioms hnext_content_ambient_of_slice_long
#print axioms hcur_ambient_long_srcOff0
#print axioms hinb_ambient_long_list_end
#print axioms hss_ambient_of_long_list_field

end EvmAsm.Codegen.TxExtractToAddressSpec
