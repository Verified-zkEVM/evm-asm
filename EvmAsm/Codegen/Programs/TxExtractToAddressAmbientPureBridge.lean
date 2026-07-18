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

end EvmAsm.Codegen.TxExtractToAddressSpec
