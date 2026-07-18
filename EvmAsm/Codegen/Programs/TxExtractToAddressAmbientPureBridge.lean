/-
  Pure bridges: slice-relative addresses ↔ ambient abs offsets.

  Includes short-form `rlpItemDecode` transfer (single / short-string / short-list).
  Long-form arms need drop/take room hyps — residual for long outer lists.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient
import EvmAsm.Codegen.Programs.TxExtractToAddressTopWalkInitShort

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen.TxTypeDispatchSpec

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

#print axioms shortWalkCursor_loadPtr_eq
#print axioms shortWalkEnd_loadPtr_eq
#print axioms txSlice_getElem?
#print axioms txSlice_drop
#print axioms txSlice_drop_take
#print axioms rlpItemDecode_txSlice_to_abs_short
#print axioms hnext_ambient_of_loadPtr

end EvmAsm.Codegen.TxExtractToAddressSpec
