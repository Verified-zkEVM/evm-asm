/-
  EvmAsm.Rv64.RLP.UnifiedLenLoop

  EL.3 / Phase 5 — the LENGTH-DRIVEN unified RV64 RLP list-decode loop closure +
  bridge. Induct over the items, applying the length-driven body
  (`unified_lenloop_body_spec_within`) per item; the loop runs until the data
  pointer `x13` reaches the invariant end pointer `x15 = endPtr`, decoding all
  items with no item count. The length-driven analog of the count-driven
  `unified_loop_spec_within`/`_n`/`unified_loop_bridge` (`UnifiedListLoop.lean`),
  with the guard/termination swapped from "counter hits 0" to "pointer hits endPtr".
  `endPtr = regionBase + ofNat (O + (encode.encodeItems items).length)` is a byte
  offset (operationally computable, unlike an item count), so this loop decodes
  arbitrary lists from `read_input` and descends into sub-lists (`NestedDescendOne`).
-/

import EvmAsm.Rv64.RLP.UnifiedLenLoopBody
import EvmAsm.Rv64.RLP.UnifiedListLoop
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- Distinct in-bounds byte offsets give distinct region addresses (no wraparound). -/
private theorem region_offset_ne (regionBase : Word) (a b : Nat)
    (hab : a ≠ b) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    regionBase + BitVec.ofNat 64 a ≠ regionBase + BitVec.ofNat 64 b := by
  bv_omega

/-- Bundled post for the whole length-driven list-loop: scratch `x5/x10/x11/x12/x14`
    abstracted to `regOwn`, `x13` rests at `endPtr` (the loop reached the payload
    end), `x15 = endPtr` (the invariant), byte region intact. -/
@[irreducible]
def unified_lenloop_post (regionBase : Word) (bs : List (BitVec 8)) (endPtr : Word) : Assertion :=
  regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
    (.x13 ↦ᵣ endPtr) ** regOwn .x14 ** (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs

theorem unified_lenloop_post_unfold (regionBase : Word) (bs : List (BitVec 8)) (endPtr : Word) :
    unified_lenloop_post regionBase bs endPtr =
    (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      (.x13 ↦ᵣ endPtr) ** regOwn .x14 ** (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs) := by
  delta unified_lenloop_post; rfl

/-- **Length-driven n-iteration closure.** Decoding a non-empty list of arbitrary
    RLP items from the region suffix at offset `O` runs the loop body once per
    item — `63 * items.length` steps — until `x13` reaches the end pointer
    `x15 = endPtr = regionBase + ofNat (O + len)`. No item count is used. -/
theorem unified_lenloop_spec_within
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : UnifiedDecoderH regionBase decoder_base joinPC dcr bs)
    (hback : (joinPC + 4) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back))) :
    ∀ (items : List RLPItem) (O : Nat) (btail : List Byte) (v5Old v10 v11Old v12Old v14Old : Word),
      items ≠ [] →
      bs.drop O = encode.encodeItems items ++ btail →
      (∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) →
      cpsTripleWithin (63 * items.length) lbase (joinPC + 8)
        ((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
            (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
            ((CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty))
        ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
         (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
         (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode.encodeItems items).length))) **
         bytesRegion regionBase bs)
        (unified_lenloop_post regionBase bs
          (regionBase + BitVec.ofNat 64 (O + (encode.encodeItems items).length))) := by
  intro items
  induction items with
  | nil => intro O btail v5Old v10 v11Old v12Old v14Old hne _ _; exact absurd rfl hne
  | cons head tail ih =>
    intro O btail v5Old v10 v11Old v12Old v14Old _ hdrop hwin
    have hsplit : bs.drop O = encode head ++ (encode.encodeItems tail ++ btail) := by
      rw [hdrop, show encode.encodeItems (head :: tail)
            = encode head ++ encode.encodeItems tail from rfl, List.append_assoc]
    have hO : O < bs.length := by
      have hlen : (bs.drop O).length
          = (encode head ++ (encode.encodeItems tail ++ btail)).length := by
        rw [hsplit]
      rw [List.length_drop, List.length_append] at hlen
      have := encode_nonempty head; omega
    have hbsO : bs[O]'hO = (encode head)[0]'(encode_nonempty head) := by
      have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
          = (encode head)[0]'(encode_nonempty head) :=
        (List.getElem_of_eq hsplit _).trans (List.getElem_append_left (encode_nonempty head))
      rw [← key]; simp
    have hsizeHead : itemPayloadCount head < 256 ^ 8 := by
      rcases flat_or_long head with hflat | hlong
      · have h55 : itemPayloadCount head ≤ 55 := by
          cases head with
          | bytes data => simpa [itemPayloadCount, isFlatItem] using hflat
          | list items => simpa [itemPayloadCount, isFlatItem] using hflat
        calc itemPayloadCount head ≤ 55 := h55
          _ < 256 ^ 8 := by norm_num
      · have h1 : itemPayloadCount head < (encode head).length := by
          rw [encode_long_length_eq head hlong]; omega
        have h2 : (encode head).length ≤ bs.length := by
          have hle : (encode head).length ≤ (bs.drop O).length := by
            rw [hsplit, List.length_append]; omega
          rw [List.length_drop] at hle; omega
        have h3 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
        omega
    have hnext : itemNextPtrRegion (bs[O]'hO) regionBase O bs
        = regionBase + BitVec.ofNat 64 (O + (encode head).length) := by
      rw [hbsO]
      exact encode_head_eq_itemNextPtrRegion head (encode.encodeItems tail ++ btail) regionBase O bs
        hsplit hsizeHead
    have hoverO : regionBase.toNat + O < 2 ^ 64 := by omega
    have hvalidO : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true := hwin O hO
    have hwinO : regionLongWindow regionBase bs O hO :=
      regionLongWindow_of_split regionBase bs head (encode.encodeItems tail ++ btail) O hO hbsO hsplit
        hsizeHead hwin
    -- the total length of these items is bounded (≤ bs.length, from the drop)
    have htot : O + (encode.encodeItems (head :: tail)).length ≤ bs.length := by
      have e : (bs.drop O).length = (encode.encodeItems (head :: tail) ++ btail).length := by
        rw [hdrop]
      rw [List.length_drop, List.length_append] at e; omega
    set endPtr := regionBase + BitVec.ofNat 64 (O + (encode.encodeItems (head :: tail)).length)
      with hep
    cases tail with
    | nil =>
      -- single item: after decoding, x13 = endPtr, so the BNE falls through.
      have hee : itemNextPtrRegion (bs[O]'hO) regionBase O bs = endPtr := by
        rw [hnext, hep]; congr 2; simp only [encode.encodeItems, List.append_nil]
      have body := unified_lenloop_body_spec_within regionBase v5Old v10 v11Old v12Old v14Old
        endPtr lbase joinPC decoder_base dcr back bs O halign hO hoverO hvalidO
        hdec_base (decoderH O hO v10 v11Old v12Old v14Old hwinO)
        hback hne_lj hne_lj4 hd_lbu_dec hd_dec_add hd_dec_bne
      have h_absurd : ∀ hp,
          unified_lenloop_body_post regionBase bs (bs[O]'hO) (itemResidue (bs[O]'hO))
            (itemLenRegion (bs[O]'hO) bs O) (itemX12Region (bs[O]'hO) bs O v12Old)
            (itemNextPtrRegion (bs[O]'hO) regionBase O bs) (itemX14 (bs[O]'hO) v14Old)
            endPtr (itemNextPtrRegion (bs[O]'hO) regionBase O bs ≠ endPtr) hp → False :=
        fun hp hpost => (unified_lenloop_body_post_pure hp hpost) hee
      have tri := cpsBranchWithin_ntakenPath body h_absurd
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) tri
      simp only [unified_lenloop_body_post_unfold] at hp
      rw [hee] at hp
      rw [unified_lenloop_post_unfold]
      exact sepConj_mono (regIs_implies_regOwn _)
        (sepConj_mono_right
          (sepConj_mono (regIs_implies_regOwn _)
            (sepConj_mono (regIs_implies_regOwn _)
              (sepConj_mono (regIs_implies_regOwn _)
                (sepConj_mono_right
                  (sepConj_mono (regIs_implies_regOwn _)
                    (sepConj_mono_right
                      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)))))))) h hp
    | cons h2 t2 =>
      have hdrop' : bs.drop (O + (encode head).length) = encode.encodeItems (h2 :: t2) ++ btail := by
        rw [← List.drop_drop, hsplit, List.drop_append_length]
      -- one-step unfold of the cons (avoid `simp` over-expanding recursively).
      have hsplit_len : (encode.encodeItems (head :: h2 :: t2)).length
          = (encode head).length + (encode.encodeItems (h2 :: t2)).length := by
        rw [show encode.encodeItems (head :: h2 :: t2)
              = encode head ++ encode.encodeItems (h2 :: t2) from rfl, List.length_append]
      have hpos : 0 < (encode.encodeItems (h2 :: t2)).length := by
        have := encode_nonempty h2
        rw [show encode.encodeItems (h2 :: t2) = encode h2 ++ encode.encodeItems t2 from rfl,
            List.length_append]; omega
      -- the next pointer is NOT the end pointer (a nonempty tail remains).
      have hne_end : itemNextPtrRegion (bs[O]'hO) regionBase O bs ≠ endPtr := by
        rw [hnext, hep, hsplit_len]
        rw [hsplit_len] at htot
        exact region_offset_ne regionBase _ _ (by omega) (by omega) (by omega)
      have body := unified_lenloop_body_spec_within regionBase v5Old v10 v11Old v12Old v14Old
        endPtr lbase joinPC decoder_base dcr back bs O halign hO hoverO hvalidO
        hdec_base (decoderH O hO v10 v11Old v12Old v14Old hwinO)
        hback hne_lj hne_lj4 hd_lbu_dec hd_dec_add hd_dec_bne
      have h_absurd : ∀ hp,
          unified_lenloop_body_post regionBase bs (bs[O]'hO) (itemResidue (bs[O]'hO))
            (itemLenRegion (bs[O]'hO) bs O) (itemX12Region (bs[O]'hO) bs O v12Old)
            (itemNextPtrRegion (bs[O]'hO) regionBase O bs) (itemX14 (bs[O]'hO) v14Old)
            endPtr (itemNextPtrRegion (bs[O]'hO) regionBase O bs = endPtr) hp → False :=
        fun hp hpost => hne_end (unified_lenloop_body_post_pure hp hpost)
      have tri1 := cpsBranchWithin_takenPath body h_absurd
      -- endPtr (for head::h2::t2) equals the tail's end pointer (offset arithmetic).
      have hep' : endPtr
          = regionBase + BitVec.ofNat 64
              ((O + (encode head).length) + (encode.encodeItems (h2 :: t2)).length) := by
        rw [hep]; congr 2; simp only [encode.encodeItems, List.length_append]; omega
      have tri1' : cpsTripleWithin 63 lbase lbase
          ((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
              (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
              ((CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty))
          ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
           (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
           (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs)
          ((.x5 ↦ᵣ (bs[O]'hO).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
           (.x10 ↦ᵣ itemResidue (bs[O]'hO)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hO) bs O) **
           (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode head).length))) **
           (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
           (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64
              ((O + (encode head).length) + (encode.encodeItems (h2 :: t2)).length))) **
           bytesRegion regionBase bs) := by
        refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) tri1
        simp only [unified_lenloop_body_post_unfold] at hp
        rw [hnext, hep'] at hp
        exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right h').1 hp').1))))))))) h hp
      have ihspec := ih (O + (encode head).length) btail ((bs[O]'hO).zeroExtend 64)
        (itemResidue (bs[O]'hO)) (itemLenRegion (bs[O]'hO) bs O)
        (itemX12Region (bs[O]'hO) bs O v12Old) (itemX14 (bs[O]'hO) v14Old)
        (by simp) hdrop' hwin
      have composed := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) tri1' ihspec
      rw [← hep'] at composed
      rw [show (63 * (head :: h2 :: t2).length) = 63 + 63 * (h2 :: t2).length from by
            simp only [List.length_cons]; ring]
      exact composed

/-- **Length-driven loop entry (offset 0).** Running the loop over the whole region
    decodes all `items` in `63 * items.length` steps; the end pointer is
    `regionBase + ofNat (encode.encodeItems items).length`. -/
theorem unified_lenloop_n_spec_within
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (items : List RLPItem) (v5Old v10 v11Old v12Old v14Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : UnifiedDecoderH regionBase decoder_base joinPC dcr (encode.encodeItems items))
    (hback : (joinPC + 4) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)))
    (hne : items ≠ [])
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (63 * items.length) lbase (joinPC + 8)
      ((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          ((CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length)) **
       bytesRegion regionBase (encode.encodeItems items))
      (unified_lenloop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length)) := by
  have h := unified_lenloop_spec_within regionBase lbase joinPC decoder_base dcr back
    (encode.encodeItems items) halign hover hdec_base decoderH hback
    hne_lj hne_lj4 hd_lbu_dec hd_dec_add hd_dec_bne
    items 0 [] v5Old v10 v11Old v12Old v14Old hne (by rw [List.drop_zero, List.append_nil]) hwin
  rw [show regionBase + BitVec.ofNat 64 0 = regionBase from by simp,
      show (0 : Nat) + (encode.encodeItems items).length
        = (encode.encodeItems items).length from Nat.zero_add _] at h
  exact h

/-- **Length-driven list-decode bridge.** The operational loop (left) decodes the
    region in `63 * items.length` steps; the pure decoder (right) recovers exactly
    `items`. -/
theorem unified_lenloop_bridge
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (items : List RLPItem) (v5Old v10 v11Old v12Old v14Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : UnifiedDecoderH regionBase decoder_base joinPC dcr (encode.encodeItems items))
    (hback : (joinPC + 4) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)))
    (hne : items ≠ [])
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode.encodeItems items).length < 256 ^ 8) :
    cpsTripleWithin (63 * items.length) lbase (joinPC + 8)
      ((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          ((CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length)) **
       bytesRegion regionBase (encode.encodeItems items))
      (unified_lenloop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length))
    ∧ decodeItems (2 * (encode.encodeItems items).length + 1) (encode.encodeItems items)
        = some (items, []) :=
  ⟨unified_lenloop_n_spec_within regionBase lbase joinPC decoder_base dcr back items
      v5Old v10 v11Old v12Old v14Old halign hover hdec_base decoderH hback
      hne_lj hne_lj4 hd_lbu_dec hd_dec_add hd_dec_bne hne hwin,
    (decode_encode_mutual (2 * (encode.encodeItems items).length + 1)).2 items hsize (by omega)⟩

end EvmAsm.Rv64.RLP
