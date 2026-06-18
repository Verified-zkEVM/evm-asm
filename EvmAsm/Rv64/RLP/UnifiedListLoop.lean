/-
  EvmAsm.Rv64.RLP.UnifiedListLoop

  EL.3 — the UNIFIED (all-class) RLP list-decode loop closure + bridge: the
  long-item-capable analog of the flat `fll_loop_*` (`FlatListLoop.lean`).

  `unified_loop_spec_within` is the n-iteration closure (structural induction
  over a list of arbitrary RLP items, threading the byte offset via
  `bs.drop O = encode.encodeItems items` and applying the all-class loop body
  `unified_body_spec_within` per item, with the 60-step region decoder supplied
  as a ∀-hypothesis `decoderH`); each iteration re-indexes `x13` via the unified
  stride-equivalence `encode_head_eq_itemNextPtrRegion`. `unified_loop_n_spec_within`
  is the offset-0 entry; `unified_loop_bridge` conjoins the operational loop with
  the pure `decodeItems` round-trip (`decode_encode_mutual.2`). Uniform
  `64 * items.length` steps; the per-item byte stride varies by class.

  Counter on `x15`; the region decoder clobbers `x10`/`x12`/`x14` (scratch).
-/

import EvmAsm.Rv64.RLP.UnifiedListLoopBody
import EvmAsm.Rv64.RLP.UnifiedItemStride
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral
import EvmAsm.EL.RLP.Properties

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

-- ============================================================================
-- N-iteration closure: decode a list of arbitrary RLP items
-- ============================================================================

/-- Bundled post for the whole unified list-loop: the scratch registers
    `x5/x10/x11/x12/x14` are abstracted to `regOwn`, the pointer rests at
    `endPtr`, the counter `x15` is zeroed, and the byte region is intact. -/
@[irreducible]
def unified_loop_post (regionBase : Word) (bs : List (BitVec 8)) (endPtr : Word) : Assertion :=
  regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
    (.x13 ↦ᵣ endPtr) ** regOwn .x14 ** (.x15 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs

theorem unified_loop_post_unfold (regionBase : Word) (bs : List (BitVec 8)) (endPtr : Word) :
    unified_loop_post regionBase bs endPtr =
    (regOwn .x5 ** (.x0 ↦ᵣ (0 : Word)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
      (.x13 ↦ᵣ endPtr) ** regOwn .x14 ** (.x15 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) := by
  delta unified_loop_post; rfl

/-- The item count never exceeds the encoded byte length (each item is
    non-empty). Bounds the loop counter for the `≠ 0` guard. -/
private theorem length_le_encodeItems : ∀ (items : List RLPItem),
    items.length ≤ (encode.encodeItems items).length
  | [] => by simp [encode.encodeItems]
  | i :: is => by
    simp only [encode.encodeItems, List.length_append, List.length_cons]
    have := encode_nonempty i
    have := length_le_encodeItems is
    omega

/-- The decoder hypothesis the loop closure carries: the 60-step region decoder
    for ANY byte index `i` and incoming scratch values — exactly the `decoder`
    field `unified_body_spec_within` consumes. -/
abbrev UnifiedDecoderH (regionBase decoder_base joinPC : Word) (dcr : CodeReq)
    (bs : List (BitVec 8)) : Prop :=
  ∀ (i : Nat) (hi : i < bs.length) (v10 v11 v12 v14 : Word),
    cpsTripleWithin 60 decoder_base joinPC dcr
      ((.x5 ↦ᵣ (bs[i]'hi).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ v14) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ (bs[i]'hi).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ itemResidue (bs[i]'hi)) ** (.x11 ↦ᵣ itemLenRegion (bs[i]'hi) bs i) **
       (.x12 ↦ᵣ itemX12Region (bs[i]'hi) bs i v12) **
       (.x13 ↦ᵣ itemPtrRegion (bs[i]'hi) regionBase i) **
       (.x14 ↦ᵣ itemX14 (bs[i]'hi) v14) ** bytesRegion regionBase bs)

/-- **N-iteration closure.** Decoding a non-empty list of arbitrary RLP items
    from the region suffix at offset `O` runs the loop body once per item — a
    uniform `64 * items.length` steps — advancing `x13` by the total encoded
    length and zeroing the counter. The single-item region decoder is supplied
    abstractly as `decoderH`; each iteration discharges the body's opaque decoder
    with it, and `encode_head_eq_itemNextPtrRegion` re-indexes the pointer. -/
theorem unified_loop_spec_within
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (bs : List (BitVec 8))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : UnifiedDecoderH regionBase decoder_base joinPC dcr bs)
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back))) :
    ∀ (items : List RLPItem) (O : Nat) (v5Old v10 v11Old v12Old v14Old : Word),
      items ≠ [] →
      bs.drop O = encode.encodeItems items →
      (∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) →
      cpsTripleWithin (64 * items.length) lbase (joinPC + 12)
        (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
            (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
            (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1)))).union
            ((CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty))
        ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
         (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
         (.x15 ↦ᵣ BitVec.ofNat 64 items.length) ** bytesRegion regionBase bs)
        (unified_loop_post regionBase bs
          (regionBase + BitVec.ofNat 64 (O + (encode.encodeItems items).length))) := by
  intro items
  induction items with
  | nil => intro O v5Old v10 v11Old v12Old v14Old hne _ _; exact absurd rfl hne
  | cons head tail ih =>
    intro O v5Old v10 v11Old v12Old v14Old _ hdrop hwin
    have hsplit : bs.drop O = encode head ++ encode.encodeItems tail := by
      rw [hdrop]; rfl
    have hO : O < bs.length := by
      have hlen : (bs.drop O).length = (encode head ++ encode.encodeItems tail).length := by
        rw [hsplit]
      rw [List.length_drop, List.length_append] at hlen
      have := encode_nonempty head; omega
    have hbsO : bs[O]'hO = (encode head)[0]'(encode_nonempty head) := by
      have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
          = (encode head)[0]'(encode_nonempty head) :=
        (List.getElem_of_eq hsplit _).trans (List.getElem_append_left (encode_nonempty head))
      rw [← key]; simp
    -- payload-count bound (needed by the stride lemma)
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
    -- the next-item pointer lands at offset `O + (encode head).length`
    have hnext : itemNextPtrRegion (bs[O]'hO) regionBase O bs
        = regionBase + BitVec.ofNat 64 (O + (encode head).length) := by
      rw [hbsO]; exact encode_head_eq_itemNextPtrRegion head tail regionBase O bs hsplit hsizeHead
    have hoverO : regionBase.toNat + O < 2 ^ 64 := by omega
    have hvalidO : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true := hwin O hO
    cases tail with
    | nil =>
      have body := unified_body_spec_within regionBase v5Old v10 v11Old v12Old v14Old
        (BitVec.ofNat 64 1) lbase joinPC decoder_base dcr back bs O halign hO hoverO hvalidO
        hdec_base (decoderH O hO v10 v11Old v12Old v14Old)
        hback hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add hd_dec_addi hd_dec_bne
      simp only [] at body
      rw [show (BitVec.ofNat 64 1 : Word) = BitVec.ofNat 64 (0 + 1) from rfl,
        word_ofNat_succ_dec 0] at body
      have h_absurd : ∀ hp,
          unified_body_post regionBase bs (bs[O]'hO) (itemResidue (bs[O]'hO))
            (itemLenRegion (bs[O]'hO) bs O) (itemX12Region (bs[O]'hO) bs O v12Old)
            (itemNextPtrRegion (bs[O]'hO) regionBase O bs) (itemX14 (bs[O]'hO) v14Old)
            (BitVec.ofNat 64 0) ((BitVec.ofNat 64 0 : Word) ≠ 0) hp → False :=
        fun hp hpost => (unified_body_post_pure hp hpost) (by decide)
      have tri := cpsBranchWithin_ntakenPath body h_absurd
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) tri
      simp only [unified_body_post_unfold] at hp
      rw [hnext] at hp
      rw [unified_loop_post_unfold,
        show (encode.encodeItems (head :: [])).length = (encode head).length from by
          simp only [encode.encodeItems, List.append_nil]]
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
      have hdrop' : bs.drop (O + (encode head).length) = encode.encodeItems (h2 :: t2) := by
        rw [← List.drop_drop, hsplit, List.drop_append_length]
      have hcnt_bound : t2.length + 1 < 18446744073709551616 := by
        have hcount := length_le_encodeItems (h2 :: t2)
        have e : (bs.drop (O + (encode head).length)).length
            = (encode.encodeItems (h2 :: t2)).length := by rw [hdrop']
        rw [List.length_drop] at e
        simp only [List.length_cons] at hcount
        omega
      have body := unified_body_spec_within regionBase v5Old v10 v11Old v12Old v14Old
        (BitVec.ofNat 64 ((h2 :: t2).length + 1)) lbase joinPC decoder_base dcr back bs O
        halign hO hoverO hvalidO hdec_base (decoderH O hO v10 v11Old v12Old v14Old)
        hback hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add hd_dec_addi hd_dec_bne
      simp only [] at body
      rw [word_ofNat_succ_dec (h2 :: t2).length] at body
      have hne_cnt : (BitVec.ofNat 64 (h2 :: t2).length : Word) ≠ 0 :=
        word_ofNat_succ_ne_zero t2.length hcnt_bound
      have h_absurd : ∀ hp,
          unified_body_post regionBase bs (bs[O]'hO) (itemResidue (bs[O]'hO))
            (itemLenRegion (bs[O]'hO) bs O) (itemX12Region (bs[O]'hO) bs O v12Old)
            (itemNextPtrRegion (bs[O]'hO) regionBase O bs) (itemX14 (bs[O]'hO) v14Old)
            (BitVec.ofNat 64 (h2 :: t2).length)
            ((BitVec.ofNat 64 (h2 :: t2).length : Word) = 0) hp → False :=
        fun hp hpost => absurd (unified_body_post_pure hp hpost) hne_cnt
      have tri1 := cpsBranchWithin_takenPath body h_absurd
      have tri1' : cpsTripleWithin 64 lbase lbase
          (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
              (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
              (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1)))).union
              ((CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty))
          ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
           (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
           (.x15 ↦ᵣ BitVec.ofNat 64 ((h2 :: t2).length + 1)) ** bytesRegion regionBase bs)
          ((.x5 ↦ᵣ (bs[O]'hO).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
           (.x10 ↦ᵣ itemResidue (bs[O]'hO)) ** (.x11 ↦ᵣ itemLenRegion (bs[O]'hO) bs O) **
           (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
           (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (O + (encode head).length))) **
           (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
           (.x15 ↦ᵣ BitVec.ofNat 64 (h2 :: t2).length) ** bytesRegion regionBase bs) := by
        refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => ?_) tri1
        simp only [unified_body_post_unfold] at hp
        rw [hnext] at hp
        exact (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right h').1 hp').1))))))))) h hp
      have ihspec := ih (O + (encode head).length) ((bs[O]'hO).zeroExtend 64)
        (itemResidue (bs[O]'hO)) (itemLenRegion (bs[O]'hO) bs O)
        (itemX12Region (bs[O]'hO) bs O v12Old) (itemX14 (bs[O]'hO) v14Old)
        (by simp) hdrop' hwin
      have composed := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) tri1' ihspec
      rw [show 64 * (head :: h2 :: t2).length = 64 + 64 * (h2 :: t2).length from by
            simp only [List.length_cons]; ring,
          show O + (encode.encodeItems (head :: h2 :: t2)).length
              = (O + (encode head).length) + (encode.encodeItems (h2 :: t2)).length from by
            simp only [encode.encodeItems, List.length_append]; omega]
      exact composed

/-- **Loop entry (offset 0).** Running the loop over the whole region decodes all
    `items` in `64 * items.length` steps, leaving the pointer at the region end. -/
theorem unified_loop_n_spec_within
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (items : List RLPItem) (v5Old v10 v11Old v12Old v14Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : UnifiedDecoderH regionBase decoder_base joinPC dcr (encode.encodeItems items))
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)))
    (hne : items ≠ [])
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin (64 * items.length) lbase (joinPC + 12)
      (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1)))).union
          ((CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ BitVec.ofNat 64 items.length) ** bytesRegion regionBase (encode.encodeItems items))
      (unified_loop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length)) := by
  have h := unified_loop_spec_within regionBase lbase joinPC decoder_base dcr back
    (encode.encodeItems items) halign hover hdec_base decoderH hback
    hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add hd_dec_addi hd_dec_bne
    items 0 v5Old v10 v11Old v12Old v14Old hne (by rw [List.drop_zero]) hwin
  rw [show regionBase + BitVec.ofNat 64 0 = regionBase from by simp,
      show (0 : Nat) + (encode.encodeItems items).length
        = (encode.encodeItems items).length from Nat.zero_add _] at h
  exact h

/-- **Unified list-decode bridge.** The operational loop (left) decodes the
    region in `64 * items.length` steps; the pure decoder (right) recovers exactly
    `items`, consuming the whole list. The two halves share the region contents
    `encode.encodeItems items`. -/
theorem unified_loop_bridge
    (regionBase : Word) (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (items : List RLPItem) (v5Old v10 v11Old v12Old v14Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode.encodeItems items).length < 2 ^ 64)
    (hdec_base : decoder_base = lbase + 4)
    (decoderH : UnifiedDecoderH regionBase decoder_base joinPC dcr (encode.encodeItems items))
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)))
    (hne : items ≠ [])
    (hwin : ∀ i, i < (encode.encodeItems items).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode.encodeItems items).length < 256 ^ 8) :
    cpsTripleWithin (64 * items.length) lbase (joinPC + 12)
      (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1)))).union
          ((CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ BitVec.ofNat 64 items.length) ** bytesRegion regionBase (encode.encodeItems items))
      (unified_loop_post regionBase (encode.encodeItems items)
        (regionBase + BitVec.ofNat 64 (encode.encodeItems items).length))
    ∧ decodeItems (2 * (encode.encodeItems items).length + 1) (encode.encodeItems items)
        = some (items, []) :=
  ⟨unified_loop_n_spec_within regionBase lbase joinPC decoder_base dcr back items
      v5Old v10 v11Old v12Old v14Old halign hover hdec_base decoderH hback
      hne_lj hne_lj4 hne_lj8 hd_lbu_dec hd_dec_add hd_dec_addi hd_dec_bne hne hwin,
    (decode_encode_mutual (2 * (encode.encodeItems items).length + 1)).2 items hsize (by omega)⟩

-- Cross-check the bridge's pure half on a concrete two-item list.
example :
    decodeItems (2 * (encode.encodeItems [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]).length + 1)
        (encode.encodeItems [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]])
      = some ([.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]], []) := by
  decide

end EvmAsm.Rv64.RLP
