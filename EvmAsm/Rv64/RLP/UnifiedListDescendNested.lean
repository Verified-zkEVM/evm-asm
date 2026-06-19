/-
  EvmAsm.Rv64.RLP.UnifiedListDescendNested

  EL.3 / Phase 5 — DEPTH-2 nested RLP list descent. A concrete RV64 program
  descends TWO levels: the outer list header (to its payload pointer), then the
  first sub-list item (itself a `.list`), fully decoding the inner list — and
  coincides with the pure nested `decode`. The recursive step toward the
  fixed-schema STF block/header/tx decoders.

  Layout (program base `base`; aligned `regionBase`, whole buffer `bs`):
      base       LBU x5,x13,0 ++ unified_decoder_prog   ; OUTER header
                 (base .. base+148)                      ;   x13 → outer payload ptr
      base+148   < inner descent at offset payloadOff >  ; decode the inner .list
                 (base+148 .. base+456)
      base+456   (exit)

  Composes `unified_list_header_descend` (outer, offset 0) with
  `unified_list_descend_concrete_bridge_at` (inner, at the outer payload offset):
  reading at an OFFSET into the single aligned region — never re-anchoring at the
  unaligned payload pointer — is what makes the two levels compose.
-/

import EvmAsm.Rv64.RLP.UnifiedListDescendConcrete

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

set_option maxRecDepth 8000 in
/-- **Concrete depth-2 RLP list descent.** For an outer list whose head is itself a
    list (`.list (.list innerItems :: rest)`) embedded at the front of the buffer
    `bs = encode (.list (.list innerItems :: rest)) ++ outerTail`, the program
    descends the outer header to its payload pointer (offset `payloadOff`), then
    descends the inner `.list innerItems` there — in `123 + 63 * innerItems.length`
    steps — coinciding with the pure nested `decode` (both the outer value and the
    inner sub-list). -/
theorem unified_list_descend_nested_bridge
    (base regionBase : Word) (innerItems rest : List RLPItem) (outerTail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat
      + (encode (.list (.list innerItems :: rest)) ++ outerTail).length < 2 ^ 64)
    (hwin : ∀ i, i < (encode (.list (.list innerItems :: rest)) ++ outerTail).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize_outer : (encode (.list (.list innerItems :: rest))).length < 256 ^ 8)
    (hsize_inner : (encode (.list innerItems)).length < 256 ^ 8)
    (hinner_ne : innerItems ≠ []) :
    ∃ payloadOff,
      cpsTripleWithin (61 + (62 + 63 * innerItems.length)) base (base + 456)
        (((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          ((((((CodeReq.singleton (base + 148) (.LBU .x5 .x13 0)).union
                (CodeReq.ofProg (base + 152) unified_decoder_prog)).union
                (CodeReq.singleton (base + 296) (.ADD .x15 .x13 .x11))).union
                ((((CodeReq.singleton (base + 300) (.LBU .x5 .x13 0)).union
                  (CodeReq.ofProg (base + 304) unified_decoder_prog)).union
                  (CodeReq.singleton (base + 448) (.ADD .x13 .x13 .x11))).union
                  ((CodeReq.singleton (base + 448 + 4) (.BNE .x13 .x15 (-152))).union
                    CodeReq.empty))))))
        ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
         (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) **
         bytesRegion regionBase (encode (.list (.list innerItems :: rest)) ++ outerTail))
        (unified_lenloop_post regionBase
          (encode (.list (.list innerItems :: rest)) ++ outerTail)
          (regionBase + BitVec.ofNat 64 (payloadOff + (encode (.list innerItems)).length)))
      ∧ (encode (.list (.list innerItems :: rest)) ++ outerTail).drop payloadOff
          = encode (.list innerItems) ++ (encode.encodeItems rest ++ outerTail)
      ∧ decode (encode (.list (.list innerItems :: rest)) ++ outerTail)
          = some (.list (.list innerItems :: rest), outerTail) := by
  set outerItems := (.list innerItems :: rest : List RLPItem) with houter
  set bs := encode (.list outerItems) ++ outerTail with hbsdef
  -- outer value sizes
  have hsize_outer' : (encode.encodeItems outerItems).length < 256 ^ 8 := by
    have hle : (encode.encodeItems outerItems).length ≤ (encode (.list outerItems)).length := by
      by_cases h : (encode.encodeItems outerItems).length ≤ 55
      · rw [encode_list_short outerItems h]; simp only [List.length_cons]; omega
      · rw [encode_list_long outerItems (by omega)]
        simp only [List.length_cons, List.length_append]; omega
    omega
  -- outer header window (offset 0)
  have hO0 : 0 < bs.length := by
    rw [hbsdef, List.length_append]; have := encode_nonempty (RLPItem.list outerItems); omega
  have hdrop0 : bs.drop 0 = encode (.list outerItems) ++ outerTail := by rw [List.drop_zero]
  have hbs_head : bs[0]'hO0 = (encode (.list outerItems))[0]'(encode_nonempty (RLPItem.list outerItems)) := by
    have key : (bs.drop 0)[0]'(by rw [List.length_drop]; omega)
        = (encode (.list outerItems))[0]'(encode_nonempty (RLPItem.list outerItems)) :=
      (List.getElem_of_eq hdrop0 _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  obtain ⟨payloadOff, hptr, hlen, hdpay⟩ :=
    list_item_payload_window outerItems outerTail regionBase 0 bs hdrop0 hsize_outer'
  rw [show ((encode (.list outerItems))[0]'(encode_nonempty (RLPItem.list outerItems)))
        = (bs[0]'hO0) from hbs_head.symm] at hptr hlen
  -- the outer payload is `encode (.list innerItems) ++ (encode.encodeItems rest ++ outerTail)`
  have hdrop_inner : bs.drop payloadOff
      = encode (.list innerItems) ++ (encode.encodeItems rest ++ outerTail) := by
    rw [hdpay, houter,
      show encode.encodeItems (.list innerItems :: rest)
        = encode (.list innerItems) ++ encode.encodeItems rest from rfl, List.append_assoc]
  refine ⟨payloadOff, ?_, hdrop_inner, ?_⟩
  · -- operational: outer header ⨾ inner descent
    have hwindow0 : regionLongWindow regionBase bs 0 hO0 :=
      regionLongWindow_of_split regionBase bs (.list outerItems) outerTail 0 hO0
        hbs_head hdrop0 (by simpa [itemPayloadCount] using hsize_outer') hwin
    have hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 0) = true := hwin 0 hO0
    have outer := unified_list_header_descend base regionBase bs 0 hO0
      v5Old v10 v11Old v12Old v14Old v15Old halign hover hvalid0 hwindow0
    rw [show regionBase + BitVec.ofNat 64 0 = regionBase from by simp, hptr] at outer
    have inner := (unified_list_descend_concrete_bridge_at (base + 148) regionBase innerItems bs
      payloadOff (encode.encodeItems rest ++ outerTail)
      ((bs[0]'hO0).zeroExtend 64) (itemResidue (bs[0]'hO0)) (itemLenRegion (bs[0]'hO0) bs 0)
      (itemX12Region (bs[0]'hO0) bs 0 v12Old) (itemX14 (bs[0]'hO0) v14Old) v15Old
      halign hover hwin hsize_inner hinner_ne hdrop_inner).1
    -- normalize the inner program's `(base+148)+k` addresses to `base+(148+k)` form
    rw [show base + 148 + 4 = base + 152 from by bv_omega,
        show base + 148 + 148 = base + 296 from by bv_omega,
        show base + 148 + 152 = base + 300 from by bv_omega,
        show base + 148 + 156 = base + 304 from by bv_omega,
        show base + 148 + 300 = base + 448 from by bv_omega,
        show base + 148 + 308 = base + 456 from by bv_omega] at inner
    -- disjointness: outer header code ⊥ inner descent code (non-overlapping ranges)
    have dcr_none4 : ∀ (a : Word),
        (∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)) →
        CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
      fun a h => CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
        unified_decoder_prog_length h
    have dcr_none_i152 : ∀ (a : Word),
        (∀ k, k < 36 → a ≠ (base + 152) + BitVec.ofNat 64 (4 * k)) →
        CodeReq.ofProg (base + 152) unified_decoder_prog a = none :=
      fun a h => CodeReq.ofProg_none_range_len (base + 152) unified_decoder_prog 36 a
        unified_decoder_prog_length h
    have dcr_none_i304 : ∀ (a : Word),
        (∀ k, k < 36 → a ≠ (base + 304) + BitVec.ofNat 64 (4 * k)) →
        CodeReq.ofProg (base + 304) unified_decoder_prog a = none :=
      fun a h => CodeReq.ofProg_none_range_len (base + 304) unified_decoder_prog 36 a
        unified_decoder_prog_length h
    have hdisj :
        ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) unified_decoder_prog)).Disjoint
          ((((((CodeReq.singleton (base + 148) (.LBU .x5 .x13 0)).union
                (CodeReq.ofProg (base + 152) unified_decoder_prog)).union
                (CodeReq.singleton (base + 296) (.ADD .x15 .x13 .x11))).union
                ((((CodeReq.singleton (base + 300) (.LBU .x5 .x13 0)).union
                  (CodeReq.ofProg (base + 304) unified_decoder_prog)).union
                  (CodeReq.singleton (base + 448) (.ADD .x13 .x13 .x11))).union
                  ((CodeReq.singleton (base + 448 + 4) (.BNE .x13 .x15 (-152))).union
                    CodeReq.empty))))) :=
      CodeReq.Disjoint.union_left
        -- LBU @ base  ⊥  inner CR
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.singleton (by bv_omega))
              (CodeReq.Disjoint.singleton_ofProg (dcr_none_i152 base (by intro k hk; bv_omega))))
            (CodeReq.Disjoint.singleton (by bv_omega)))
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.union_right
                (CodeReq.Disjoint.singleton (by bv_omega))
                (CodeReq.Disjoint.singleton_ofProg (dcr_none_i304 base (by intro k hk; bv_omega))))
              (CodeReq.Disjoint.singleton (by bv_omega)))
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.singleton (by bv_omega)) (CodeReq.Disjoint.empty_right _))))
        -- ofProg (base+4)  ⊥  inner CR
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 148) (by intro k hk; bv_omega)))
              (ofProg_disjoint_ofProg (base + 4) (base + 152) _ _ 36 36
                unified_decoder_prog_length unified_decoder_prog_length
                (by intro k1 hk1 k2 hk2; bv_omega)))
            (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 296) (by intro k hk; bv_omega))))
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.union_right
                (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 300) (by intro k hk; bv_omega)))
                (ofProg_disjoint_ofProg (base + 4) (base + 304) _ _ 36 36
                  unified_decoder_prog_length unified_decoder_prog_length
                  (by intro k1 hk1 k2 hk2; bv_omega)))
              (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 448) (by intro k hk; bv_omega))))
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 448 + 4) (by intro k hk; bv_omega)))
              (CodeReq.Disjoint.empty_right _))))
    exact cpsTripleWithin_seq hdisj outer inner
  · -- pure: the outer value round-trips with its trailer
    exact decode_encode_append (.list outerItems) outerTail hsize_outer

-- Depth-2 cross-check: the program at `base = 0x1000` decodes the nested list
-- `[[0x01, 0x02], 0x03]` (`encode = [0xc4, 0xc2, 0x01, 0x02, 0x03]`) from `0x2000`,
-- descending the outer `0xc4` header to its payload, then the inner `0xc2` sub-list
-- → `[.bytes [1], .bytes [2]]`, in `123 + 63 * 2 = 249` steps.
example :=
  unified_list_descend_nested_bridge (0x1000 : Word) (0x2000 : Word)
    [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]] [.bytes [(0x03 : Byte)]] []
    0 0 0 0 0 0
    (by decide) (by decide)
    (by intro i hi
        have hlen : (encode (.list [.list [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]],
            .bytes [(0x03 : Byte)]]) ++ ([] : List Byte)).length = 5 := by decide
        rw [hlen] at hi; interval_cases i <;> decide)
    (by decide) (by decide) (by decide)

end EvmAsm.Rv64.RLP
