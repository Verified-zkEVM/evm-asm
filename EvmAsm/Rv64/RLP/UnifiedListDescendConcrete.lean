/-
  EvmAsm.Rv64.RLP.UnifiedListDescendConcrete

  EL.3 / Phase 5 — the fully CONCRETE top-level RLP list DESCENT. A real RV64
  program decodes a complete RLP list value `encode (.list items)` by descending
  through the list header into its payload, coinciding with the pure `decode`.
  This is the realistic top-level decode (the input IS a list value, e.g. a
  block). It composes three pieces:

      base        LBU  x5, x13, 0          ; load list prefix bs[0]
      base+4      < unified_decoder_prog : 36 instr >   → x13 = payloadPtr, x11 = payloadLen
      base+148    ADD  x15, x13, x11        ; x15 := endPtr = payloadPtr + payloadLen
      base+152    LBU  x5, x13, 0           ; length-driven loop (lbase = base+152)
      base+156    < unified_decoder_prog : 36 instr >   (loop decoder)
      base+300    ADD  x13, x13, x11        ; loop joinPC
      base+304    BNE  x13, x15, -152       ; loop back to base+152
      base+308    (exit)

  The descend-one-level window (`list_item_payload_window`) bridges the header
  output to the loop precondition: for a top-level list the window IS the payload
  `encode.encodeItems items`. The header is decoded by `unified_decoder_spec`; the
  end pointer is `ADD x15 x13 x11`; the payload by the length-driven loop.
-/

import EvmAsm.Rv64.RLP.NestedDescendOne
import EvmAsm.Rv64.RLP.UnifiedLenLoop
import EvmAsm.Rv64.RLP.UnifiedDecoderConcrete
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- `(regionBase + ofNat a) + ofNat b = regionBase + ofNat (a + b)`. -/
private theorem region_ptr_add (regionBase : Word) (a b : Nat) :
    (regionBase + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = regionBase + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]

/-- Two programs at non-overlapping address ranges have disjoint code requirements. -/
theorem ofProg_disjoint_ofProg (b1 b2 : Word) (p1 p2 : List Instr) (n1 n2 : Nat)
    (h1 : p1.length = n1) (h2 : p2.length = n2)
    (hsep : ∀ k1, k1 < n1 → ∀ k2, k2 < n2 →
      b1 + BitVec.ofNat 64 (4 * k1) ≠ b2 + BitVec.ofNat 64 (4 * k2)) :
    (CodeReq.ofProg b1 p1).Disjoint (CodeReq.ofProg b2 p2) := by
  intro a
  by_cases hin : ∀ k, k < n1 → a ≠ b1 + BitVec.ofNat 64 (4 * k)
  · exact Or.inl (CodeReq.ofProg_none_range_len b1 p1 n1 a h1 hin)
  · push Not at hin
    obtain ⟨k, hk, rfl⟩ := hin
    exact Or.inr (CodeReq.ofProg_none_range_len b2 p2 n2 _ h2
      (fun k2 hk2 => hsep k hk k2 hk2))

/-- **The payload loop, isolated.** The length-driven loop at `base + 152` decodes
    the payload `encode.encodeItems items` (the suffix `bs.drop payloadOff` of the
    full list encoding) in `63 * items.length` steps. Extracted into its own
    declaration so the (heavy) `unified_lenloop_spec_within` application elaborates
    in a clean local context — applying it inside the main descent theorem's large
    context provokes an unbounded `whnf`. The scratch registers `x5/x10/x11/x12/x14`
    are arbitrary (the loop only reads `x13`/`x15`). -/
private theorem descend_loop_triple
    (base regionBase : Word) (items : List RLPItem) (bs : List Byte) (tail : List Byte)
    (payloadOff : Nat) (v5' v10' v11' v12' v14' : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hitems_ne : items ≠ [])
    (hdpay : bs.drop payloadOff = encode.encodeItems items ++ tail) :
    cpsTripleWithin (63 * items.length) (base + 152) (base + 308)
      ((((CodeReq.singleton (base + 152) (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 156) unified_decoder_prog)).union
          (CodeReq.singleton (base + 300) (.ADD .x13 .x13 .x11))).union
          ((CodeReq.singleton (base + 300 + 4) (.BNE .x13 .x15 (-152))).union CodeReq.empty))
      ((.x5 ↦ᵣ v5') ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10') ** (.x11 ↦ᵣ v11') **
       (.x12 ↦ᵣ v12') ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 payloadOff)) ** (.x14 ↦ᵣ v14') **
       (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 (payloadOff + (encode.encodeItems items).length))) **
       bytesRegion regionBase bs)
      (unified_lenloop_post regionBase bs
        (regionBase + BitVec.ofNat 64 (payloadOff + (encode.encodeItems items).length))) := by
  have dcr_none_l : ∀ (a : Word),
      (∀ k, k < 36 → a ≠ (base + 156) + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg (base + 156) unified_decoder_prog a = none :=
    fun a h => CodeReq.ofProg_none_range_len (base + 156) unified_decoder_prog 36 a
      unified_decoder_prog_length h
  have decoderH_loop : UnifiedDecoderH regionBase (base + 156) (base + 300)
      (CodeReq.ofProg (base + 156) unified_decoder_prog) bs := by
    intro i hi v10'' v11'' v12'' v14'' hwindow
    have hd := unified_decoder_spec (base + 156) regionBase bs i hi
      v10'' v11'' v12'' v14'' halign hover hwindow
    rwa [show (base + 156) + 144 = base + 300 from by bv_omega] at hd
  have hback_loop : (base + 300 + 4) + signExtend13 (-152 : BitVec 13) = base + 152 := by
    have h152 : signExtend13 (-152 : BitVec 13) = (-152 : Word) := by decide
    rw [h152]; bv_omega
  have t_loop := unified_lenloop_spec_within regionBase (base + 152) (base + 300) (base + 156)
    (CodeReq.ofProg (base + 156) unified_decoder_prog) (-152) bs
    halign hover (by bv_omega) decoderH_loop hback_loop (by bv_omega) (by bv_omega)
    (CodeReq.Disjoint.singleton_ofProg (dcr_none_l (base + 152) (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none_l (base + 300) (by intro k hk; bv_omega)))
    (CodeReq.Disjoint.ofProg_singleton (dcr_none_l (base + 300 + 4) (by intro k hk; bv_omega)))
    items payloadOff tail v5' v10' v11' v12' v14'
    hitems_ne hdpay hwin
  rwa [show base + 300 + 8 = base + 308 from by bv_omega] at t_loop

set_option maxRecDepth 8000 in
/-- **Concrete RLP list descent (offset/buffer-general).** The program at `base`
    decodes the list value `encode (.list items)` sitting at byte offset `O` of the
    buffer `bs` (with `bs.drop O = encode (.list items) ++ tail`) — `x13` enters at
    `regionBase + ofNat O`, the header descends into the payload, and the
    length-driven loop runs to the sub-list boundary — in `62 + 63 * items.length`
    steps, coinciding with the pure `decode (bs.drop O) = some (.list items, tail)`.
    Reading at an OFFSET into the single dword-aligned `regionBase` (rather than
    re-anchoring at the unaligned payload pointer) is what makes nested descent
    composable. No abstract hypotheses remain. -/
theorem unified_list_descend_concrete_bridge_at
    (base regionBase : Word) (items : List RLPItem) (bs : List Byte) (O : Nat) (tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode (.list items)).length < 256 ^ 8)
    (hitems_ne : items ≠ [])
    (hdrop : bs.drop O = encode (.list items) ++ tail) :
    cpsTripleWithin (62 + 63 * items.length) base (base + 308)
      ((((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
            (CodeReq.singleton (base + 148) (.ADD .x15 .x13 .x11))).union
            ((((CodeReq.singleton (base + 152) (.LBU .x5 .x13 0)).union
              (CodeReq.ofProg (base + 156) unified_decoder_prog)).union
              (CodeReq.singleton (base + 300) (.ADD .x13 .x13 .x11))).union
              ((CodeReq.singleton (base + 300 + 4) (.BNE .x13 .x15 (-152))).union CodeReq.empty)))))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      (unified_lenloop_post regionBase bs
        (regionBase + BitVec.ofNat 64 (O + (encode (.list items)).length)))
    ∧ decode (bs.drop O) = some (.list items, tail) := by
  refine ⟨?_, by rw [hdrop]; exact decode_encode_append (.list items) tail hsize⟩
  -- `x13` points at byte offset `O`, which holds the list value's first byte.
  have hO : O < bs.length := by
    have h := congrArg List.length hdrop
    rw [List.length_drop, List.length_append] at h
    have := encode_nonempty (RLPItem.list items); omega
  -- the byte at offset `O` is the list value's first byte (the trailer is past it)
  have hbs_head : bs[O]'hO = (encode (.list items))[0]'(encode_nonempty (RLPItem.list items)) := by
    have key : (bs.drop O)[0]'(by rw [List.length_drop]; omega)
        = (encode (.list items))[0]'(encode_nonempty (RLPItem.list items)) :=
      (List.getElem_of_eq hdrop _).trans (List.getElem_append_left (encode_nonempty _))
    rw [← key]; simp
  set bz := (bs[O]'hO).zeroExtend 64 with hbz
  have hsize' : (encode.encodeItems items).length < 256 ^ 8 := by
    have hle : (encode.encodeItems items).length ≤ (encode (.list items)).length := by
      by_cases h : (encode.encodeItems items).length ≤ 55
      · rw [encode_list_short items h]; simp only [List.length_cons]; omega
      · rw [encode_list_long items (by omega)]
        simp only [List.length_cons, List.length_append]; omega
    omega
  -- the payload window at offset `O` (the trailer `tail` follows the list value)
  obtain ⟨payloadOff, hptr, hlen, hdpay⟩ :=
    list_item_payload_window items tail regionBase O bs hdrop hsize'
  -- align the getElem proof term with the buffer's `bs[O]`
  rw [show ((encode (.list items))[0]'(encode_nonempty (RLPItem.list items)))
        = (bs[O]'hO) from hbs_head.symm] at hptr hlen
  -- the header's region window obligation (head = .list items, rest = tail)
  have hwindow0 : regionLongWindow regionBase bs O hO :=
    regionLongWindow_of_split regionBase bs (.list items) tail O hO
      hbs_head hdrop (by simpa [itemPayloadCount] using hsize') hwin
  -- payloadOff + payloadLen = O + list-value length (the trailer cancels)
  have hpayne : 0 < (encode.encodeItems items).length := by
    cases items with
    | nil => exact absurd rfl hitems_ne
    | cons h t =>
      have := encode_nonempty h
      simp only [encode.encodeItems, List.length_append]; omega
  have hpoff_le :
      payloadOff + (encode.encodeItems items).length = O + (encode (.list items)).length := by
    have e1 := congrArg List.length hdpay
    have e2 := congrArg List.length hdrop
    simp only [List.length_drop, List.length_append] at e1 e2; omega
  have hover0 : regionBase.toNat + O < 2 ^ 64 := by omega
  have hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true := hwin O hO
  have dcr_none4 : ∀ (a : Word),
      (∀ k, k < 36 → a ≠ (base + 4) + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg (base + 4) unified_decoder_prog a = none :=
    fun a h => CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 a
      unified_decoder_prog_length h
  -- t_header : LBU x5,x13,0 ; unified_decoder_prog  (decode the list header)
  have lbu_raw := bytesRegion_lbu_within .x5 .x13 regionBase v5Old base
    bs O (by decide) halign hO hover0 hvalid0
  have s_lbu : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU .x5 .x13 0))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
         (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old))
        (by pcFree) lbu_raw)
  have dec_raw := unified_decoder_spec (base + 4) regionBase bs O hO
    v10 v11Old v12Old v14Old halign hover hwindow0
  rw [show (base + 4) + 144 = base + 148 from by bv_omega] at dec_raw
  have s_dec : cpsTripleWithin 60 (base + 4) (base + 148)
      (CodeReq.ofProg (base + 4) unified_decoder_prog)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0:Word)) **
       (.x10 ↦ᵣ itemResidue (bs[O]'hO)) **
       (.x11 ↦ᵣ itemLenRegion (bs[O]'hO) bs O) **
       (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
       (.x13 ↦ᵣ itemPtrRegion (bs[O]'hO) regionBase O) **
       (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x15 ↦ᵣ v15Old) (by pcFree) dec_raw)
  have t_header := cpsTripleWithin_seq
    (CodeReq.Disjoint.singleton_ofProg (dcr_none4 base (by intro k hk; bv_omega))) s_lbu s_dec
  -- t_add : ADD x15, x13, x11 — compute endPtr = payloadPtr + payloadLen
  have add_raw := add_spec_gen_within .x15 .x13 .x11
    (itemPtrRegion (bs[O]'hO) regionBase O)
    (itemLenRegion (bs[O]'hO) bs O)
    v15Old (base + 148) (by decide)
  rw [show (base + 148) + 4 = base + 152 from by bv_omega] at add_raw
  have s_add : cpsTripleWithin 1 (base + 148) (base + 152)
      (CodeReq.singleton (base + 148) (.ADD .x15 .x13 .x11))
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0:Word)) **
       (.x10 ↦ᵣ itemResidue (bs[O]'hO)) **
       (.x11 ↦ᵣ itemLenRegion (bs[O]'hO) bs O) **
       (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
       (.x13 ↦ᵣ itemPtrRegion (bs[O]'hO) regionBase O) **
       (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0:Word)) **
       (.x10 ↦ᵣ itemResidue (bs[O]'hO)) **
       (.x11 ↦ᵣ BitVec.ofNat 64 (encode.encodeItems items).length) **
       (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 payloadOff)) **
       (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
       (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 (payloadOff + (encode.encodeItems items).length))) **
       bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by rw [hptr, hlen, region_ptr_add] at hp; xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0:Word)) **
         (.x10 ↦ᵣ itemResidue (bs[O]'hO)) **
         (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
         (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
         bytesRegion regionBase bs)
        (by pcFree) add_raw)
  have t_ha := cpsTripleWithin_seq
    (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 148) (by intro k hk; bv_omega))))
    t_header s_add
  -- t_loop : the length-driven loop on the payload, at offset payloadOff
  have dcr_none_l : ∀ (a : Word),
      (∀ k, k < 36 → a ≠ (base + 156) + BitVec.ofNat 64 (4 * k)) →
      CodeReq.ofProg (base + 156) unified_decoder_prog a = none :=
    fun a h => CodeReq.ofProg_none_range_len (base + 156) unified_decoder_prog 36 a
      unified_decoder_prog_length h
  have t_loop := descend_loop_triple base regionBase items bs tail payloadOff bz
    (itemResidue (bs[O]'hO))
    (BitVec.ofNat 64 (encode.encodeItems items).length)
    (itemX12Region (bs[O]'hO) bs O v12Old)
    (itemX14 (bs[O]'hO) v14Old)
    halign hover hwin hitems_ne hdpay
  -- the header/ADD code is disjoint from the loop code (non-overlapping ranges)
  have hd_big :
      ((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
          (CodeReq.singleton (base + 148) (.ADD .x15 .x13 .x11)))).Disjoint
        ((((CodeReq.singleton (base + 152) (.LBU .x5 .x13 0)).union
          (CodeReq.ofProg (base + 156) unified_decoder_prog)).union
          (CodeReq.singleton (base + 300) (.ADD .x13 .x13 .x11))).union
          ((CodeReq.singleton (base + 300 + 4) (.BNE .x13 .x15 (-152))).union CodeReq.empty)) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left
        -- LBU @ base  ⊥  loop CR
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.singleton (by bv_omega))
              (CodeReq.Disjoint.singleton_ofProg (dcr_none_l base (by intro k hk; bv_omega))))
            (CodeReq.Disjoint.singleton (by bv_omega)))
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.singleton (by bv_omega)) (CodeReq.Disjoint.empty_right _)))
        -- ofProg (base+4)  ⊥  loop CR
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.union_right
              (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 152) (by intro k hk; bv_omega)))
              (ofProg_disjoint_ofProg (base + 4) (base + 156) _ _ 36 36
                unified_decoder_prog_length unified_decoder_prog_length
                (by intro k1 hk1 k2 hk2; bv_omega)))
            (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 300) (by intro k hk; bv_omega))))
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.ofProg_singleton (dcr_none4 (base + 300 + 4) (by intro k hk; bv_omega)))
            (CodeReq.Disjoint.empty_right _))))
      -- ADD @ base+148  ⊥  loop CR
      (CodeReq.Disjoint.union_right
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.union_right
            (CodeReq.Disjoint.singleton (by bv_omega))
            (CodeReq.Disjoint.singleton_ofProg (dcr_none_l (base + 148) (by intro k hk; bv_omega))))
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.union_right
          (CodeReq.Disjoint.singleton (by bv_omega)) (CodeReq.Disjoint.empty_right _)))
  have composed := cpsTripleWithin_seq hd_big t_ha t_loop
  rw [hpoff_le] at composed
  exact composed

/-- **Concrete RLP list descent (top-level/interior, `O = 0`).** The `O = 0`
    specialization of `unified_list_descend_concrete_bridge_at`: decode the list
    value at the FRONT of `encode (.list items) ++ tail`. -/
theorem unified_list_descend_concrete_bridge
    (base regionBase : Word) (items : List RLPItem) (tail : List Byte)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + (encode (.list items) ++ tail).length < 2 ^ 64)
    (hwin : ∀ i, i < (encode (.list items) ++ tail).length →
       isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode (.list items)).length < 256 ^ 8)
    (hitems_ne : items ≠ []) :
    cpsTripleWithin (62 + 63 * items.length) base (base + 308)
      ((((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
            (CodeReq.singleton (base + 148) (.ADD .x15 .x13 .x11))).union
            ((((CodeReq.singleton (base + 152) (.LBU .x5 .x13 0)).union
              (CodeReq.ofProg (base + 156) unified_decoder_prog)).union
              (CodeReq.singleton (base + 300) (.ADD .x13 .x13 .x11))).union
              ((CodeReq.singleton (base + 300 + 4) (.BNE .x13 .x15 (-152))).union CodeReq.empty)))))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old) **
       bytesRegion regionBase (encode (.list items) ++ tail))
      (unified_lenloop_post regionBase (encode (.list items) ++ tail)
        (regionBase + BitVec.ofNat 64 (encode (.list items)).length))
    ∧ decode (encode (.list items) ++ tail) = some (.list items, tail) := by
  have h := unified_list_descend_concrete_bridge_at base regionBase items
    (encode (.list items) ++ tail) 0 tail v5Old v10 v11Old v12Old v14Old v15Old
    halign hover hwin hsize hitems_ne (by rw [List.drop_zero])
  rw [show regionBase + BitVec.ofNat 64 0 = regionBase from by simp,
      show (0 : Nat) + (encode (.list items)).length = (encode (.list items)).length
        from Nat.zero_add _, List.drop_zero] at h
  exact h

/-- **List-header descent primitive.** `LBU x5,x13,0 ++ unified_decoder_prog` at
    `base` (61 steps, `base .. base+148`): from `x13 = regionBase + ofNat O` pointing
    at a `.list` value (whose region window `hwindow0` holds), it leaves `x13 =
    itemPtrRegion` (the payload pointer) and `x11 = itemLenRegion` (the payload
    length) — the reusable "descend one list level to its payload" step. Composed
    with `unified_list_descend_concrete_bridge_at` (at the payload offset) it gives
    nested descent; used directly by the STF schema decoders for each list level. -/
theorem unified_list_header_descend
    (base regionBase : Word) (bs : List Byte) (O : Nat) (hO : O < bs.length)
    (v5Old v10 v11Old v12Old v14Old v15Old : Word)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 O) = true)
    (hwindow0 : regionLongWindow regionBase bs O hO) :
    cpsTripleWithin 61 base (base + 148)
      ((CodeReq.singleton base (.LBU .x5 .x13 0)).union
        (CodeReq.ofProg (base + 4) unified_decoder_prog))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ (bs[O]'hO).zeroExtend 64) ** (.x0 ↦ᵣ (0:Word)) **
       (.x10 ↦ᵣ itemResidue (bs[O]'hO)) **
       (.x11 ↦ᵣ itemLenRegion (bs[O]'hO) bs O) **
       (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
       (.x13 ↦ᵣ itemPtrRegion (bs[O]'hO) regionBase O) **
       (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) := by
  have hover0 : regionBase.toNat + O < 2 ^ 64 := by omega
  have lbu_raw := bytesRegion_lbu_within .x5 .x13 regionBase v5Old base
    bs O (by decide) halign hO hover0 hvalid0
  have s_lbu : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU .x5 .x13 0))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ (bs[O]'hO).zeroExtend 64) ** (.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
         (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ v15Old))
        (by pcFree) lbu_raw)
  have dec_raw := unified_decoder_spec (base + 4) regionBase bs O hO
    v10 v11Old v12Old v14Old halign hover hwindow0
  rw [show (base + 4) + 144 = base + 148 from by bv_omega] at dec_raw
  have s_dec : cpsTripleWithin 60 (base + 4) (base + 148)
      (CodeReq.ofProg (base + 4) unified_decoder_prog)
      ((.x5 ↦ᵣ (bs[O]'hO).zeroExtend 64) ** (.x0 ↦ᵣ (0:Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ (bs[O]'hO).zeroExtend 64) ** (.x0 ↦ᵣ (0:Word)) **
       (.x10 ↦ᵣ itemResidue (bs[O]'hO)) **
       (.x11 ↦ᵣ itemLenRegion (bs[O]'hO) bs O) **
       (.x12 ↦ᵣ itemX12Region (bs[O]'hO) bs O v12Old) **
       (.x13 ↦ᵣ itemPtrRegion (bs[O]'hO) regionBase O) **
       (.x14 ↦ᵣ itemX14 (bs[O]'hO) v14Old) **
       (.x15 ↦ᵣ v15Old) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x15 ↦ᵣ v15Old) (by pcFree) dec_raw)
  exact cpsTripleWithin_seq
    (CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len (base + 4) unified_decoder_prog 36 base
        unified_decoder_prog_length (by intro k hk; bv_omega)))
    s_lbu s_dec

set_option maxRecDepth 8000 in
/-- **`regOwn`-re-entry descent (chainable).** The offset-general descent restated so
    its PRE is itself a `unified_lenloop_post` (at `O`) and its POST is the next
    `unified_lenloop_post` (at `O + (encode (.list items)).length`). A descent's post
    already abstracts the scratch registers to `regOwn` and leaves `x13`/`x15` at the
    next sibling, so this lets one descent feed DIRECTLY into the next (sequential
    sibling descent) with a syntactic `unified_lenloop_post` match. Derived from
    `…_bridge_at` by consuming the 5 owned scratch registers (`x5,x10,x11,x12,x14`)
    via `cpsTripleWithin_of_forall_regIs_to_regOwn`. -/
theorem unified_list_descend_concrete_bridge_at_regOwn
    (base regionBase : Word) (items : List RLPItem) (bs : List Byte) (O : Nat) (tail : List Byte)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < bs.length → isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hsize : (encode (.list items)).length < 256 ^ 8)
    (hitems_ne : items ≠ [])
    (hdrop : bs.drop O = encode (.list items) ++ tail) :
    cpsTripleWithin (62 + 63 * items.length) base (base + 308)
      ((((((CodeReq.singleton base (.LBU .x5 .x13 0)).union
            (CodeReq.ofProg (base + 4) unified_decoder_prog)).union
            (CodeReq.singleton (base + 148) (.ADD .x15 .x13 .x11))).union
            ((((CodeReq.singleton (base + 152) (.LBU .x5 .x13 0)).union
              (CodeReq.ofProg (base + 156) unified_decoder_prog)).union
              (CodeReq.singleton (base + 300) (.ADD .x13 .x13 .x11))).union
              ((CodeReq.singleton (base + 300 + 4) (.BNE .x13 .x15 (-152))).union CodeReq.empty)))))
      (unified_lenloop_post regionBase bs (regionBase + BitVec.ofNat 64 O))
      (unified_lenloop_post regionBase bs
        (regionBase + BitVec.ofNat 64 (O + (encode (.list items)).length))) := by
  rw [unified_lenloop_post_unfold]
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (.x0 ↦ᵣ (0:Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** bytesRegion regionBase bs **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x14)
      (fun v5 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
      (P := (.x0 ↦ᵣ (0:Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** bytesRegion regionBase bs **
        (.x5 ↦ᵣ v5) ** regOwn .x11 ** regOwn .x12 ** regOwn .x14)
      (fun v10 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x11)
      (P := (.x0 ↦ᵣ (0:Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** bytesRegion regionBase bs **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** regOwn .x12 ** regOwn .x14)
      (fun v11 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x12)
      (P := (.x0 ↦ᵣ (0:Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** bytesRegion regionBase bs **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** regOwn .x14)
      (fun v12 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x14)
      (P := (.x0 ↦ᵣ (0:Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) **
        (.x15 ↦ᵣ (regionBase + BitVec.ofNat 64 O)) ** bytesRegion regionBase bs **
        (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      (fun v14 => ?_))
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (unified_list_descend_concrete_bridge_at base regionBase items bs O tail
      v5 v10 v11 v12 v14 (regionBase + BitVec.ofNat 64 O)
      halign hover hwin hsize hitems_ne hdrop).1

-- Top-level cross-check (`tail = []`): the program at `base = 0x1000` decodes the
-- complete list value `[0x01, 0x02]` (`encode = [0xc2, 0x01, 0x02]`) from the region
-- at `0x2000`, descending the `0xc2` header into its 2-byte payload, in
-- `62 + 63 * 2 = 188` steps — pure `decode` recovers `(.list […], [])`.
example :=
  unified_list_descend_concrete_bridge (0x1000 : Word) (0x2000 : Word)
    [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]] [] 0 0 0 0 0 0
    (by decide) (by decide)
    (by intro i hi
        have hlen : (encode (.list
            [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]) ++ ([] : List Byte)).length = 3 := by
          decide
        rw [hlen] at hi; interval_cases i <;> decide)
    (by decide) (by decide)

-- Interior cross-check (`tail = [0xFF]`): the SAME list value embedded in a larger
-- buffer `[0xc2, 0x01, 0x02, 0xFF]` — the program descends the sub-list, stops at the
-- boundary leaving the `0xFF` sibling unread, and pure `decode` recovers
-- `(.list […], [0xFF])`.
example :=
  unified_list_descend_concrete_bridge (0x1000 : Word) (0x2000 : Word)
    [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]] [(0xFF : Byte)] 0 0 0 0 0 0
    (by decide) (by decide)
    (by intro i hi
        have hlen : (encode (.list
            [.bytes [(0x01 : Byte)], .bytes [(0x02 : Byte)]]) ++ [(0xFF : Byte)]).length = 4 := by
          decide
        rw [hlen] at hi; interval_cases i <;> decide)
    (by decide) (by decide)

-- Offset cross-check (`O = 2`): the list value `[0xc1, 0x01]` (`= encode (.list
-- [.bytes [1]])`) sits at byte offset 2 of the buffer `[0xFF, 0xFF, 0xc1, 0x01]`.
-- The descent reads at offset 2 of the single aligned region (NOT re-anchored) and
-- pure `decode ((…).drop 2)` recovers `(.list [.bytes [1]], [])`.
example :=
  unified_list_descend_concrete_bridge_at (0x1000 : Word) (0x2000 : Word)
    [.bytes [(0x01 : Byte)]] [(0xFF : Byte), (0xFF : Byte), (0xc1 : Byte), (0x01 : Byte)] 2 []
    0 0 0 0 0 0
    (by decide) (by decide)
    (by intro i hi
        have hlen : ([(0xFF : Byte), (0xFF : Byte), (0xc1 : Byte), (0x01 : Byte)]).length = 4 := by
          decide
        rw [hlen] at hi; interval_cases i <;> decide)
    (by decide) (by decide) (by decide)

end EvmAsm.Rv64.RLP
