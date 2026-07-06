/-
  EvmAsm.Rv64.RLP.FlatListLoopBody

  EL.3 — the BODY (one iteration) of an RV64 RLP flat-item list-decode loop.

  Each iteration reads the current item's prefix byte from a multi-dword
  `bytesRegion` into `x5`, runs the flat reconverged single-item decoder
  (`rlp_decode_single_item_reconverged_flat`, passed as an opaque triple
  hypothesis), advances `x13` to the next item start (`x13 += x11`), decrements
  the item counter `x14`, and `BNE`s back to the loop top:

      loop_top:  LBU  x5, x13, 0          ; prefix bs[i] → x5
                 < flat decoder: lbase+4 .. joinPC >
      joinPC:    ADD  x13, x13, x11        ; x13 := next item start
                 ADDI x14, x14, -1         ; item counter -= 1
                 BNE  x14, x0, back        ; loop if counter ≠ 0

  Scope: flat items only (singleByte / shortBytes / shortList — no memory read
  for the length, so the only memory access is the prefix `LBU`). The decoder is
  an OPAQUE `cpsTripleWithin` hypothesis here; the n-iteration closure (a
  follow-up) discharges it by applying the flat decoder lemma per iteration and
  re-indexes the pointer by the `itemNextPtr` stride.
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItemReconverge
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- `bytesRegion` is PC-free — lets the `pcFree` tactic discharge frame
    side-conditions involving the region. -/
instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

-- ============================================================================
-- Per-item stride (next-item pointer)
-- ============================================================================

/-- Total bytes consumed by one flat item (the loop's per-iteration stride):
    `itemPayloadPtr pfx v13 + itemPayloadLen pfx = v13 + itemTotalLen pfx`. -/
def itemTotalLen (pfx : Byte) : Word :=
  match classifyPrefix pfx with
  | .singleByte => 1
  | .shortBytes => signExtend12 (1 : BitVec 12) + BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx)
  | .shortList  => signExtend12 (1 : BitVec 12) + BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx)
  | _ => 0

/-- The next item's start pointer after decoding the item at `v13`. -/
def itemNextPtr (pfx : Byte) (v13 : Word) : Word := v13 + itemTotalLen pfx

/-- For a flat prefix, advancing `x13` by the decoded payload length
    (`itemPayloadPtr + itemPayloadLen`) lands at `itemNextPtr` — the factored
    `v13 + stride` form a count-induction closure can re-index on. -/
theorem itemNextPtr_eq (pfx : Byte) (v13 : Word)
    (hflat : classifyPrefix pfx = .singleByte ∨ classifyPrefix pfx = .shortBytes
              ∨ classifyPrefix pfx = .shortList) :
    itemPayloadPtr pfx v13 + itemPayloadLen pfx = itemNextPtr pfx v13 := by
  rcases hflat with h | h | h <;>
    simp only [itemPayloadPtr, itemPayloadLen, itemTotalLen, itemNextPtr, h] <;> bv_omega

-- ============================================================================
-- Bundled post for either exit of the loop body
-- ============================================================================

@[irreducible]
def fll_body_post (regionBase : Word) (bs : List (BitVec 8)) (pfx : Byte)
    (v10New v11New nextPtr cnt' : Word) (P : Prop) : Assertion :=
  (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10New) **
    (.x11 ↦ᵣ v11New) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ cnt') **
    bytesRegion regionBase bs ** ⌜P⌝

theorem fll_body_post_unfold (regionBase : Word) (bs : List (BitVec 8)) (pfx : Byte)
    (v10New v11New nextPtr cnt' : Word) (P : Prop) :
    fll_body_post regionBase bs pfx v10New v11New nextPtr cnt' P =
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10New) **
      (.x11 ↦ᵣ v11New) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ cnt') **
      bytesRegion regionBase bs ** ⌜P⌝) := by
  delta fll_body_post; rfl

theorem fll_body_post_pure {regionBase : Word} {bs : List (BitVec 8)} {pfx : Byte}
    {v10New v11New nextPtr cnt' : Word} {P : Prop} :
    ∀ hp, fll_body_post regionBase bs pfx v10New v11New nextPtr cnt' P hp → P := by
  intro hp hpost
  simp only [fll_body_post_unfold] at hpost
  open EvmAsm.Rv64.Tactics in extract_pure hpost
  exact hpost.1

-- ============================================================================
-- Loop body spec (one iteration): a 2-exit cpsBranchWithin
-- ============================================================================

/-- Step-bounded spec for one pass through the flat list-loop body. The flat
    reconverged decoder is supplied as the opaque triple `decoder`
    (`decoder_base = lbase + 4`); the per-item stride is `itemNextPtr`. -/
theorem fll_body_spec_within
    (regionBase v5Old v10 v11Old cnt : Word)
    (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hflat : classifyPrefix (bs[i]'hi) = .singleByte
              ∨ classifyPrefix (bs[i]'hi) = .shortBytes
              ∨ classifyPrefix (bs[i]'hi) = .shortList)
    (hdec_base : decoder_base = lbase + 4)
    (decoder : cpsTripleWithin 11 decoder_base joinPC dcr
       ((.x5 ↦ᵣ (bs[i]'hi).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)))
       ((.x5 ↦ᵣ (bs[i]'hi).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ itemCascadeResidue (bs[i]'hi)) ** (.x11 ↦ᵣ itemPayloadLen (bs[i]'hi)) **
        (.x13 ↦ᵣ itemPayloadPtr (bs[i]'hi) (regionBase + BitVec.ofNat 64 i))))
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back))) :
    let cnt' := cnt + signExtend12 (-1 : BitVec 12)
    cpsBranchWithin 15 lbase
      (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1)))).union
          ((CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      lbase
        (fll_body_post regionBase bs (bs[i]'hi) (itemCascadeResidue (bs[i]'hi))
          (itemPayloadLen (bs[i]'hi)) (itemNextPtr (bs[i]'hi) (regionBase + BitVec.ofNat 64 i))
          cnt' (cnt' ≠ 0))
      (joinPC + 12)
        (fll_body_post regionBase bs (bs[i]'hi) (itemCascadeResidue (bs[i]'hi))
          (itemPayloadLen (bs[i]'hi)) (itemNextPtr (bs[i]'hi) (regionBase + BitVec.ofNat 64 i))
          cnt' (cnt' = 0)) := by
  intro cnt'
  set pfx := bs[i]'hi with hpfx
  simp only [fll_body_post_unfold]
  set bz := pfx.zeroExtend 64 with hbz
  -- Step 1: LBU x5, x13, 0 — load the prefix byte into x5.
  have lbu_raw := bytesRegion_lbu_within .x5 .x13 regionBase v5Old lbase bs i
    (by decide) halign hi hover hvalid
  have s_lbu : cpsTripleWithin 1 lbase (lbase + 4)
      (CodeReq.singleton lbase (.LBU .x5 .x13 0))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) ** (.x14 ↦ᵣ cnt))
        (by pcFree) lbu_raw)
  -- Step 2: the decoder (opaque), framed with x14 + bytesRegion (it touches neither).
  rw [hdec_base] at decoder
  have s_dec : cpsTripleWithin 11 (lbase + 4) joinPC dcr
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt) **
       bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemCascadeResidue pfx) **
       (.x11 ↦ᵣ itemPayloadLen pfx) ** (.x13 ↦ᵣ itemPayloadPtr pfx (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR ((.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs) (by pcFree) decoder)
  -- Step 3: ADD x13, x13, x11 — advance x13 to the next item start.
  have add_raw := add_spec_gen_rd_eq_rs1_within .x13 .x11
    (itemPayloadPtr pfx (regionBase + BitVec.ofNat 64 i)) (itemPayloadLen pfx) joinPC (by nofun)
  rw [itemNextPtr_eq pfx (regionBase + BitVec.ofNat 64 i) hflat] at add_raw
  have s_add : cpsTripleWithin 1 joinPC (joinPC + 4)
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemCascadeResidue pfx) **
       (.x11 ↦ᵣ itemPayloadLen pfx) ** (.x13 ↦ᵣ itemPayloadPtr pfx (regionBase + BitVec.ofNat 64 i)) **
       (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x14 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ bz) **
       (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
       (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemCascadeResidue pfx) **
         (.x14 ↦ᵣ cnt) ** bytesRegion regionBase bs) (by pcFree) add_raw)
  -- Step 4: ADDI x14, x14, -1 — decrement the item counter.
  have addi_raw := addi_spec_gen_same_within .x14 cnt (-1) (joinPC + 4) (by nofun)
  rw [show (joinPC + 4 : Word) + 4 = joinPC + 8 from by bv_omega] at addi_raw
  have s_addi : cpsTripleWithin 1 (joinPC + 4) (joinPC + 8)
      (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1)))
      ((.x14 ↦ᵣ cnt) ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ bz) **
       (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
       (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** bytesRegion regionBase bs)
      ((.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ bz) **
       (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
       (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemCascadeResidue pfx) **
         (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** bytesRegion regionBase bs)
        (by pcFree) addi_raw)
  -- Step 5: BNE x14, x0, back.
  have bne_raw := bne_spec_gen_within .x14 .x0 back cnt' (0 : Word) (joinPC + 8)
  have bne_framed : cpsBranchWithin 1 (joinPC + 8)
      (CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back))
      ((.x14 ↦ᵣ cnt') ** (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ bz) **
       (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
       (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** bytesRegion regionBase bs)
      lbase
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemCascadeResidue pfx) **
         (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt') **
         bytesRegion regionBase bs ** ⌜cnt' ≠ 0⌝)
      (joinPC + 12)
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemCascadeResidue pfx) **
         (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ cnt') **
         bytesRegion regionBase bs ** ⌜cnt' = 0⌝) := by
    have h_eq : (joinPC + 8 : Word) + 4 = joinPC + 12 := by bv_omega
    rw [h_eq, hback] at bne_raw
    exact cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x10 ↦ᵣ itemCascadeResidue pfx) ** (.x11 ↦ᵣ itemPayloadLen pfx) **
         (.x13 ↦ᵣ itemNextPtr pfx (regionBase + BitVec.ofNat 64 i)) ** bytesRegion regionBase bs)
        (by pcFree) bne_raw)
  -- Extend the BNE CR with a trailing empty (to match the seq output shape).
  have bne_ext : cpsBranchWithin 1 (joinPC + 8)
      ((CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty) _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  -- Disjointness for the union chain.
  have hd1 : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr := hd_lbu_dec
  have hd2 : ((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).Disjoint
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)) :=
    CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj)
      hd_dec_add
  have hd3 : (((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).Disjoint
      (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1))) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj4)
        hd_dec_addi)
      (CodeReq.Disjoint.singleton (by bv_omega))
  have hd4 : ((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
      (CodeReq.singleton (joinPC + 4) (.ADDI .x14 .x14 (-1)))).Disjoint
      ((CodeReq.singleton (joinPC + 8) (.BNE .x14 .x0 back)).union CodeReq.empty) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj8)
            hd_dec_bne)
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.empty_right _)
  -- Compose the chain.
  have t12 := cpsTripleWithin_seq hd1 s_lbu s_dec
  have t123 := cpsTripleWithin_seq hd2 t12 s_add
  have t1234 := cpsTripleWithin_seq hd3 t123 s_addi
  have composed := cpsTripleWithin_seq_cpsBranchWithin hd4 t1234 bne_ext
  exact composed

end EvmAsm.Rv64.RLP
