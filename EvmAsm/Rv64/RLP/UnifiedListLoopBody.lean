/-
  EvmAsm.Rv64.RLP.UnifiedListLoopBody

  EL.3 — one iteration (BODY) of the UNIFIED RV64 RLP list-decode loop: decodes
  ANY item (all 5 classes) via the region all-class decoder, then advances. The
  long-capable analog of `fll_body_spec_within` (`FlatListLoopBody.lean`).

      loop_top (lbase):  LBU  x5, x13, 0          ; prefix bs[i] → x5
                         < region all-class decoder: lbase+4 .. joinPC, 60 steps >
      joinPC:            ADD  x13, x13, x11        ; x13 := payloadPtr + payloadLen
      (joinPC+4):        ADDI x15, x15, -1         ; item counter -= 1
      (joinPC+8):        BNE  x15, x0, back        ; loop if counter ≠ 0 (taken → lbase)

  The item counter is **x15** — the region decoder clobbers x14 (its length-read
  counter) and x12 (last length byte), so unlike the flat body (counter on x14)
  the loop's counter must live elsewhere; x10/x12/x14 are decoder scratch. The
  decoder is an OPAQUE `cpsTripleWithin 60` hypothesis (region-decoder-shaped,
  `decoder_base = lbase+4`); the concrete region decoder
  (`rlp_decode_single_item_reconverged_all_region`) discharges it in a later PR.
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItemReconvergeAllRegion
import EvmAsm.Rv64.RLP.FlatListLoopBody
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

/-- The next item's start pointer after decoding the item at byte offset `off`:
    the decoder leaves `x13 = itemPtrRegion` (payload pointer) and `x11 =
    itemLenRegion` (payload length); `ADD x13,x13,x11` lands here. -/
def itemNextPtrRegion (pfx : Byte) (regionBase : Word) (off : Nat) (bs : List Byte) : Word :=
  itemPtrRegion pfx regionBase off + itemLenRegion pfx bs off

-- ============================================================================
-- Bundled post for either exit of the unified loop body
-- ============================================================================

@[irreducible]
def unified_body_post (regionBase : Word) (bs : List (BitVec 8)) (pfx : Byte)
    (v10New v11New v12New nextPtr v14New cnt' : Word) (P : Prop) : Assertion :=
  (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10New) **
    (.x11 ↦ᵣ v11New) ** (.x12 ↦ᵣ v12New) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ v14New) **
    (.x15 ↦ᵣ cnt') ** bytesRegion regionBase bs ** ⌜P⌝

theorem unified_body_post_unfold (regionBase : Word) (bs : List (BitVec 8)) (pfx : Byte)
    (v10New v11New v12New nextPtr v14New cnt' : Word) (P : Prop) :
    unified_body_post regionBase bs pfx v10New v11New v12New nextPtr v14New cnt' P =
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10New) **
      (.x11 ↦ᵣ v11New) ** (.x12 ↦ᵣ v12New) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ v14New) **
      (.x15 ↦ᵣ cnt') ** bytesRegion regionBase bs ** ⌜P⌝) := by
  delta unified_body_post; rfl

theorem unified_body_post_pure {regionBase : Word} {bs : List (BitVec 8)} {pfx : Byte}
    {v10New v11New v12New nextPtr v14New cnt' : Word} {P : Prop} :
    ∀ hp, unified_body_post regionBase bs pfx v10New v11New v12New nextPtr v14New cnt' P hp → P := by
  intro hp hpost
  simp only [unified_body_post_unfold] at hpost
  open EvmAsm.Rv64.Tactics in extract_pure hpost
  exact hpost.1

-- ============================================================================
-- Unified loop body spec (one iteration): a 2-exit cpsBranchWithin
-- ============================================================================

/-- Step-bounded spec for one pass through the unified list-loop body. The region
    all-class decoder is supplied as the opaque triple `decoder`
    (`decoder_base = lbase + 4`, 60 steps); the per-item stride is
    `itemNextPtrRegion`; the item counter is `x15`. -/
theorem unified_body_spec_within
    (regionBase v5Old v10 v11Old v12Old v14Old cnt : Word)
    (lbase joinPC decoder_base : Word) (dcr : CodeReq) (back : BitVec 13)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 i) = true)
    (hdec_base : decoder_base = lbase + 4)
    (decoder : cpsTripleWithin 60 decoder_base joinPC dcr
       ((.x5 ↦ᵣ (bs[i]'hi).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
        (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
       ((.x5 ↦ᵣ (bs[i]'hi).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ itemResidue (bs[i]'hi)) ** (.x11 ↦ᵣ itemLenRegion (bs[i]'hi) bs i) **
        (.x12 ↦ᵣ itemX12Region (bs[i]'hi) bs i v12Old) **
        (.x13 ↦ᵣ itemPtrRegion (bs[i]'hi) regionBase i) **
        (.x14 ↦ᵣ itemX14 (bs[i]'hi) v14Old) ** bytesRegion regionBase bs))
    (hback : (joinPC + 8) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4) (hne_lj8 : lbase ≠ joinPC + 8)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_addi : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1))))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back))) :
    let cnt' := cnt + signExtend12 (-1 : BitVec 12)
    cpsBranchWithin 64 lbase
      (((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1)))).union
          ((CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      lbase
        (unified_body_post regionBase bs (bs[i]'hi) (itemResidue (bs[i]'hi))
          (itemLenRegion (bs[i]'hi) bs i) (itemX12Region (bs[i]'hi) bs i v12Old)
          (itemNextPtrRegion (bs[i]'hi) regionBase i bs) (itemX14 (bs[i]'hi) v14Old)
          cnt' (cnt' ≠ 0))
      (joinPC + 12)
        (unified_body_post regionBase bs (bs[i]'hi) (itemResidue (bs[i]'hi))
          (itemLenRegion (bs[i]'hi) bs i) (itemX12Region (bs[i]'hi) bs i v12Old)
          (itemNextPtrRegion (bs[i]'hi) regionBase i bs) (itemX14 (bs[i]'hi) v14Old)
          cnt' (cnt' = 0)) := by
  intro cnt'
  set pfx := bs[i]'hi with hpfx
  simp only [unified_body_post_unfold]
  set bz := pfx.zeroExtend 64 with hbz
  -- Step 1: LBU x5, x13, 0 — load the prefix byte into x5.
  have lbu_raw := bytesRegion_lbu_within .x5 .x13 regionBase v5Old lbase bs i
    (by decide) halign hi hover hvalid
  have s_lbu : cpsTripleWithin 1 lbase (lbase + 4)
      (CodeReq.singleton lbase (.LBU .x5 .x13 0))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
         (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ cnt))
        (by pcFree) lbu_raw)
  -- Step 2: the region decoder (opaque), framed with x15 (it touches neither x15 nor leaves bytesRegion).
  rw [hdec_base] at decoder
  have s_dec : cpsTripleWithin 60 (lbase + 4) joinPC dcr
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemPtrRegion pfx regionBase i) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x15 ↦ᵣ cnt) (by pcFree) decoder)
  -- Step 3: ADD x13, x13, x11 — advance x13 to the next item start.
  have add_raw := add_spec_gen_rd_eq_rs1_within .x13 .x11
    (itemPtrRegion pfx regionBase i) (itemLenRegion pfx bs i) joinPC (by nofun)
  have s_add : cpsTripleWithin 1 joinPC (joinPC + 4)
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemPtrRegion pfx regionBase i) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by simp only [itemNextPtrRegion]; xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs)
        (by pcFree) add_raw)
  -- Step 4: ADDI x15, x15, -1 — decrement the item counter.
  have addi_raw := addi_spec_gen_same_within .x15 cnt (-1) (joinPC + 4) (by nofun)
  rw [show (joinPC + 4 : Word) + 4 = joinPC + 8 from by bv_omega] at addi_raw
  have s_addi : cpsTripleWithin 1 (joinPC + 4) (joinPC + 8)
      (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1)))
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ cnt) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ cnt') ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
         (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         bytesRegion regionBase bs)
        (by pcFree) addi_raw)
  -- Step 5: BNE x15, x0, back.
  have bne_raw := bne_spec_gen_within .x15 .x0 back cnt' (0 : Word) (joinPC + 8)
  have bne_framed : cpsBranchWithin 1 (joinPC + 8)
      (CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back))
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ cnt') ** bytesRegion regionBase bs)
      lbase
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
         (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         (.x15 ↦ᵣ cnt') ** bytesRegion regionBase bs ** ⌜cnt' ≠ 0⌝)
      (joinPC + 12)
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
         (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         (.x15 ↦ᵣ cnt') ** bytesRegion regionBase bs ** ⌜cnt' = 0⌝) := by
    have h_eq : (joinPC + 8 : Word) + 4 = joinPC + 12 := by bv_omega
    rw [h_eq, hback] at bne_raw
    exact cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLenRegion pfx bs i) **
         (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
         (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         bytesRegion regionBase bs)
        (by pcFree) bne_raw)
  -- Extend the BNE CR with a trailing empty (to match the seq output shape).
  have bne_ext : cpsBranchWithin 1 (joinPC + 8)
      ((CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty) _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  -- Disjointness for the union chain.
  have hd1 : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr := hd_lbu_dec
  have hd2 : ((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).Disjoint
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)) :=
    CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj) hd_dec_add
  have hd3 : (((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).Disjoint
      (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1))) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj4) hd_dec_addi)
      (CodeReq.Disjoint.singleton (by bv_omega))
  have hd4 : ((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
      (CodeReq.singleton (joinPC + 4) (.ADDI .x15 .x15 (-1)))).Disjoint
      ((CodeReq.singleton (joinPC + 8) (.BNE .x15 .x0 back)).union CodeReq.empty) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left
          (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj8) hd_dec_bne)
          (CodeReq.Disjoint.singleton (by bv_omega)))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.empty_right _)
  -- Compose the chain.
  have t12 := cpsTripleWithin_seq hd1 s_lbu s_dec
  have t123 := cpsTripleWithin_seq hd2 t12 s_add
  have t1234 := cpsTripleWithin_seq hd3 t123 s_addi
  exact cpsTripleWithin_seq_cpsBranchWithin hd4 t1234 bne_ext

end EvmAsm.Rv64.RLP
