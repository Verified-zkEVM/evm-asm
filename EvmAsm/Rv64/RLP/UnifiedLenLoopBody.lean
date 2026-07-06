/-
  EvmAsm.Rv64.RLP.UnifiedLenLoopBody

  EL.3 / Phase 5 — one iteration (BODY) of the LENGTH-DRIVEN unified RV64 RLP
  list-decode loop. Unlike the count-driven body (`unified_body_spec_within`,
  `UnifiedListLoopBody.lean`), which decrements an item counter, this body stops
  when the data pointer reaches a precomputed END pointer held invariant in `x15`.
  This needs no item count (which the decoder cannot produce) and stops at the
  payload end regardless of trailing bytes — the foundation for nested decode,
  pairing with the descend-one-level window (`NestedDescendOne.lean`).

      loop_top (lbase):  LBU  x5, x13, 0          ; prefix bs[i] → x5
                         < region all-class decoder: lbase+4 .. joinPC, 60 steps >
      joinPC:            ADD  x13, x13, x11        ; x13 := payloadPtr + payloadLen
      (joinPC+4):        BNE  x13, x15, back       ; loop if x13 ≠ endPtr (taken → lbase)

  `x15` holds the loop-invariant end pointer `endPtr` (the decoder never touches
  x15, so it survives the 60-step decode framed); x10/x12/x14 are decoder scratch;
  `x11` holds the decoded length (consumed by `ADD`). The decoder is an OPAQUE
  `cpsTripleWithin 60` hypothesis (`decoder_base = lbase+4`), discharged by the
  concrete region decoder in a later PR. Analog of `unified_body_spec_within`.
-/

import EvmAsm.Rv64.RLP.UnifiedListLoopBody
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP

-- ============================================================================
-- Bundled post for either exit of the length-driven loop body
-- ============================================================================

/-- Bundled post for the length-driven body. Like `unified_body_post` but `x15`
    holds the loop-invariant end pointer `endPtr` (no decremented counter). -/
@[irreducible]
def unified_lenloop_body_post (regionBase : Word) (bs : List (BitVec 8)) (pfx : Byte)
    (v10New v11New v12New nextPtr v14New endPtr : Word) (P : Prop) : Assertion :=
  (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10New) **
    (.x11 ↦ᵣ v11New) ** (.x12 ↦ᵣ v12New) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ v14New) **
    (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs ** ⌜P⌝

theorem unified_lenloop_body_post_unfold (regionBase : Word) (bs : List (BitVec 8)) (pfx : Byte)
    (v10New v11New v12New nextPtr v14New endPtr : Word) (P : Prop) :
    unified_lenloop_body_post regionBase bs pfx v10New v11New v12New nextPtr v14New endPtr P =
    ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10New) **
      (.x11 ↦ᵣ v11New) ** (.x12 ↦ᵣ v12New) ** (.x13 ↦ᵣ nextPtr) ** (.x14 ↦ᵣ v14New) **
      (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs ** ⌜P⌝) := by
  delta unified_lenloop_body_post; rfl

theorem unified_lenloop_body_post_pure {regionBase : Word} {bs : List (BitVec 8)} {pfx : Byte}
    {v10New v11New v12New nextPtr v14New endPtr : Word} {P : Prop} :
    ∀ hp, unified_lenloop_body_post regionBase bs pfx v10New v11New v12New nextPtr v14New endPtr P hp
      → P := by
  intro hp hpost
  simp only [unified_lenloop_body_post_unfold] at hpost
  open EvmAsm.Rv64.Tactics in extract_pure hpost
  exact hpost.1

-- ============================================================================
-- Length-driven loop body spec (one iteration): a 2-exit cpsBranchWithin
-- ============================================================================

/-- Step-bounded spec for one pass through the length-driven list-loop body. The
    region all-class decoder is the opaque triple `decoder` (`decoder_base =
    lbase + 4`, 60 steps); the per-item stride is `itemNextPtrRegion`; the guard
    compares the advanced pointer `x13` to the invariant end pointer `x15 = endPtr`
    (`BNE x13 x15` → loop while not at the end). -/
theorem unified_lenloop_body_spec_within
    (regionBase v5Old v10 v11Old v12Old v14Old endPtr : Word)
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
    (hback : (joinPC + 4) + signExtend13 back = lbase)
    (hne_lj : lbase ≠ joinPC) (hne_lj4 : lbase ≠ joinPC + 4)
    (hd_lbu_dec : (CodeReq.singleton lbase (.LBU .x5 .x13 0)).Disjoint dcr)
    (hd_dec_add : dcr.Disjoint (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)))
    (hd_dec_bne : dcr.Disjoint (CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back))) :
    cpsBranchWithin 63 lbase
      ((((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
          (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).union
          ((CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs)
      lbase
        (unified_lenloop_body_post regionBase bs (bs[i]'hi) (itemResidue (bs[i]'hi))
          (itemLenRegion (bs[i]'hi) bs i) (itemX12Region (bs[i]'hi) bs i v12Old)
          (itemNextPtrRegion (bs[i]'hi) regionBase i bs) (itemX14 (bs[i]'hi) v14Old)
          endPtr (itemNextPtrRegion (bs[i]'hi) regionBase i bs ≠ endPtr))
      (joinPC + 8)
        (unified_lenloop_body_post regionBase bs (bs[i]'hi) (itemResidue (bs[i]'hi))
          (itemLenRegion (bs[i]'hi) bs i) (itemX12Region (bs[i]'hi) bs i v12Old)
          (itemNextPtrRegion (bs[i]'hi) regionBase i bs) (itemX14 (bs[i]'hi) v14Old)
          endPtr (itemNextPtrRegion (bs[i]'hi) regionBase i bs = endPtr)) := by
  set pfx := bs[i]'hi with hpfx
  simp only [unified_lenloop_body_post_unfold]
  set bz := pfx.zeroExtend 64 with hbz
  -- Step 1: LBU x5, x13, 0 — load the prefix byte into x5.
  have lbu_raw := bytesRegion_lbu_within .x5 .x13 regionBase v5Old lbase bs i
    (by decide) halign hi hover hvalid
  have s_lbu : cpsTripleWithin 1 lbase (lbase + 4)
      (CodeReq.singleton lbase (.LBU .x5 .x13 0))
      ((.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) **
         (.x14 ↦ᵣ v14Old) ** (.x15 ↦ᵣ endPtr))
        (by pcFree) lbu_raw)
  -- Step 2: the region decoder (opaque), framed with x15 = endPtr (untouched).
  rw [hdec_base] at decoder
  have s_dec : cpsTripleWithin 60 (lbase + 4) joinPC dcr
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (.x14 ↦ᵣ v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemPtrRegion pfx regionBase i) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x15 ↦ᵣ endPtr) (by pcFree) decoder)
  -- Step 3: ADD x13, x13, x11 — advance x13 to the next item start.
  have add_raw := add_spec_gen_rd_eq_rs1_within .x13 .x11
    (itemPtrRegion pfx regionBase i) (itemLenRegion pfx bs i) joinPC (by nofun)
  have s_add : cpsTripleWithin 1 joinPC (joinPC + 4)
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemPtrRegion pfx regionBase i) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by simp only [itemNextPtrRegion]; xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs)
        (by pcFree) add_raw)
  -- Step 4: BNE x13, x15, back — loop while the pointer has not reached endPtr.
  have bne_raw := bne_spec_gen_within .x13 .x15 back
    (itemNextPtrRegion pfx regionBase i bs) endPtr (joinPC + 4)
  have bne_framed : cpsBranchWithin 1 (joinPC + 4)
      (CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back))
      ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
       (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
       (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
       (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs)
      lbase
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
         (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs
           ** ⌜itemNextPtrRegion pfx regionBase i bs ≠ endPtr⌝)
      (joinPC + 8)
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
         (.x13 ↦ᵣ itemNextPtrRegion pfx regionBase i bs) ** (.x14 ↦ᵣ itemX14 pfx v14Old) **
         (.x15 ↦ᵣ endPtr) ** bytesRegion regionBase bs
           ** ⌜itemNextPtrRegion pfx regionBase i bs = endPtr⌝) := by
    have h_eq : (joinPC + 4 : Word) + 4 = joinPC + 8 := by bv_omega
    rw [h_eq, hback] at bne_raw
    exact cpsBranchWithin_weaken
      (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x5 ↦ᵣ bz) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ itemResidue pfx) **
         (.x11 ↦ᵣ itemLenRegion pfx bs i) ** (.x12 ↦ᵣ itemX12Region pfx bs i v12Old) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** bytesRegion regionBase bs)
        (by pcFree) bne_raw)
  -- Extend the BNE CR with a trailing empty (to match the seq output shape).
  have bne_ext : cpsBranchWithin 1 (joinPC + 4)
      ((CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty) _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  -- Disjointness for the union chain.
  have hd2 : ((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).Disjoint
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11)) :=
    CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj) hd_dec_add
  have hd3 : (((CodeReq.singleton lbase (.LBU .x5 .x13 0)).union dcr).union
      (CodeReq.singleton joinPC (.ADD .x13 .x13 .x11))).Disjoint
      ((CodeReq.singleton (joinPC + 4) (.BNE .x13 .x15 back)).union CodeReq.empty) :=
    CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.union_left (CodeReq.Disjoint.singleton hne_lj4) hd_dec_bne)
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.empty_right _)
  -- Compose the chain.
  have t12 := cpsTripleWithin_seq hd_lbu_dec s_lbu s_dec
  have t123 := cpsTripleWithin_seq hd2 t12 s_add
  exact cpsTripleWithin_seq_cpsBranchWithin hd3 t123 bne_ext

end EvmAsm.Rv64.RLP
