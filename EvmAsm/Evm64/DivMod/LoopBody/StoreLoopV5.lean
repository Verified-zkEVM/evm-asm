/-
  EvmAsm.Evm64.DivMod.LoopBody.StoreLoopV5

  v5 store-loop loop-body brick over `sharedDivModCodeNoNop_v5`.

  Brick 5 of the v5 n=1 loop-body execution layer (bead `evm-asm-wbc4i.7.2`).
  The store-q[j] + loop-control (addi + bge) instructions are SHARED between v4
  and v5 (they run after the mulsub/correction block, far from the differing
  `div128` subroutine), so these are mechanical mirrors of
  `divK_store_loop_{j0,jgt0}_v4_spec_within_noNop`, swapping the code surface
  `sharedDivModCodeNoNop_v4` → `_v5` and the code-subsumption lemma
  `lb_sub_noNop_v4` → `lb_sub_noNop_v5`.

  Feeds `divK_loop_body_n1_call_skip_*_v5` (next brick), which composes
  trial-call-full v5 (#7237) + mulsub-correction-skip v5 (#7238) + these.
-/

module

public import EvmAsm.Evm64.DivMod.LoopBody.StoreLoop
public import EvmAsm.Evm64.DivMod.Compose.V5Code

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Store q[0] + loop exit at j=0 over `sharedDivModCodeNoNop_v5`.  Mechanical
    mirror of `divK_store_loop_j0_v4_spec_within_noNop`. -/
theorem divK_store_loop_j0_v5_spec_within_noNop
    (sp qHat v5Old v7Old qOld : Word)
    (base : Word) :
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    let j' := (0 : Word) + signExtend12 4095
    cpsTripleWithin 6 (base + storeLoopOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      ((.x9 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qOld))
      ((.x9 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qHat)) := by
  intro qAddr j'
  have SQ := divK_store_qj_spec_within sp (0 : Word) qHat v5Old v7Old qOld (base + storeLoopOff)
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_noNop_v5 109 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 110 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 111 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_noNop_v5 112 _ _ (by decide) (by bv_addr) (by decide))))) SQ
  have haddi := addi_spec_gen_same_within .x9 (0 : Word) 4095 (base + loopControlOff) (by nofun)
  rw [show (base + loopControlOff : Word) + 4 = base + loopBackBgeOff from by bv_addr] at haddi
  have haddi_e := cpsTripleWithin_extend_code (hmono := by
    exact lb_sub_noNop_v5 113 _ _ (by decide) (by bv_addr) (by decide)) haddi
  have hbge_raw := bge_spec_gen_within .x9 .x0 (7736 : BitVec 13) j' (0 : Word) (base + loopBackBgeOff)
  rw [show (base + loopBackBgeOff : Word) + signExtend13 (7736 : BitVec 13) = base + loopBodyOff from by rv64_addr,
      show (base + loopBackBgeOff : Word) + 4 = base + denormOff from by bv_addr] at hbge_raw
  have hbge_ext := cpsBranchWithin_extend_code (hmono := by
    exact lb_sub_noNop_v5 114 _ _ (by decide) (by bv_addr) (by decide)) hbge_raw
  have hbge_exit_raw := cpsBranchWithin_ntakenPath hbge_ext
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
      exact hpure (by decide : BitVec.slt ((0 : Word) + signExtend12 4095) 0 = true))
  have hbge_exit := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbge_exit_raw
  have SQx0 : cpsTripleWithin 4 (base + storeLoopOff) (base + loopControlOff) (sharedDivModCodeNoNop_v5 base)
      ((.x9 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qOld))
      ((.x9 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) **
       (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qHat)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  have haddi_x0 := cpsTripleWithin_frameR
      (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_e
  have addi_bge := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddi_x0 hbge_exit
  have addi_bge_framed := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ (0 : Word) <<< (3 : BitVec 6).toNat) ** (.x7 ↦ᵣ qAddr) **
       (qAddr ↦ₘ qHat))
      (by pcFree) addi_bge
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) SQx0 addi_bge_framed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

/-- Store q[j] + loop back at j>0 over `sharedDivModCodeNoNop_v5`.  Mechanical
    mirror of `divK_store_loop_jgt0_v4_spec_within_noNop`. -/
theorem divK_store_loop_jgt0_v5_spec_within_noNop
    (sp j qHat v5Old v7Old qOld : Word)
    (base : Word)
    (hj_pos : BitVec.slt (j + signExtend12 4095) 0 = false) :
    let jX8 := j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - jX8
    let j' := j + signExtend12 4095
    cpsTripleWithin 6 (base + storeLoopOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
      ((.x9 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qOld))
      ((.x9 ↦ᵣ j') ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) **
       (qAddr ↦ₘ qHat)) := by
  intro jX8 qAddr j'
  have SQ := divK_store_qj_spec_within sp j qHat v5Old v7Old qOld (base + storeLoopOff)
  dsimp only [] at SQ
  rw [lb_sqj] at SQ
  have SQe := cpsTripleWithin_extend_code (hmono := by
    exact CodeReq.union_sub (lb_sub_noNop_v5 109 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 110 _ _ (by decide) (by bv_addr) (by decide))
     (CodeReq.union_sub (lb_sub_noNop_v5 111 _ _ (by decide) (by bv_addr) (by decide))
      (lb_sub_noNop_v5 112 _ _ (by decide) (by bv_addr) (by decide))))) SQ
  have haddi := addi_spec_gen_same_within .x9 j 4095 (base + loopControlOff) (by nofun)
  rw [show (base + loopControlOff : Word) + 4 = base + loopBackBgeOff from by bv_addr] at haddi
  have haddi_e := cpsTripleWithin_extend_code (hmono := by
    exact lb_sub_noNop_v5 113 _ _ (by decide) (by bv_addr) (by decide)) haddi
  have hbge_raw := bge_spec_gen_within .x9 .x0 (7736 : BitVec 13) j' (0 : Word) (base + loopBackBgeOff)
  rw [show (base + loopBackBgeOff : Word) + signExtend13 (7736 : BitVec 13) = base + loopBodyOff from by rv64_addr,
      show (base + loopBackBgeOff : Word) + 4 = base + denormOff from by bv_addr] at hbge_raw
  have hbge_ext := cpsBranchWithin_extend_code (hmono := by
    exact lb_sub_noNop_v5 114 _ _ (by decide) (by bv_addr) (by decide)) hbge_raw
  have hbge_exit_raw := cpsBranchWithin_takenPath hbge_ext
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQf
      exact absurd hpure (by rw [hj_pos]; exact Bool.false_ne_true))
  have hbge_exit := cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    hbge_exit_raw
  have SQx0 : cpsTripleWithin 4 (base + storeLoopOff) (base + loopControlOff) (sharedDivModCodeNoNop_v5 base)
      ((.x9 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ v5Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qOld))
      ((.x9 ↦ᵣ j) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (qAddr ↦ₘ qHat)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) SQe)
  have haddi_x0 := cpsTripleWithin_frameR
      (.x0 ↦ᵣ (0 : Word)) (by pcFree) haddi_e
  have addi_bge := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) haddi_x0 hbge_exit
  have addi_bge_framed := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x5 ↦ᵣ jX8) ** (.x7 ↦ᵣ qAddr) **
       (qAddr ↦ₘ qHat))
      (by pcFree) addi_bge
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) SQx0 addi_bge_framed
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    full

end EvmAsm.Evm64
