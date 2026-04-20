/-
  EvmAsm.Evm64.DivMod.LoopIterN1.Max

  Loop body cpsTriple specs for n=1, BLTU not-taken (max path).
  Split from LoopIterN1.lean for faster builds.
-/

import EvmAsm.Evm64.DivMod.LoopBodyN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (slt_jpos_1 slt_jpos_2 slt_jpos_3)

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=0 → cpsTriple to base+904
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=1, max+skip, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n1_max_skip_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr hborrow
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec sp (0 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (0 : Word)] at TF
  rw [u_addr8_eq_n1 sp (0 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp qHat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    (0 : Word) u0 vtopBase u1 v0 v2_old base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store + loop exit j=0 (cpsTriple base+880 → base+904)
  have SL := divK_store_loop_j0_spec sp qHat u4_new (0 : Word) q_old base
  intro_lets at SL
  -- 4. Frame TF with mulsub cells (n=1: u1,u0,v0 consumed by trial; v1,u2,v2,u3,v3,uTop in frame)
  have TFf := cpsTriple_frameR
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Frame store_loop_j0 with remaining atoms
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  -- 7. Compose pre_store + SLf
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  -- 8. Permute final cpsTriple to match target
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=3 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=1, max+skip, j=3.
    Since j=3, the BGE loop-back is taken (j' = 2 ≥ 0), giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_skip_j3_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    let uBase := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095
    let qAddr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (3 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr hborrow
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (3 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (3 : Word)] at TF
  rw [u_addr8_eq_n1 sp (3 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp qHat (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    (3 : Word) u0 vtopBase u1 v0 v2_old base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  have hj_pos := slt_jpos_3
  have SL := divK_store_loop_jgt0_spec sp (3 : Word) qHat u4_new (0 : Word) q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frameR
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=1 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=1, max+skip, j=1.
    Since j=1, the BGE loop-back is taken (j' = 0 ≥ 0), giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_skip_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095
    let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (1 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr hborrow
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (1 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (1 : Word)] at TF
  rw [u_addr8_eq_n1 sp (1 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp qHat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    (1 : Word) u0 vtopBase u1 v0 v2_old base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  have hj_pos := slt_jpos_1
  have SL := divK_store_loop_jgt0_spec sp (1 : Word) qHat u4_new (0 : Word) q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frameR
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=2 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
/-- Loop body cpsTriple for n=1, max+skip, j=2.
    Since j=2, the BGE loop-back is taken (j' = 1 ≥ 0), giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_skip_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0) :
    let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qHat : Word := signExtend12 4095
    let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult uTop (mulsubN4_c3 qHat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (2 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qHat qAddr hborrow
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := uTop - c3
  let vtopBase := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (2 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (2 : Word)] at TF
  rw [u_addr8_eq_n1 sp (2 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp qHat (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop
    (2 : Word) u0 vtopBase u1 v0 v2_old base

  intro_lets at MCS
  have MCS0 := MCS hborrow
  have hj_pos := slt_jpos_2
  have SL := divK_store_loop_jgt0_spec sp (2 : Word) qHat u4_new (0 : Word) q_old base hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frameR
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frameR
    ((.x6 ↦ᵣ uBase) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
     ((uBase + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_perm_same_cr
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

end EvmAsm.Evm64
