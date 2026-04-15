/-
  EvmAsm.Evm64.DivMod.LoopIterN1

  Loop body cpsTriple specs for n=1 (1-limb divisor).
  These specialize the generic LoopBodyN1 cpsBranch specs to specific j values,
  producing cpsTriple specs using divK_store_loop_j0_spec (j=0) and
  divK_store_loop_jgt0_spec (j>0).

  For n=1, the loop runs 4 iterations (j=3 then j=2 then j=1 then j=0). This file covers:
  - j=0 (final iteration): cpsTriple base+448 → base+904 (max+skip, max+addback, call+skip, call+addback)
  - j=1: cpsTriple base+448 → base+448 (max+skip, max+addback, call+skip, call+addback)
  - j=2: cpsTriple base+448 → base+448 (max+skip, max+addback, call+skip, call+addback)
  - j=3 (first iteration): cpsTriple base+448 → base+448 (max+skip, max+addback, call+skip, call+addback)

  For n=1: BLTU compares u1 vs v0, div128 uses u_hi=u1, u_lo=u0, v_top=v0.
-/

import EvmAsm.Evm64.DivMod.LoopBodyN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=0 → cpsTriple to base+904
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+skip, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n1_max_skip_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0
  let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi
  let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1
  let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi
  let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2
  let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi
  let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  -- 1. Trial max full (base+448 → base+516)
  have TF := divK_trial_max_full_spec sp (0 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (0 : Word)] at TF
  rw [u_addr8_eq_n1 sp (0 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  -- 2. Mulsub + correction skip (base+516 → base+880)
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (0 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  -- 3. Store + loop exit j=0 (cpsTriple base+880 → base+904)
  have SL := divK_store_loop_j0_spec sp q_hat u4_new (0 : Word) q_old base hv_q
  intro_lets at SL
  -- 4. Frame TF with mulsub cells (n=1: u1,u0,v0 consumed by trial; v1,u2,v2,u3,v3,u_top in frame)
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  -- 5. Compose TF + MCS0
  seqFrame TFf MCS0
  -- 6. Frame store_loop_j0 with remaining atoms
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  -- 7. Compose pre_store + SLf
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  -- 8. Permute final cpsTriple to match target
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ addback, j=0 → cpsTriple to base+904
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+addback, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n1_max_addback_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackPost sp (0 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi
  let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (0 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (0 : Word)] at TF
  rw [u_addr8_eq_n1 sp (0 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (0 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  have SL := divK_store_loop_j0_spec sp q_hat' aun4 aco3 q_old base hv_q
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=3 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+skip, j=3.
    Since j=3, the BGE loop-back is taken (j' = 2 ≥ 0), giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_skip_j3_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (3 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (3 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (3 : Word)] at TF
  rw [u_addr8_eq_n1 sp (3 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (3 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  have hj_pos : BitVec.slt ((3 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (3 : Word) q_hat u4_new (0 : Word) q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ addback, j=3 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+addback, j=3.
    Since j=3, the BGE loop-back is taken (j' = 2 ≥ 0), giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_addback_j3_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackPost sp (3 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (3 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (3 : Word)] at TF
  rw [u_addr8_eq_n1 sp (3 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (3 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  have hj_pos : BitVec.slt ((3 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (3 : Word) q_hat' aun4 aco3 q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=1 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+skip, j=1.
    Since j=1, the BGE loop-back is taken (j' = 0 ≥ 0), giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_skip_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (1 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (1 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (1 : Word)] at TF
  rw [u_addr8_eq_n1 sp (1 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (1 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  have hj_pos : BitVec.slt ((1 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (1 : Word) q_hat u4_new (0 : Word) q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ addback, j=1 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+addback, j=1.
    Since j=1, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_addback_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackPost sp (1 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (1 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (1 : Word)] at TF
  rw [u_addr8_eq_n1 sp (1 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (1 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  have hj_pos : BitVec.slt ((1 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (1 : Word) q_hat' aun4 aco3 q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ skip, j=2 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+skip, j=2.
    Since j=2, the BGE loop-back is taken (j' = 1 ≥ 0), giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_skip_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1SkipPost sp (2 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (2 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (2 : Word)] at TF
  rw [u_addr8_eq_n1 sp (2 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (2 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  have hj_pos : BitVec.slt ((2 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (2 : Word) q_hat u4_new (0 : Word) q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU not-taken (max path) + BEQ addback, j=2 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, max+addback, j=2.
    Since j=2, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_max_addback_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u1 v0) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopBodyN1AddbackPost sp (2 : Word) q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_hat q_addr hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_max_full_spec sp (2 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old
    u1 u0 v0 base hv_j hv_n1 hv_uhi hv_ulo hv_vtop hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (2 : Word)] at TF
  rw [u_addr8_eq_n1 sp (2 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    (2 : Word) u0 vtop_base u1 v0 v2_old base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  have hj_pos : BitVec.slt ((2 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (2 : Word) q_hat' aun4 aco3 q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    ((.x2 ↦ᵣ v2_old) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost; rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ skip, j=0 → cpsTriple to base+904
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+skip, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n1_call_skip_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallSkipPostJ sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (0 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (0 : Word)] at TF
  rw [u_addr8_eq_n1 sp (0 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  have SL := divK_store_loop_j0_spec sp q_hat u4_new (0 : Word) q_old base hv_q
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ addback, j=0 → cpsTriple to base+904
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+addback, j=0.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n1_call_addback_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackPostJ sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (0 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (0 : Word)] at TF
  rw [u_addr8_eq_n1 sp (0 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  have SL := divK_store_loop_j0_spec sp q_hat' aun4 aco3 q_old base hv_q
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ skip, j=1 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+skip, j=1.
    Since j=1, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_call_skip_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallSkipPostJ sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (1 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (1 : Word)] at TF
  rw [u_addr8_eq_n1 sp (1 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  have hj_pos : BitVec.slt ((1 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (1 : Word) q_hat u4_new (0 : Word) q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ addback, j=1 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+addback, j=1.
    Since j=1, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_call_addback_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackPostJ sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (1 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (1 : Word)] at TF
  rw [u_addr8_eq_n1 sp (1 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  have hj_pos : BitVec.slt ((1 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (1 : Word) q_hat' aun4 aco3 q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (1 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ skip, j=2 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+skip, j=2.
    Since j=2, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_call_skip_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallSkipPostJ sp base (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (2 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (2 : Word)] at TF
  rw [u_addr8_eq_n1 sp (2 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  have hj_pos : BitVec.slt ((2 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (2 : Word) q_hat u4_new (0 : Word) q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ addback, j=2 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+addback, j=2.
    Since j=2, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_call_addback_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackPostJ sp base (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (2 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (2 : Word)] at TF
  rw [u_addr8_eq_n1 sp (2 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  have hj_pos : BitVec.slt ((2 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (2 : Word) q_hat' aun4 aco3 q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ skip, j=3 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+skip, j=3.
    Since j=3, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_call_skip_j3_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallSkipPostJ sp base (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isSkipBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (3 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (3 : Word)] at TF
  rw [u_addr8_eq_n1 sp (3 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCS := divK_mulsub_correction_skip_spec sp q_hat (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCS
  have MCS0 := MCS hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  have hj_pos : BitVec.slt ((3 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (3 : Word) q_hat u4_new (0 : Word) q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCS0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
     (sp + signExtend12 3976 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3) **
     ((u_base + signExtend12 4064) ↦ₘ u4_new) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCS0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallSkipPostJ div128Quot div128DLo div128Un0
            loopBodyN1SkipPost loopBodySkipPost mulsubN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

-- ============================================================================
-- n=1, BLTU taken (call path) + BEQ addback, j=3 → cpsTriple to base+448
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Loop body cpsTriple for n=1, call+addback, j=3.
    Since j=3, the BGE loop-back is taken, giving a cpsTriple to base+448. -/
theorem divK_loop_body_n1_call_addback_j3_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopBodyN1CallAddbackPostJ sp base (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  let d_hi := v0 >>> (32 : BitVec 6).toNat
  let d_lo := (v0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u0 >>> (32 : BitVec 6).toNat
  let div_un0 := (u0 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u1 d_hi; let rhat := u1 - q1 * d_hi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + d_hi
  let q_dlo := q1c * d_lo
  let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
  let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
  let cu_q1_dlo := q1' * d_lo
  let un21 := cu_rhat_un1 - cu_q1_dlo
  let q0 := rv64_divu un21 d_hi; let rhat2 := un21 - q0 * d_hi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
  let q0_dlo := q0c * d_lo
  let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
  let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
  unfold isAddbackBorrowN1Call div128Quot at hborrow
  let vtop_base := sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat
  have TF := divK_trial_call_full_spec sp (3 : Word) (1 : Word) j_old v5_old v6_old v7_old v10_old v11_old v2_old
    u1 u0 v0 ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu
  dsimp only [] at TF
  rw [u_addr_eq_n1 sp (3 : Word)] at TF
  rw [u_addr8_eq_n1 sp (3 : Word)] at TF
  rw [vtop_eq_v0_n1 sp] at TF
  have MCA := divK_mulsub_correction_addback_spec sp q_hat (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top
    rhat2_un0 q0' d_hi q0_dlo q1' (base + 516) base
    hv_j hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4
  intro_lets at MCA
  have MCA0 := MCA hborrow
  let p0_lo := q_hat * v0; let p0_hi := rv64_mulhu q_hat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := q_hat * v1; let p1_hi := rv64_mulhu q_hat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := q_hat * v2; let p2_hi := rv64_mulhu q_hat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := q_hat * v3; let p3_hi := rv64_mulhu q_hat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let u4_new := u_top - c3
  let upc0 := un0 + (signExtend12 0 : Word)
  let ac1_0 := if BitVec.ult upc0 (signExtend12 0 : Word) then (1 : Word) else 0
  let aun0 := upc0 + v0; let ac2_0 := if BitVec.ult aun0 v0 then (1 : Word) else 0
  let aco0 := ac1_0 ||| ac2_0
  let upc1 := un1 + aco0; let ac1_1 := if BitVec.ult upc1 aco0 then (1 : Word) else 0
  let aun1 := upc1 + v1; let ac2_1 := if BitVec.ult aun1 v1 then (1 : Word) else 0
  let aco1 := ac1_1 ||| ac2_1
  let upc2 := un2 + aco1; let ac1_2 := if BitVec.ult upc2 aco1 then (1 : Word) else 0
  let aun2 := upc2 + v2; let ac2_2 := if BitVec.ult aun2 v2 then (1 : Word) else 0
  let aco2 := ac1_2 ||| ac2_2
  let upc3 := un3 + aco2; let ac1_3 := if BitVec.ult upc3 aco2 then (1 : Word) else 0
  let aun3 := upc3 + v3; let ac2_3 := if BitVec.ult aun3 v3 then (1 : Word) else 0
  let aco3 := ac1_3 ||| ac2_3
  let aun4 := u4_new + aco3
  let q_hat' := q_hat + signExtend12 4095
  have hj_pos : BitVec.slt ((3 : Word) + signExtend12 4095) 0 = false := by decide
  have SL := divK_store_loop_jgt0_spec sp (3 : Word) q_hat' aun4 aco3 q_old base hv_q hj_pos
  intro_lets at SL
  have TFf := cpsTriple_frame_left _ _ _ _ _
    (((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4064) ↦ₘ u_top) **
     (q_addr ↦ₘ q_old))
    (by pcFree) TF
  seqFrame TFf MCA0
  have SLf := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ u_base) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ aun3) **
     (sp + signExtend12 3976 ↦ₘ (3 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ aun0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ aun1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ aun2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ aun3) **
     ((u_base + signExtend12 4064) ↦ₘ aun4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v0) **
     (sp + signExtend12 3952 ↦ₘ d_lo) **
     (sp + signExtend12 3944 ↦ₘ div_un0))
    (by pcFree) SL
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by rw [sepConj_assoc'] at hp; xperm_hyp hp) TFfMCA0 SLf
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopBodyN1CallAddbackPostJ div128Quot div128DLo div128Un0
            loopBodyN1AddbackPost loopBodyAddbackPost mulsubN4 addbackN4 loopExitPostN1 loopExitPost
      rw [sepConj_assoc'] at hp; xperm_hyp hp)
    full

end EvmAsm.Evm64
