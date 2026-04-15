/-
  EvmAsm.Evm64.DivMod.LoopComposeN3

  Two-iteration loop composition for n=3: composes j=1 (loop-back) with
  j=0 (loop-exit) to produce a cpsTriple from base+448 to base+904.

  For n=3, the loop runs 2 iterations. The j=1 iteration modifies u[1]..u[4]
  and stores q[1]. The j=0 iteration reads u[0]..u[4] (where u[1]..u[4]
  are the updated values from j=1) and stores q[0].
-/

import EvmAsm.Evm64.DivMod.LoopIterN3

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address equality lemmas for j=1 output → j=0 input transition
--
-- j=1 postcondition uses u_base(1) = sp + signExtend12(4056) - 8
-- j=0 precondition uses u_base(0) = sp + signExtend12(4056)
-- The overlap: u_base(1) + offset_k = u_base(0) + offset_{k-1}
-- ============================================================================

/-- j=1 un0 at u_base(1)+0 = j=0 u1 at u_base(0)-8 -/
theorem u_j1_0_eq_j0_4088 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  simp only [
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

/-- j=1 un1 at u_base(1)-8 = j=0 u2 at u_base(0)-16 -/
theorem u_j1_4088_eq_j0_4080 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

/-- j=1 un2 at u_base(1)-16 = j=0 u3 at u_base(0)-24 -/
theorem u_j1_4080_eq_j0_4072 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

/-- j=1 un3 at u_base(1)-24 = j=0 u_top at u_base(0)-32 -/
theorem u_j1_4072_eq_j0_4064 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

-- ============================================================================
-- Two-iteration composition: max+skip at both j=1 and j=0
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Full n=3 loop (max+skip path at both iterations).
    Composes j=1 (base+448→base+448) with j=0 (base+448→base+904). -/
theorem divK_loop_n3_max_skip_skip_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (base : Word)
    -- Validity hypotheses (j=1 and j=0)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    -- Branch conditions (j=1)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hborrow_1 : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3)
                  then (1 : Word) else 0) = (0 : Word))
    -- Branch conditions (j=0, depend on j=1 mulsub output)
    (hbltu_0 : isMaxBltuN3After_j1_skip v0 v1 v2 v3 u0 u1 u2 u3)
    (hborrow_0 : isSkipBorrowN3After_j1_skip v0 v1 v2 v3 u0 u1 u2 u3 u0_orig) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN3Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old)
      (loopN3MaxSkipSkipPost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- Unfold bundled condition defs
  delta isMaxBltuN3After_j1_skip isSkipBorrowN3After_j1_skip at hbltu_0 hborrow_0
  simp only [] at hbltu_0 hborrow_0
  let q_hat : Word := signExtend12 4095
  let ms := mulsubN4 q_hat v0 v1 v2 v3 u0 u1 u2 u3
  -- 1. j=1 iteration spec
  have J1 := divK_loop_body_n3_max_skip_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old base
    hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1 hbltu_1
  intro_lets at J1
  have J1s := J1 hborrow_1
  -- Frame j=1 with u0_orig and q0_old
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J1s
  -- 2. j=0 iteration spec (instantiated with j=1 mulsub output)
  have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_j1_0_eq_j0_4088]; exact hv_u0_1
  have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_j1_4088_eq_j0_4080]; exact hv_u1_1
  have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_j1_4080_eq_j0_4072]; exact hv_u2_1
  have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_j1_4072_eq_j0_4064]; exact hv_u3_1
  have J0 := divK_loop_body_n3_max_skip_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1 ms.2.2.2.2 q_hat ms.2.2.2.1
    v0 v1 v2 v3 u0_orig ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 q0_old base
    hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
    hbltu_0
  intro_lets at J0
  have J0s := J0 hborrow_0
  -- Frame j=0 with j=1's carried atoms (u4_new, q[1])
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (u_top - ms.2.2.2.2)) ** (q_addr_1 ↦ₘ q_hat))
    (by pcFree) J0s
  -- 3. Compose via perm: rewrite j=1 postcondition addresses → j=0 precondition
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopBodyN3SkipPost loopBodySkipPost loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 4. Clean up postcondition
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN3MaxSkipSkipPost
      exact hp)
    full

-- ============================================================================
-- Unified per-iteration specs: case-split skip/addback internally
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified j=1 max-path spec: handles both skip and addback internally.
    Produces loopIterPostN3Max which uses iterN3Max for the result values. -/
theorem divK_loop_body_n3_max_unified_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
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
    (hbltu : ¬BitVec.ult u3 v2) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopIterPostN3Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n3_max_addback_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Max iterN3Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN3AddbackPost loopBodyAddbackPost at hp
        exact hp)
      (J1 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n3_max_skip_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Max iterN3Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN3SkipPost loopBodySkipPost at hp
        exact hp)
      (J1 hborrow)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified j=0 max-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n3_max_unified_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
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
    (hbltu : ¬BitVec.ult u3 v2) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n3_max_addback_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Max iterN3Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN3AddbackPost loopBodyAddbackPost at hp
        exact hp)
      (J0 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n3_max_skip_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Max iterN3Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN3SkipPost loopBodySkipPost at hp
        exact hp)
      (J0 hborrow)

-- ============================================================================
-- Unified two-iteration composition: max path at both j=1 and j=0
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Full n=3 loop (max path at both iterations, all skip/addback combinations).
    Composes j=1 (base+448→base+448) with j=0 (base+448→base+904). -/
theorem divK_loop_n3_max_max_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (base : Word)
    -- Validity hypotheses (j=1 and j=0)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    -- Branch conditions
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN3Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old)
      (loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 unified iteration spec
  have J1 := divK_loop_body_n3_max_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old base
    hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1 hbltu_1
  intro_lets at J1
  -- Frame j=1 with u0_orig and q0_old
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J1
  -- 2. Derive j=0 validity hypotheses via address rewriting
  have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_j1_0_eq_j0_4088]; exact hv_u0_1
  have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_j1_4088_eq_j0_4080]; exact hv_u1_1
  have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_j1_4080_eq_j0_4072]; exact hv_u2_1
  have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_j1_4072_eq_j0_4064]; exact hv_u3_1
  -- 3. j=0 unified iteration spec (inputs from j=1 via iterN3Max)
  have J0 := divK_loop_body_n3_max_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old base
    hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
    hbltu_0
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
    (by pcFree) J0
  -- 4. Compose via perm: rewrite j=1 postcondition addresses → j=0 precondition
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN3Max loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN3MaxPost
      exact hp)
    full

-- ============================================================================
-- Unified per-iteration call-path specs
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified j=1 call-path spec: handles both skip and addback internally. -/
theorem divK_loop_body_n3_call_unified_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
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
    (hbltu : BitVec.ult u3 v2) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
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
      (loopIterPostN3Call sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN3Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n3_call_addback_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Call iterN3Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN3CallAddbackPostJ loopBodyN3AddbackPost loopBodyAddbackPost at hp
        exact hp)
      J1
  · -- skip path
    have hborrow : isSkipBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J1 := divK_loop_body_n3_call_skip_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Call iterN3Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN3CallSkipPostJ loopBodyN3SkipPost loopBodySkipPost at hp
        exact hp)
      J1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified j=0 call-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n3_call_unified_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
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
    (hbltu : BitVec.ult u3 v2) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
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
      (loopIterPostN3Call sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN3Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n3_call_addback_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Call iterN3Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN3CallAddbackPost loopBodyN3AddbackPost loopBodyAddbackPost at hp
        exact hp)
      J0
  · -- skip path
    have hborrow : isSkipBorrowN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J0 := divK_loop_body_n3_call_skip_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN3Call iterN3Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN3CallSkipPost loopBodyN3SkipPost loopBodySkipPost at hp
        exact hp)
      J0

-- ============================================================================
-- Unified two-iteration composition: call path at both j=1 and j=0
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Full n=3 loop (call path at both iterations, all skip/addback combinations).
    Composes j=1 (base+448→base+448) with j=0 (base+448→base+904). -/
theorem divK_loop_n3_call_call_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    -- Validity hypotheses
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    -- Branch conditions
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 unified call iteration spec
  have J1 := divK_loop_body_n3_call_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1 hbltu_1
  intro_lets at J1
  -- Frame j=1 with u0_orig and q0_old
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J1
  -- 2. Derive j=0 validity hypotheses via address rewriting
  have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_j1_0_eq_j0_4088]; exact hv_u0_1
  have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_j1_4088_eq_j0_4080]; exact hv_u1_1
  have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_j1_4080_eq_j0_4072]; exact hv_u2_1
  have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_j1_4072_eq_j0_4064]; exact hv_u3_1
  -- 3. j=0 unified call iteration spec (inputs from j=1 via iterN3Call)
  have J0 := divK_loop_body_n3_call_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old
    (base + 516) v2 (div128DLo v2) (div128Un0 u2)
    base
    hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
    hbltu_0
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
    (by pcFree) J0
  -- 4. Compose via perm
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN3Call loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN3CallCallPost
      exact hp)
    full

-- ============================================================================
-- Cross-path: j=1 max, j=0 call
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Full n=3 loop (j=1 max path, j=0 call path).
    Scratch cells are in the frame for j=1, consumed/written by j=0 call. -/
theorem divK_loop_n3_max_call_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    -- Branch conditions: j=1 max (BLTU not taken), j=0 call (BLTU taken)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 max unified spec (no scratch cells)
  have J1 := divK_loop_body_n3_max_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old base
    hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1 hbltu_1
  intro_lets at J1
  -- Frame j=1 with u0_orig, q0_old, AND scratch cells (max doesn't touch scratch)
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J1
  -- 2. Derive j=0 validity hypotheses
  have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_j1_0_eq_j0_4088]; exact hv_u0_1
  have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_j1_4088_eq_j0_4080]; exact hv_u1_1
  have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_j1_4080_eq_j0_4072]; exact hv_u2_1
  have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_j1_4072_eq_j0_4064]; exact hv_u3_1
  -- 3. j=0 call unified spec (inputs from j=1 via iterN3Max, scratch from frame)
  have J0 := divK_loop_body_n3_call_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old
    ret_mem d_mem dlo_mem scratch_un0
    base
    hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
    hbltu_0
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
    (by pcFree) J0
  -- 4. Compose via perm
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN3Max loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopN3MaxCallPost; exact hp)
    full

-- ============================================================================
-- Cross-path: j=1 call, j=0 max
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Full n=3 loop (j=1 call path, j=0 max path).
    Scratch cells from j=1 call are carried through in the frame. -/
theorem divK_loop_n3_call_max_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    -- Branch conditions: j=1 call (BLTU taken), j=0 max (BLTU not taken)
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN3PreWithScratch loopN3Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 call unified spec (with scratch cells)
  have J1 := divK_loop_body_n3_call_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1 hbltu_1
  intro_lets at J1
  -- Frame j=1 with u0_orig and q0_old
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J1
  -- 2. Derive j=0 validity hypotheses
  have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_j1_0_eq_j0_4088]; exact hv_u0_1
  have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_j1_4088_eq_j0_4080]; exact hv_u1_1
  have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_j1_4080_eq_j0_4072]; exact hv_u2_1
  have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_j1_4072_eq_j0_4064]; exact hv_u3_1
  -- 3. j=0 max unified spec (inputs from j=1 via iterN3Call)
  have J0 := divK_loop_body_n3_max_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old base
    hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
    hbltu_0
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1]) AND j=1's scratch cells
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v2) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v2) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u2))
    (by pcFree) J0
  -- 4. Compose via perm
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN3Call loopExitPostN3 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by delta loopN3CallMaxPost; exact hp)
    full

end EvmAsm.Evm64
