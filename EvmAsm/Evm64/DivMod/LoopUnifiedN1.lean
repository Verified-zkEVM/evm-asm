/-
  EvmAsm.Evm64.DivMod.LoopUnifiedN1

  Bool-parameterized (unified) loop composition for n=1.
  Issue #262: Unify max/call branch paths via Bool parameter.

  For n=1, the loop runs 4 iterations (j=3, j=2, j=1, j=0).
  Structure:
  1. `divK_loop_n1_iter10_unified_spec (bltu_1 bltu_0 : Bool)`:
     Two-iteration (j=1, j=0) composition -- 4 cases.
  2. `divK_loop_n1_max_iter10_spec` / `divK_loop_n1_call_iter10_spec`:
     Compose j=2 (max or call) with the two-iteration intermediate.
  3. `divK_loop_n1_iter210_unified_spec (bltu_2 bltu_1 bltu_0 : Bool)`:
     Three-iteration -- dispatches via cases on bltu_2.
  4. `divK_loop_n1_max_iter210_spec` / `divK_loop_n1_call_iter210_spec`:
     Compose j=3 (max or call) with the three-iteration intermediate.
  5. `divK_loop_n1_unified_spec (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)`:
     Full four-iteration -- dispatches via cases on bltu_3.
-/

import EvmAsm.Evm64.DivMod.LoopComposeN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Two-iteration (j=1, j=0) unified composition
-- Same pattern as divK_loop_n2_iter10_unified_spec but with n=1 per-iteration specs
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified n=1 two-iteration loop composition for j=1 and j=0,
    parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max*max, call*call, max*call, call*max).
    Dispatches to existing per-iteration specs in LoopComposeN1.lean. -/
theorem divK_loop_n1_iter10_unified_spec (bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    -- Validity hypotheses
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
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
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    -- Unified branch conditions
    (hbltu_1 : bltu_1 = BitVec.ult u1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN1Iter10PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1Iter10Post bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
        ret_mem d_mem dlo_mem scratch_un0) := by
  -- Dispatch to per-iteration specs via case analysis on (bltu_1, bltu_0)
  cases bltu_1 <;> cases bltu_0 <;> simp only [iterN1_true, iterN1_false] at hbltu_0
  · -- (false, false) = max*max
    have hbltu_1' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_1.symm]; decide
    have hbltu_0' : ¬BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0 := by
      rw [show BitVec.ult _ v0 = false from hbltu_0.symm]; decide
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 max spec
    have J1 := divK_loop_body_n1_max_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1
      hbltu_1'
    intro_lets at J1
    -- Frame j=1 with u0_orig, q0_old, and scratch
    have J1f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) J1
    -- Derive j=0 validity via j=1->j=0 address linking
    have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
      rw [← u_n1_j1_0_eq_j0_4088]; exact hv_u0_1
    have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
      rw [← u_n1_j1_4088_eq_j0_4080]; exact hv_u1_1
    have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
      rw [← u_n1_j1_4080_eq_j0_4072]; exact hv_u2_1
    have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
      rw [← u_n1_j1_4072_eq_j0_4064]; exact hv_u3_1
    -- j=0 max spec (inputs from j=1 via iterN1Max)
    have J0 := divK_loop_body_n1_max_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
      v0 v1 v2 v3
      u0_orig
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
      q0_old base
      hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
      hbltu_0'
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms and scratch
    have J0f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) J0
    -- Compose j=1 and j=0 via address rewriting
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        delta loopIterPostN1Max loopExitPostN1 at hp
        simp only [] at hp ⊢
        have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    -- Bridge to unified postcondition
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_false, sepConj_emp_right']
        xperm_hyp hp)
      full
  · -- (false, true) = max*call
    have hbltu_1' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_1.symm]; decide
    have hbltu_0' : BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0 :=
      hbltu_0.symm ▸ rfl
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 max spec
    have J1 := divK_loop_body_n1_max_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1
      hbltu_1'
    intro_lets at J1
    have J1f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old) **
       (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) J1
    -- Derive j=0 validity
    have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
      rw [← u_n1_j1_0_eq_j0_4088]; exact hv_u0_1
    have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
      rw [← u_n1_j1_4088_eq_j0_4080]; exact hv_u1_1
    have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
      rw [← u_n1_j1_4080_eq_j0_4072]; exact hv_u2_1
    have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
      rw [← u_n1_j1_4072_eq_j0_4064]; exact hv_u3_1
    -- j=0 call spec (includes scratch in pre/post)
    have J0 := divK_loop_body_n1_call_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
      ((iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
      v0 v1 v2 v3
      u0_orig
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
      q0_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
      hbltu_0'
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms only
    have J0f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
      (by pcFree) J0
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        delta loopIterPostN1Max loopExitPostN1 at hp
        simp only [] at hp ⊢
        have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_false, sepConj_emp_right']
        xperm_hyp hp)
      full
  · -- (true, false) = call*max
    have hbltu_1' : BitVec.ult u1 v0 := hbltu_1.symm ▸ rfl
    have hbltu_0' : ¬BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0 := by
      rw [show BitVec.ult _ v0 = false from hbltu_0.symm]; decide
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 call spec (includes scratch)
    have J1 := divK_loop_body_n1_call_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1
      hbltu_1'
    intro_lets at J1
    -- Frame j=1 with u0_orig, q0_old only (scratch is in call spec)
    have J1f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
      (by pcFree) J1
    -- Derive j=0 validity
    have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
      rw [← u_n1_j1_0_eq_j0_4088]; exact hv_u0_1
    have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
      rw [← u_n1_j1_4088_eq_j0_4080]; exact hv_u1_1
    have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
      rw [← u_n1_j1_4080_eq_j0_4072]; exact hv_u2_1
    have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
      rw [← u_n1_j1_4072_eq_j0_4064]; exact hv_u3_1
    -- j=0 max spec (no scratch)
    have J0 := divK_loop_body_n1_max_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
      v0 v1 v2 v3
      u0_orig
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
      q0_old base
      hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
      hbltu_0'
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms + j=1 scratch (persists from call)
    have J0f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v0) **
       (sp + signExtend12 3952 ↦ₘ div128DLo v0) **
       (sp + signExtend12 3944 ↦ₘ div128Un0 u0))
      (by pcFree) J0
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        delta loopIterPostN1Call loopExitPostN1 at hp
        simp only [] at hp ⊢
        have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_true, sepConj_emp_right']
        xperm_hyp hp)
      full
  · -- (true, true) = call*call
    have hbltu_1' : BitVec.ult u1 v0 := hbltu_1.symm ▸ rfl
    have hbltu_0' : BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0 :=
      hbltu_0.symm ▸ rfl
    delta loopN1Iter10PreWithScratch loopN1Iter10Pre; simp only []
    let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    -- j=1 call spec (includes scratch)
    have J1 := divK_loop_body_n1_call_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0_1 hv_v1 hv_u1_1 hv_v2 hv_u2_1 hv_v3 hv_u3_1 hv_u4_1 hv_q1
      hbltu_1'
    intro_lets at J1
    -- Frame j=1 with u0_orig, q0_old only
    have J1f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
      (by pcFree) J1
    -- Derive j=0 validity
    have hv_u1_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
      rw [← u_n1_j1_0_eq_j0_4088]; exact hv_u0_1
    have hv_u2_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
      rw [← u_n1_j1_4088_eq_j0_4080]; exact hv_u1_1
    have hv_u3_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
      rw [← u_n1_j1_4080_eq_j0_4072]; exact hv_u2_1
    have hv_u4_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
      rw [← u_n1_j1_4072_eq_j0_4064]; exact hv_u3_1
    -- j=0 call spec (includes scratch -- j=0 overwrites j=1's scratch)
    have J0 := divK_loop_body_n1_call_unified_j0_spec sp (1 : Word)
      ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
      ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
      ((iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
      v0 v1 v2 v3
      u0_orig
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
      q0_old
      (base + 516) v0 (div128DLo v0) (div128Un0 u0) base
      hv_j hv_n1 hv_uhi_0 hv_ulo_0 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0_0 hv_v1 hv_u1_0 hv_v2 hv_u2_0 hv_v3 hv_u3_0 hv_u4_0 hv_q0
      hbltu_0'
    intro_lets at J0
    -- Frame j=0 with j=1's carried atoms only
    have J0f := cpsTriple_frame_left _ _ _ _ _
      (((u_base_1 + signExtend12 4064) ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
       (q_addr_1 ↦ₘ (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
      (by pcFree) J0
    have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
      (fun h hp => by
        delta loopIterPostN1Call loopExitPostN1 at hp
        simp only [] at hp ⊢
        have hj' : (1 : Word) + signExtend12 4095 = (0 : Word) := by decide
        rw [hj', u_n1_j1_0_eq_j0_4088 sp, u_n1_j1_4088_eq_j0_4080 sp,
            u_n1_j1_4080_eq_j0_4072 sp, u_n1_j1_4072_eq_j0_4064 sp] at hp
        rw [sepConj_assoc'] at hp
        xperm_hyp hp)
      J1f J0f
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        delta loopN1Iter10Post loopIterPostN1
        simp only [iterN1_true, sepConj_emp_right']
        xperm_hyp hp)
      full

-- ============================================================================
-- Three-iteration: compose j=2 with iter10 -- separate lemmas per case
-- Postcondition uses @[irreducible] loopN1Iter210Post
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Three-iteration composition when j=2 is max (bltu_2 = false).
    Composes j=2 max spec with the 2-iteration iter10 unified spec. -/
theorem divK_loop_n1_max_iter10_spec (bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     q2_old q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_2 : ¬BitVec.ult u1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1 v0) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN1Iter210PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 q2_old q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1Iter210Post false bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 ret_mem d_mem dlo_mem scratch_un0) := by
  let r2 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- Derive j=1 validity via j=2->j=1 address linking
  have hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_n1_j2_0_eq_j1_4088]; exact hv_u0_2
  have hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_n1_j2_4088_eq_j1_4080]; exact hv_u1_2
  have hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_n1_j2_4080_eq_j1_4072]; exact hv_u2_2
  have hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_n1_j2_4072_eq_j1_4064]; exact hv_u3_2
  -- j=2 max spec
  have J2 := divK_loop_body_n1_max_unified_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q2_old base
    hv_j hv_n1 hv_uhi_2 hv_ulo_2 hv_vtop hv_v0 hv_u0_2 hv_v1 hv_u1_2 hv_v2 hv_u2_2 hv_v3 hv_u3_2 hv_u4_2 hv_q2
    hbltu_2
  intro_lets at J2
  -- Frame j=2 with iter10 extra atoms and scratch
  have J2f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1_old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0_old) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J2
  -- iter10 unified spec (inputs from j=2 max output)
  have H10 := divK_loop_n1_iter10_unified_spec bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop
    hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    hbltu_1 hbltu_0
  -- Frame iter10 with j=2 carried atoms
  have H10f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  -- Compose j=2 and iter10
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 at hp
      delta loopN1Iter10PreWithScratch loopN1Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' : (2 : Word) + signExtend12 4095 = (1 : Word) := by decide
      rw [hj', u_n1_j2_0_eq_j1_4088 sp, u_n1_j2_4088_eq_j1_4080 sp,
          u_n1_j2_4080_eq_j1_4072 sp, u_n1_j2_4072_eq_j1_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by delta loopN1Iter210PreWithScratch loopN1Iter210Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210Post loopN1Iter10Post at hp ⊢
      simp only [iterN1_false] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Three-iteration composition when j=2 is call (bltu_2 = true).
    Composes j=2 call spec with the 2-iteration iter10 unified spec. -/
theorem divK_loop_n1_call_iter10_spec (bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     q2_old q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_2 : BitVec.ult u1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1 v0) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN1Iter210PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 q2_old q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1Iter210Post true bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 ret_mem d_mem dlo_mem scratch_un0) := by
  let r2 := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- Derive j=1 validity
  have hv_u1_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_n1_j2_0_eq_j1_4088]; exact hv_u0_2
  have hv_u2_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_n1_j2_4088_eq_j1_4080]; exact hv_u1_2
  have hv_u3_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_n1_j2_4080_eq_j1_4072]; exact hv_u2_2
  have hv_u4_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_n1_j2_4072_eq_j1_4064]; exact hv_u3_2
  -- j=2 call spec (includes scratch)
  have J2 := divK_loop_body_n1_call_unified_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q2_old ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi_2 hv_ulo_2 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_u0_2 hv_v1 hv_u1_2 hv_v2 hv_u2_2 hv_v3 hv_u3_2 hv_u4_2 hv_q2
    hbltu_2
  intro_lets at J2
  -- Frame j=2 with iter10 extra atoms only (scratch consumed by call)
  have J2f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1_old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J2
  -- iter10 unified spec (inputs from j=2 call output, scratch = j=2 call values)
  have H10 := divK_loop_n1_iter10_unified_spec bltu_1 bltu_0
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    u0_orig_0 q1_old q0_old
    (base + 516) v0 (div128DLo v0) (div128Un0 u0) base
    hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop
    hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    hbltu_1 hbltu_0
  -- Frame iter10 with j=2 carried atoms
  have H10f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) H10
  -- Compose j=2 and iter10
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN1Call loopExitPostN1 at hp
      delta loopN1Iter10PreWithScratch loopN1Iter10Pre at ⊢
      simp only [] at hp ⊢
      have hj' : (2 : Word) + signExtend12 4095 = (1 : Word) := by decide
      rw [hj', u_n1_j2_0_eq_j1_4088 sp, u_n1_j2_4088_eq_j1_4080 sp,
          u_n1_j2_4080_eq_j1_4072 sp, u_n1_j2_4072_eq_j1_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f H10f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by delta loopN1Iter210PreWithScratch loopN1Iter210Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210Post loopN1Iter10Post at hp ⊢
      simp only [iterN1_true] at hp ⊢
      cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

-- ============================================================================
-- Three-iteration unified dispatch: cases bltu_2
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified n=1 three-iteration loop composition, parameterized by
    `(bltu_2 bltu_1 bltu_0 : Bool)`.  Covers all 8 path combinations.
    Dispatches to divK_loop_n1_max_iter10_spec / divK_loop_n1_call_iter10_spec. -/
theorem divK_loop_n1_iter210_unified_spec (bltu_2 bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_1 u0_orig_0
     q2_old q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_2 : bltu_2 = BitVec.ult u1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1 v0) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN1Iter210PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 q2_old q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1Iter210Post bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_1 u0_orig_0 ret_mem d_mem dlo_mem scratch_un0) := by
  cases bltu_2 <;> simp only [iterN1_true, iterN1_false] at hbltu_1 hbltu_0
  · -- bltu_2 = false -> max
    have hbltu_2' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_2.symm]; decide
    exact divK_loop_n1_max_iter10_spec bltu_1 bltu_0
      sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig_1 u0_orig_0 q2_old q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_2 hv_ulo_2 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_2 hv_u1_2 hv_u2_2 hv_u3_2 hv_u4_2 hv_q2
      hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_2' hbltu_1 hbltu_0
  · -- bltu_2 = true -> call
    have hbltu_2' : BitVec.ult u1 v0 := hbltu_2.symm ▸ rfl
    exact divK_loop_n1_call_iter10_spec bltu_1 bltu_0
      sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig_1 u0_orig_0 q2_old q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_2 hv_ulo_2 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_2 hv_u1_2 hv_u2_2 hv_u3_2 hv_u4_2 hv_q2
      hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_2' hbltu_1 hbltu_0

-- ============================================================================
-- Full four-iteration: compose j=3 with iter210 -- separate lemmas per case
-- Postcondition uses @[irreducible] loopN1UnifiedPost
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Four-iteration composition when j=3 is max (bltu_3 = false).
    Composes j=3 max spec with the 3-iteration iter210 unified spec. -/
theorem divK_loop_n1_max_iter210_spec (bltu_2 bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_2 u0_orig_1 u0_orig_0
     q3_old q2_old q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_3 : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_3 : ¬BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.2.2.1).2.1 v0) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN1PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_2 u0_orig_1 u0_orig_0 q3_old q2_old q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1UnifiedPost false bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_2 u0_orig_1 u0_orig_0 ret_mem d_mem dlo_mem scratch_un0) := by
  let r3 := iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- Derive j=2 validity via j=3->j=2 address linking
  have hv_u1_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_n1_j3_0_eq_j2_4088]; exact hv_u0_3
  have hv_u2_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_n1_j3_4088_eq_j2_4080]; exact hv_u1_3
  have hv_u3_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_n1_j3_4080_eq_j2_4072]; exact hv_u2_3
  have hv_u4_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_n1_j3_4072_eq_j2_4064]; exact hv_u3_3
  -- j=3 max spec
  have J3 := divK_loop_body_n1_max_unified_j3_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q3_old base
    hv_j hv_n1 hv_uhi_3 hv_ulo_3 hv_vtop hv_v0 hv_u0_3 hv_v1 hv_u1_3 hv_v2 hv_u2_3 hv_v3 hv_u3_3 hv_u4_3 hv_q3
    hbltu_3
  intro_lets at J3
  -- Frame j=3 with iter210 extra atoms and scratch
  have J3f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2_old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1_old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0_old) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J3
  -- iter210 unified spec (inputs from j=3 max output)
  have H210 := divK_loop_n1_iter210_unified_spec bltu_2 bltu_1 bltu_0
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old
    ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi_2 hv_ulo_2 hv_vtop
    hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_2 hv_u1_2 hv_u2_2 hv_u3_2 hv_u4_2 hv_q2
    hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    hbltu_2 hbltu_1 hbltu_0
  -- Frame iter210 with j=3 carried atoms
  have H210f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) H210
  -- Compose j=3 and iter210
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN1Max loopExitPostN1 at hp
      delta loopN1Iter210PreWithScratch loopN1Iter210Pre at ⊢
      simp only [] at hp ⊢
      have hj' : (3 : Word) + signExtend12 4095 = (2 : Word) := by decide
      rw [hj', u_n1_j3_0_eq_j2_4088 sp, u_n1_j3_4088_eq_j2_4080 sp,
          u_n1_j3_4080_eq_j2_4072 sp, u_n1_j3_4072_eq_j2_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f H210f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by delta loopN1PreWithScratch loopN1Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPost loopN1Iter210Post at hp ⊢
      simp only [iterN1_false] at hp ⊢
      have hr3 : r3 = iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top := rfl
      have hub3 : u_base_3 = sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      have hqa3 : q_addr_3 = sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      simp only [hr3, hub3, hqa3] at hp
      rw [sepConj_assoc'] at hp
      cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;> (simp only [sepConj_emp_right'] at hp ⊢; xperm_hyp hp))
    full

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Four-iteration composition when j=3 is call (bltu_3 = true).
    Composes j=3 call spec with the 3-iteration iter210 unified spec. -/
theorem divK_loop_n1_call_iter210_spec (bltu_2 bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_2 u0_orig_1 u0_orig_0
     q3_old q2_old q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_3 : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_3 : BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.2.2.1).2.1 v0) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN1PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_2 u0_orig_1 u0_orig_0 q3_old q2_old q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1UnifiedPost true bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_2 u0_orig_1 u0_orig_0 ret_mem d_mem dlo_mem scratch_un0) := by
  let r3 := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- Derive j=2 validity
  have hv_u1_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true := by
    rw [← u_n1_j3_0_eq_j2_4088]; exact hv_u0_3
  have hv_u2_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true := by
    rw [← u_n1_j3_4088_eq_j2_4080]; exact hv_u1_3
  have hv_u3_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true := by
    rw [← u_n1_j3_4080_eq_j2_4072]; exact hv_u2_3
  have hv_u4_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true := by
    rw [← u_n1_j3_4072_eq_j2_4064]; exact hv_u3_3
  -- j=3 call spec (includes scratch)
  have J3 := divK_loop_body_n1_call_unified_j3_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q3_old ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n1 hv_uhi_3 hv_ulo_3 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_u0_3 hv_v1 hv_u1_3 hv_v2 hv_u2_3 hv_v3 hv_u3_3 hv_u4_3 hv_q3
    hbltu_3
  intro_lets at J3
  -- Frame j=3 with iter210 extra atoms only (scratch consumed by call)
  have J3f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2_old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1_old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J3
  -- iter210 unified spec (inputs from j=3 call output, scratch = j=3 call values)
  have H210 := divK_loop_n1_iter210_unified_spec bltu_2 bltu_1 bltu_0
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0_orig_1 u0_orig_0
    q2_old q1_old q0_old
    (base + 516) v0 (div128DLo v0) (div128Un0 u0) base
    hv_j hv_n1 hv_uhi_2 hv_ulo_2 hv_vtop
    hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_2 hv_u1_2 hv_u2_2 hv_u3_2 hv_u4_2 hv_q2
    hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    hbltu_2 hbltu_1 hbltu_0
  -- Frame iter210 with j=3 carried atoms
  have H210f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) H210
  -- Compose j=3 and iter210
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN1Call loopExitPostN1 at hp
      delta loopN1Iter210PreWithScratch loopN1Iter210Pre at ⊢
      simp only [] at hp ⊢
      have hj' : (3 : Word) + signExtend12 4095 = (2 : Word) := by decide
      rw [hj', u_n1_j3_0_eq_j2_4088 sp, u_n1_j3_4088_eq_j2_4080 sp,
          u_n1_j3_4080_eq_j2_4072 sp, u_n1_j3_4072_eq_j2_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f H210f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by delta loopN1PreWithScratch loopN1Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPost loopN1Iter210Post at hp ⊢
      simp only [iterN1_true] at hp ⊢
      have hr3 : r3 = iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := rfl
      have hub3 : u_base_3 = sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      have hqa3 : q_addr_3 = sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      simp only [hr3, hub3, hqa3] at hp
      rw [sepConj_assoc'] at hp
      cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;> (simp only [sepConj_emp_right'] at hp ⊢; xperm_hyp hp))
    full

-- ============================================================================
-- Final unified dispatch: cases bltu_3, delegates to max/call lemmas
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified n=1 four-iteration loop composition, parameterized by
    `(bltu_3 bltu_2 bltu_1 bltu_0 : Bool)`.  Covers all 16 path combinations.
    Dispatches to divK_loop_n1_max_iter210_spec / divK_loop_n1_call_iter210_spec. -/
theorem divK_loop_n1_unified_spec (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top
     u0_orig_2 u0_orig_1 u0_orig_0
     q3_old q2_old q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_3 : isValidDwordAccess (sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u0_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_u1_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_u2_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_u3_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4_3 : isValidDwordAccess ((sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (1 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu_3 : bltu_3 = BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1).2.2.2.2.1).2.1 v0) :
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      (loopN1PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_2 u0_orig_1 u0_orig_0 q3_old q2_old q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top
        u0_orig_2 u0_orig_1 u0_orig_0 ret_mem d_mem dlo_mem scratch_un0) := by
  cases bltu_3 <;> simp only [iterN1_true, iterN1_false] at hbltu_2 hbltu_1 hbltu_0
  · -- bltu_3 = false -> max
    have hbltu_3' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_3.symm]; decide
    exact divK_loop_n1_max_iter210_spec bltu_2 bltu_1 bltu_0
      sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig_2 u0_orig_1 u0_orig_0
      q3_old q2_old q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_3 hv_ulo_3 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_3 hv_u1_3 hv_u2_3 hv_u3_3 hv_u4_3 hv_q3
      hv_uhi_2 hv_ulo_2 hv_u0_2 hv_q2
      hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_3' hbltu_2 hbltu_1 hbltu_0
  · -- bltu_3 = true -> call
    have hbltu_3' : BitVec.ult u1 v0 := hbltu_3.symm ▸ rfl
    exact divK_loop_n1_call_iter210_spec bltu_2 bltu_1 bltu_0
      sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig_2 u0_orig_1 u0_orig_0
      q3_old q2_old q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_3 hv_ulo_3 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_3 hv_u1_3 hv_u2_3 hv_u3_3 hv_u4_3 hv_q3
      hv_uhi_2 hv_ulo_2 hv_u0_2 hv_q2
      hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_3' hbltu_2 hbltu_1 hbltu_0

end EvmAsm.Evm64
