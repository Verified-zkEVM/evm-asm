/-
  EvmAsm.Evm64.DivMod.LoopUnifiedN3

  Bool-parameterized (unified) loop composition for n=3.
  Issue #262: Unify max/call branch paths via Bool parameter.

  Instead of 4 separate two-iteration composition theorems (max×max, call×call,
  max×call, call×max), this file provides a single theorem parameterized by
  `(bltu_1 bltu_0 : Bool)` that covers all 4 combinations.

  The proofs delegate to the existing per-path theorems in LoopComposeN3.lean
  via `cases bltu`, then bridge the pre/postconditions to the unified forms.
-/

import EvmAsm.Evm64.DivMod.LoopComposeN3

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Unified two-iteration composition (Bool×Bool parameterized)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified n=3 two-iteration loop composition, parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max×max, call×call, max×call, call×max).
    Precondition always includes scratch cells (loopN3PreWithScratch).
    Postcondition is loopN3UnifiedPost which delegates to existing per-path defs. -/
theorem divK_loop_n3_unified_spec (bltu_1 bltu_0 : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    -- Validity hypotheses (union of max and call requirements)
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
    -- Unified branch conditions
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN3 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 908) (sharedDivModCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3UnifiedPost bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig
        ret_mem d_mem dlo_mem scratch_un0) := by
  -- Dispatch to existing per-path composition theorems
  cases bltu_1 <;> cases bltu_0 <;> simp only [iterN3_true, iterN3_false] at hbltu_0
  · -- (false, false) = max×max
    have hbltu_1' : ¬BitVec.ult u3 v2 := by
      rw [show BitVec.ult u3 v2 = false from hbltu_1.symm]; decide
    have hbltu_0' : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2 := by
      rw [show BitVec.ult _ v2 = false from hbltu_0.symm]; decide
    have hMM := divK_loop_n3_max_max_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_1' hbltu_0'
    -- Frame scratch cells (max path doesn't touch them)
    have hMMF := cpsTriple_frame_left _ _ _ _ _
      ((sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) hMM
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by delta loopN3PreWithScratch at hp; xperm_hyp hp)
      (fun h hp => by delta loopN3UnifiedPost; xperm_hyp hp)
      hMMF
  · -- (false, true) = max×call
    have hbltu_1' : ¬BitVec.ult u3 v2 := by
      rw [show BitVec.ult u3 v2 = false from hbltu_1.symm]; decide
    have hbltu_0' : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2 :=
      hbltu_0.symm ▸ rfl
    have hMC := divK_loop_n3_max_call_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop
      hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_1' hbltu_0'
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by delta loopN3UnifiedPost; exact hp)
      hMC
  · -- (true, false) = call×max
    have hbltu_1' : BitVec.ult u3 v2 := hbltu_1.symm ▸ rfl
    have hbltu_0' : ¬BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2 := by
      rw [show BitVec.ult _ v2 = false from hbltu_0.symm]; decide
    have hCM := divK_loop_n3_call_max_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop
      hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_1' hbltu_0'
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by delta loopN3UnifiedPost; exact hp)
      hCM
  · -- (true, true) = call×call
    have hbltu_1' : BitVec.ult u3 v2 := hbltu_1.symm ▸ rfl
    have hbltu_0' : BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2 :=
      hbltu_0.symm ▸ rfl
    have hCC := divK_loop_n3_call_call_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop
      hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
      hbltu_1' hbltu_0'
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by delta loopN3UnifiedPost; exact hp)
      hCC

end EvmAsm.Evm64
