/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

  Bool-parameterized unified preloop+loop composition for n=3.
  Issue #262: Single theorem covers all 4 path combinations at the
  preloop+loop level (base → base+904).

  Dispatches to the existing 4 per-path theorems in FullPathN3Loop.lean.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Unified condition predicates
-- ============================================================================

/-- Unified j=1 trial condition: `bltu_1 = true` means call (BLTU taken),
    `bltu_1 = false` means max (BLTU not taken). -/
def isTrialN3_j1 (bltu : Bool) (a3 b1 b2 : Word) : Prop :=
  match bltu with
  | false => isMaxTrialN3_j1 a3 b1 b2
  | true => isCallTrialN3_j1 a3 b1 b2

/-- Unified j=0 trial condition, dependent on j=1 path. -/
def isTrialN3_j0 (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  match bltu_1, bltu_0 with
  | false, false => isMaxTrialN3_j0 a0 a1 a2 a3 b0 b1 b2 b3
  | false, true  => isCallTrialN3_j0_afterMax a0 a1 a2 a3 b0 b1 b2 b3
  | true,  false => isMaxTrialN3_j0_afterCall a0 a1 a2 a3 b0 b1 b2 b3
  | true,  true  => isCallTrialN3_j0_afterCall a0 a1 a2 a3 b0 b1 b2 b3

-- ============================================================================
-- Unified preloop+loop postcondition
-- ============================================================================

/-- Unified postcondition for preloop+loop at n=3.
    All variants share the same shift/denorm computation and framing atoms,
    differing only in which loop postcondition they use.
    For max×max, scratch cells pass through (carried as parameters).
    For other variants, scratch cells are overwritten by div128 (params unused). -/
@[irreducible]
def preloopN3UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  match bltu_1, bltu_0 with
  | false, false =>
    preloopN3MaxMaxPost sp a0 a1 a2 a3 b0 b1 b2 b3 **
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | true,  true  => preloopN3CallCallPost sp base a0 a1 a2 a3 b0 b1 b2 b3
  | false, true  => preloopN3MaxCallPost sp base a0 a1 a2 a3 b0 b1 b2 b3
  | true,  false => preloopN3CallMaxPost sp base a0 a1 a2 a3 b0 b1 b2 b3

-- ============================================================================
-- Unified preloop+loop composition (base → base+904)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified preloop+loop for n=3, parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max×max, call×call, max×call, call×max).
    Precondition always includes scratch cells.
    Dispatches to existing per-path theorems via cases. -/
theorem evm_div_n3_preloop_loop_unified_spec (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true)
    (hv_u4 : isValidDwordAccess (sp + signExtend12 4024) = true)
    (hv_u5 : isValidDwordAccess (sp + signExtend12 4016) = true)
    (hv_u6 : isValidDwordAccess (sp + signExtend12 4008) = true)
    (hv_u7 : isValidDwordAccess (sp + signExtend12 4000) = true)
    (hv_n  : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_j  : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_1 : isTrialN3_j1 bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 908) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11_old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0_old) ** ((sp + signExtend12 4048) ↦ₘ u1_old) **
       ((sp + signExtend12 4040) ↦ₘ u2_old) ** ((sp + signExtend12 4032) ↦ₘ u3_old) **
       ((sp + signExtend12 4024) ↦ₘ u4_old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ n_mem) **
       ((sp + signExtend12 3992) ↦ₘ shift_mem) **
       ((sp + signExtend12 3976) ↦ₘ j_mem) **
       ((sp + signExtend12 3968) ↦ₘ ret_mem) **
       ((sp + signExtend12 3960) ↦ₘ d_mem) **
       ((sp + signExtend12 3952) ↦ₘ dlo_mem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0))
      (preloopN3UnifiedPost bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        ret_mem d_mem dlo_mem scratch_un0) := by
  cases bltu_1 <;> cases bltu_0 <;> simp only [isTrialN3_j1, isTrialN3_j0] at hbltu_1 hbltu_0
  · -- (false, false) = max×max: frame scratch, dispatch to existing
    have hMM := evm_div_n3_preloop_max_max_spec sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
      q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
      hbnz hb3z hb2nz hshift_nz hvalid
      hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
      hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j
      hbltu_1 hbltu_0
    have hMMF := cpsTriple_frame_left _ _ _ _ _
      ((sp + signExtend12 3968 ↦ₘ ret_mem) **
       (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) hMM
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by delta preloopN3UnifiedPost; xperm_hyp hp)
      hMMF
  · -- (false, true) = max×call: precondition matches exactly
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by delta preloopN3UnifiedPost; exact hp)
      (evm_div_n3_preloop_max_call_spec sp base
        a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
        q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
        ret_mem d_mem dlo_mem scratch_un0
        hbnz hb3z hb2nz hshift_nz hvalid
        hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
        hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j
        hv_ret hv_d hv_dlo hv_scratch_un0 halign
        hbltu_1 hbltu_0)
  · -- (true, false) = call×max: precondition matches exactly
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by delta preloopN3UnifiedPost; exact hp)
      (evm_div_n3_preloop_call_max_spec sp base
        a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
        q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
        ret_mem d_mem dlo_mem scratch_un0
        hbnz hb3z hb2nz hshift_nz hvalid
        hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
        hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j
        hv_ret hv_d hv_dlo hv_scratch_un0 halign
        hbltu_1 hbltu_0)
  · -- (true, true) = call×call: precondition matches exactly
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by delta preloopN3UnifiedPost; exact hp)
      (evm_div_n3_preloop_call_call_spec sp base
        a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
        q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
        ret_mem d_mem dlo_mem scratch_un0
        hbnz hb3z hb2nz hshift_nz hvalid
        hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
        hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j
        hv_ret hv_d hv_dlo hv_scratch_un0 halign
        hbltu_1 hbltu_0)

end EvmAsm.Evm64
