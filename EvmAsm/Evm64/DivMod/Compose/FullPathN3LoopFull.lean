/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopFull

  Unified full n=3 DIV path (shift ≠ 0, base → base+1068).
  Dispatches to the 4 existing per-path theorems in FullPathN3Loop.lean.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Unified full path postcondition for n=3 (all 4 path combinations)
-- ============================================================================

/-- Unified full path postcondition for n=3 DIV (shift ≠ 0).
    Uses `iterN3` (reduces to `iterN3Max`/`iterN3Call` for concrete bools).
    Scratch cells: none for max×max; div128 scratch for others. -/
@[irreducible]
def fullDivN3UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b2).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (anti_shift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let r1 := iterN3 bltu_1 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
  let r0 := iterN3 bltu_0 b0' b1' b2' b3' u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 0 0 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | true, true =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b2') **
    (sp + signExtend12 3952 ↦ₘ div128DLo b2') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.2.1)
  | false, true =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b2') **
    (sp + signExtend12 3952 ↦ₘ div128DLo b2') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.2.1)
  | true, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b2') **
    (sp + signExtend12 3952 ↦ₘ div128DLo b2') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u3)

-- ============================================================================
-- Bridge lemmas: fullDivN3UnifiedPost concrete_bools = fullDivN3_XXX_Post
-- Separate lemmas for heartbeat isolation.
-- ============================================================================

-- For (F,F), fullDivN3UnifiedPost includes scratch cells but fullDivN3MaxMaxPost does not.
-- The bridge is: fullDivN3UnifiedPost FF = fullDivN3MaxMaxPost ** scratch_cells.
-- This is used in the dispatch via cpsTriple_frame_left + consequence.

theorem fullDivN3UnifiedPost_FT_eq (sp base a0 a1 a2 a3 b0 b1 b2 b3
    ret_mem d_mem dlo_mem scratch_un0 : Word) :
    fullDivN3UnifiedPost false true sp base a0 a1 a2 a3 b0 b1 b2 b3
      ret_mem d_mem dlo_mem scratch_un0 =
    fullDivN3MaxCallPost sp base a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN3UnifiedPost fullDivN3MaxCallPost; simp only [iterN3_false, iterN3_true]

theorem fullDivN3UnifiedPost_TF_eq (sp base a0 a1 a2 a3 b0 b1 b2 b3
    ret_mem d_mem dlo_mem scratch_un0 : Word) :
    fullDivN3UnifiedPost true false sp base a0 a1 a2 a3 b0 b1 b2 b3
      ret_mem d_mem dlo_mem scratch_un0 =
    fullDivN3CallMaxPost sp base a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN3UnifiedPost fullDivN3CallMaxPost; simp only [iterN3_false, iterN3_true]

theorem fullDivN3UnifiedPost_TT_eq (sp base a0 a1 a2 a3 b0 b1 b2 b3
    ret_mem d_mem dlo_mem scratch_un0 : Word) :
    fullDivN3UnifiedPost true true sp base a0 a1 a2 a3 b0 b1 b2 b3
      ret_mem d_mem dlo_mem scratch_un0 =
    fullDivN3CallCallPost sp base a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN3UnifiedPost fullDivN3CallCallPost; simp only [iterN3_true]

-- ============================================================================
-- Unified full n=3 DIV path (shift≠0): base → base+1068
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 25600000 in
/-- Unified full n=3 DIV path (shift ≠ 0), covering all 4 path combinations.
    Dispatches to per-path theorems via postcondition bridge. -/
theorem evm_div_n3_full_unified_spec (bltu_1 bltu_0 : Bool) (sp base : Word)
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
    cpsTriple base (base + 1068) (divCode base)
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
      (fullDivN3UnifiedPost bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        ret_mem d_mem dlo_mem scratch_un0) := by
  cases bltu_1 <;> cases bltu_0 <;>
    simp only [isTrialN3_j1, isTrialN3_j0] at hbltu_1 hbltu_0
  · -- (F,F) max×max: frame scratch cells (max×max theorem doesn't have them)
    have hMM := evm_div_n3_full_max_max_spec sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
      q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
      hbnz hb3z hb2nz hshift_nz hvalid
      hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
      hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hbltu_1 hbltu_0
    have hMMF := cpsTriple_frame_left _ _ _ _ _
      ((sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) hMM
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by
        delta fullDivN3MaxMaxPost at hq
        delta fullDivN3UnifiedPost; simp only [iterN3_false]
        xperm_hyp hq)
      hMMF
  · -- (F,T) max×call
    rw [fullDivN3UnifiedPost_FT_eq]; exact evm_div_n3_full_max_call_spec sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
      q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
      ret_mem d_mem dlo_mem scratch_un0
      hbnz hb3z hb2nz hshift_nz hvalid
      hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
      hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j
      hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu_1 hbltu_0
  · -- (T,F) call×max
    rw [fullDivN3UnifiedPost_TF_eq]; exact evm_div_n3_full_call_max_spec sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
      q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
      ret_mem d_mem dlo_mem scratch_un0
      hbnz hb3z hb2nz hshift_nz hvalid
      hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
      hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j
      hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu_1 hbltu_0
  · -- (T,T) call×call
    rw [fullDivN3UnifiedPost_TT_eq]; exact evm_div_n3_full_call_call_spec sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
      q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
      ret_mem d_mem dlo_mem scratch_un0
      hbnz hb3z hb2nz hshift_nz hvalid
      hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
      hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j
      hv_ret hv_d hv_dlo hv_scratch_un0 halign hbltu_1 hbltu_0

end EvmAsm.Evm64
