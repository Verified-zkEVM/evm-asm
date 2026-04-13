/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Shift0

  Full n=2 DIV path composition for the shift=0 case:
  pre-loop → 3-iteration loop → shift=0 epilogue.
  Composes base → base+1064 for the b[3]=b[2]=0, b[1]≠0, shift=0 case.

  When shift=0, normalization is identity (v=b, u=a, u4=0).
  Since u4=0 < b1 (b1≠0), the j=2 BLTU condition is always taken → call path.
  j=1 and j=0 can be either call or max.
  Unified theorem with (bltu_1 bltu_0 : Bool) covers all 4 combinations.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPath
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Condition predicates for n=2 shift=0 (j=2 always call, j=1/j=0 vary)
-- ============================================================================

/-- j=1 trial condition for n=2 shift=0: after j=2 call, check if
    updated u2 < b1 (the top v-limb for n=2). -/
def isTrialN2Shift0_j1 (bltu_1 : Bool) (a2 a3 b0 b1 : Word) : Prop :=
  bltu_1 = BitVec.ult
    (iterN2Call b0 b1 (0 : Word) (0 : Word) a2 a3 (0 : Word) (0 : Word) (0 : Word)).2.2.1 b1

/-- j=0 trial condition for n=2 shift=0: after j=2 call + j=1 result,
    check if updated u2 < b1. -/
def isTrialN2Shift0_j0 (bltu_1 bltu_0 : Bool) (a1 a2 a3 b0 b1 : Word) : Prop :=
  let r2 := iterN2Call b0 b1 (0 : Word) (0 : Word) a2 a3 (0 : Word) (0 : Word) (0 : Word)
  bltu_0 = BitVec.ult
    (iterN2 bltu_1 b0 b1 (0 : Word) (0 : Word) a1
      r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1).2.2.1 b1

-- ============================================================================
-- Loop instantiation helper (heartbeat isolation)
-- ============================================================================

/-- Lift the unified n=2 3-iteration loop to divCode for shift=0.
    Passes bltu_2=true (always call at j=2 since u4=0 < b1). -/
private theorem divK_loop_n2_shift0_inst (bltu_1 bltu_0 : Bool)
    (sp base : Word)
    (clz_hi v11_old j_mem : Word)
    (a0 a1 a2 a3 b0 b1 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi_2 : isValidDwordAccess (sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
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
    (hv_uhi_1 : isValidDwordAccess (sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hv_uhi_0 : isValidDwordAccess (sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_u0_0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hb1nz : b1 ≠ 0)
    (hbltu_1 : isTrialN2Shift0_j1 bltu_1 a2 a3 b0 b1)
    (hbltu_0 : isTrialN2Shift0_j0 bltu_1 bltu_0 a1 a2 a3 b0 b1) :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN2PreWithScratch sp j_mem (2 : Word) (0 : Word)
        clz_hi (0 : Word) v11_old (0 : Word)
        b0 b1 (0 : Word) (0 : Word)
        a2 a3 (0 : Word) (0 : Word) (0 : Word)
        a1 a0 (0 : Word) (0 : Word) (0 : Word)
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN2UnifiedPost true bltu_1 bltu_0 sp base
        b0 b1 (0 : Word) (0 : Word)
        a2 a3 (0 : Word) (0 : Word) (0 : Word)
        a1 a0 ret_mem d_mem dlo_mem scratch_un0) := by
  unfold isTrialN2Shift0_j1 at hbltu_1
  unfold isTrialN2Shift0_j0 at hbltu_0
  exact divK_loop_n2_unified_divCode true bltu_1 bltu_0
    sp j_mem (2 : Word) (0 : Word) clz_hi (0 : Word) v11_old (0 : Word)
    b0 b1 (0 : Word) (0 : Word)
    a2 a3 (0 : Word) (0 : Word) (0 : Word)
    a1 a0 (0 : Word) (0 : Word) (0 : Word)
    ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n hv_uhi_2 hv_ulo_2 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_2 hv_u1_2 hv_u2_2 hv_u3_2 hv_u4_2 hv_q2
    hv_uhi_1 hv_ulo_1 hv_u0_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    (Eq.symm (ult_zero_of_ne hb1nz)) hbltu_1 hbltu_0

-- ============================================================================
-- Preloop postcondition for shift=0 (unified)
-- ============================================================================

/-- Preloop+loop postcondition for n=2 shift=0, unified over (bltu_1 bltu_0 : Bool).
    Wraps loopN2UnifiedPost with shift=0 values plus frame atoms. -/
@[irreducible]
def preloopN2Shift0Post (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  loopN2UnifiedPost true bltu_1 bltu_0 sp base
    b0 b1 (0 : Word) (0 : Word)
    a2 a3 (0 : Word) (0 : Word) (0 : Word)
    a1 a0 ret_mem d_mem dlo_mem scratch_un0 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word))

-- ============================================================================
-- Preloop + loop composition (shift=0): base → base+904
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified preloop+loop for n=2 shift=0, parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (j=2 always call). -/
theorem evm_div_n2_preloop_shift0_spec
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0)
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
    (hbltu_1 : isTrialN2Shift0_j1 bltu_1 a2 a3 b0 b1)
    (hbltu_0 : isTrialN2Shift0_j0 bltu_1 bltu_0 a1 a2 a3 b0 b1) :
    cpsTriple base (base + 904) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
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
       (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (preloopN2Shift0Post bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
        ret_mem d_mem dlo_mem scratch_un0) := by
  -- 1. Pre-loop spec: base → base+448 (shift=0)
  have hPre := evm_div_n2_shift0_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3z hb2z hb1nz hshift_z hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift
  have hPreF := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11_old) ** ((sp + signExtend12 3976) ↦ₘ j_mem) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- 2. Loop spec via helper
  have hLoop := divK_loop_n2_shift0_inst bltu_1 bltu_0 sp base
    ((clzResult b1).2 >>> (63 : Nat)) v11_old j_mem a0 a1 a2 a3 b0 b1
    ret_mem d_mem dlo_mem scratch_un0
    hv_j hv_n
    (by rw [n2_uhi_2_addr]; exact hv_u4) (by rw [n2_ulo_2_addr]; exact hv_u3)
    (by rw [n2_vtop_addr, se12_40]; exact hvalid 5 (by omega))
    hv_ret hv_d hv_dlo hv_scratch_un0 halign
    (by rw [se12_32]; exact hvalid 4 (by omega))
    (by rw [se12_40]; exact hvalid 5 (by omega))
    (by rw [se12_48]; exact hvalid 6 (by omega))
    (by rw [se12_56]; exact hvalid 7 (by omega))
    (by rw [n2_ub2_off0]; exact hv_u2) (by rw [n2_ub2_off4088]; exact hv_u3)
    (by rw [n2_ub2_off4080]; exact hv_u4) (by rw [n2_ub2_off4072]; exact hv_u5)
    (by rw [n2_ub2_off4064]; exact hv_u6) (by rw [n2_qa2]; exact hv_q2)
    (by rw [n2_uhi_1_addr]; exact hv_u3) (by rw [n2_ulo_1_addr]; exact hv_u2)
    (by rw [n3_ub1_off0]; exact hv_u1) (by rw [n3_qa1]; exact hv_q1)
    (by rw [n2_uhi_0_addr]; exact hv_u2) (by rw [n2_ulo_0_addr]; exact hv_u1)
    (by rw [n3_ub0_off0]; exact hv_u0) (by rw [n3_qa0]; exact hv_q0)
    hb1nz hbltu_1 hbltu_0
  -- Frame loop with a[], spare q3, spare u7, shift_mem
  have hLoopF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      simp only [x1_val_n2, hshift_z, hb3z, hb2z,
        show signExtend12 (0 : BitVec 12) - (0 : Word) = (0 : Word) from by decide] at hp
      delta loopN2PreWithScratch loopN2Pre
      simp only []
      simp only [n2_ub2_off0 sp, n2_ub2_off4088 sp, n2_ub2_off4080 sp,
                  n2_ub2_off4072 sp, n2_ub2_off4064 sp,
                  n3_ub1_off0 sp,
                  n3_ub0_off0 sp,
                  n2_qa2 sp, n3_qa1 sp, n3_qa0 sp,
                  se12_32, se12_40, se12_48, se12_56, hshift_z]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN2Shift0Post; simp only [hshift_z] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Full path postcondition for n=2 DIV (shift=0, unified)
-- ============================================================================

/-- Full path postcondition for n=2 DIV (shift=0, unified).
    When shift=0, the denorm body is skipped (BEQ taken), so u-cells and x2
    preserve their loop-exit values. j=2 is always call. -/
@[irreducible]
def fullDivN2Shift0UnifiedPost (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 : Word) : Assertion :=
  let r2 := iterN2Call b0 b1 (0 : Word) (0 : Word) a2 a3 (0 : Word) (0 : Word) (0 : Word)
  let r1 := iterN2 bltu_1 b0 b1 (0 : Word) (0 : Word) a1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN2 bltu_0 b0 b1 (0 : Word) (0 : Word) a0
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  -- Epilogue output (shift=0: denorm body skipped, x2 preserved from loop)
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0.1) ** (.x6 ↦ᵣ r1.1) ** (.x7 ↦ᵣ r2.1) **
  (.x2 ↦ᵣ r0.2.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) ** ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ r2.1) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + 32) ↦ₘ r0.1) ** ((sp + 40) ↦ₘ r1.1) **
  ((sp + 48) ↦ₘ r2.1) ** ((sp + 56) ↦ₘ (0 : Word)) **
  -- Preserved frame atoms
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4056) ↦ₘ r0.2.1) ** ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
  ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  -- Scratch cells: all 4 cases have call scratch (j=2 is always call)
  match bltu_1, bltu_0 with
  | false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo b1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 a3)
  | false, true =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo b1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)
  | true, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo b1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r2.2.1)
  | true, true =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ b1) **
    (sp + signExtend12 3952 ↦ₘ div128DLo b1) **
    (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.1)

-- ============================================================================
-- Shift=0 epilogue helper (parametric, short WHNF)
-- ============================================================================

/-- Shift=0 epilogue helper for n=2. Takes r0/r1/r2 as explicit params (short WHNF).
    Precondition atom order matches preloopN2Shift0Post's unfolded form,
    so the perm callback is cheap. -/
private theorem evm_div_n2_shift0_denorm' (sp base : Word)
    (r0_un0 r0_un1 r0_un2 r0_un3 r0_u4 r0_q : Word)
    (r1_q r1_u4 : Word) (c3_0 : Word)
    (r2_q r2_u4 : Word)
    (scratch_un0_val : Word)
    (a0 a1 a2 a3 b0 b1 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true) :
    cpsTriple (base + 904) (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
       (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3_0) ** (.x11 ↦ᵣ r0_q) **
       (.x2 ↦ᵣ r0_un3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + signExtend12 4056) ↦ₘ r0_un0) **
       ((sp + 40) ↦ₘ b1) ** ((sp + signExtend12 4048) ↦ₘ r0_un1) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4040) ↦ₘ r0_un2) **
       ((sp + 56) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4032) ↦ₘ r0_un3) **
       ((sp + signExtend12 4024) ↦ₘ r0_u4) **
       ((sp + signExtend12 4088) ↦ₘ r0_q) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ b1) **
       (sp + signExtend12 3952 ↦ₘ div128DLo b1) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0_val) **
       ((sp + signExtend12 4016) ↦ₘ r1_u4) ** ((sp + signExtend12 4080) ↦ₘ r1_q) **
       ((sp + signExtend12 4008) ↦ₘ r2_u4) ** ((sp + signExtend12 4072) ↦ₘ r2_q) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (0 : Word)))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0_q) ** (.x6 ↦ᵣ r1_q) ** (.x7 ↦ᵣ r2_q) **
       (.x2 ↦ᵣ r0_un3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4088) ↦ₘ r0_q) ** ((sp + signExtend12 4080) ↦ₘ r1_q) **
       ((sp + signExtend12 4072) ↦ₘ r2_q) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ r0_q) ** ((sp + 40) ↦ₘ r1_q) **
       ((sp + 48) ↦ₘ r2_q) ** ((sp + 56) ↦ₘ (0 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ r0_un0) ** ((sp + signExtend12 4048) ↦ₘ r0_un1) **
       ((sp + signExtend12 4040) ↦ₘ r0_un2) ** ((sp + signExtend12 4032) ↦ₘ r0_un3) **
       ((sp + signExtend12 4024) ↦ₘ r0_u4) **
       ((sp + signExtend12 4016) ↦ₘ r1_u4) **
       ((sp + signExtend12 4008) ↦ₘ r2_u4) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
       (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0_q) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ b1) **
       (sp + signExtend12 3952 ↦ₘ div128DLo b1) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0_val)) := by
  -- Apply shift=0 epilogue (takes 16 atoms), frame with remaining
  have hB := evm_div_shift0_epilogue_spec sp base
    r0_un0 r0_un1 r0_un2 r0_un3
    (0 : Word) r0_un3 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0
    r0_q r1_q r2_q 0
    b0 b1 (0 : Word) (0 : Word)
    rfl hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ r0_un0) ** ((sp + signExtend12 4048) ↦ₘ r0_un1) **
     ((sp + signExtend12 4040) ↦ₘ r0_un2) ** ((sp + signExtend12 4032) ↦ₘ r0_un3) **
     ((sp + signExtend12 4024) ↦ₘ r0_u4) **
     ((sp + signExtend12 4016) ↦ₘ r1_u4) **
     ((sp + signExtend12 4008) ↦ₘ r2_u4) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0_q) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ b1) **
     (sp + signExtend12 3952 ↦ₘ div128DLo b1) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0_val))
    (by pcFree) hB
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hBF

-- ============================================================================
-- Shift=0 epilogue composition (instantiation wrapper)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Denorm composition for shift=0: preloopN2Shift0Post → fullDivN2Shift0UnifiedPost.
    Separate theorem with own heartbeat budget. -/
theorem evm_div_n2_shift0_denorm_comp (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true) :
    cpsTriple (base + 904) (base + 1064) (divCode base)
      (preloopN2Shift0Post bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
        ret_mem d_mem dlo_mem scratch_un0)
      (fullDivN2Shift0UnifiedPost bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1) := by
  let r2 := iterN2Call b0 b1 (0 : Word) (0 : Word) a2 a3 (0 : Word) (0 : Word) (0 : Word)
  -- Case-split on bltu_1/bltu_0 to resolve match in pre/postconditions
  cases bltu_1 <;> cases bltu_0
  · -- (false, false): j=1 max, j=0 max
    let r1 := iterN2Max b0 b1 (0:Word) (0:Word) a1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN2Max b0 b1 (0:Word) (0:Word) a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n2_shift0_denorm' sp base
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) b0 b1 0 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 (div128Un0 a3)
      a0 a1 a2 a3 b0 b1 hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN2Shift0Post loopN2UnifiedPost at hp
        simp only [iterN2_true, iterN2_false,
          loopIterPostN2_max, loopIterPostN2Max, loopExitPostN2_j0_eq,
          n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN2Shift0UnifiedPost; simp only [iterN2_false]; xperm_hyp hq)
      hD
  · -- (false, true): j=1 max, j=0 call
    let r1 := iterN2Max b0 b1 (0:Word) (0:Word) a1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN2Call b0 b1 (0:Word) (0:Word) a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n2_shift0_denorm' sp base
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 b1) b0 b1 0 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 (div128Un0 r1.2.1)
      a0 a1 a2 a3 b0 b1 hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN2Shift0Post loopN2UnifiedPost at hp
        simp only [iterN2_true, iterN2_false,
          loopIterPostN2_call, loopIterPostN2Call, loopExitPostN2_j0_eq,
          n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN2Shift0UnifiedPost; simp only [iterN2_false, iterN2_true]; xperm_hyp hq)
      hD
  · -- (true, false): j=1 call, j=0 max
    let r1 := iterN2Call b0 b1 (0:Word) (0:Word) a1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN2Max b0 b1 (0:Word) (0:Word) a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n2_shift0_denorm' sp base
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) b0 b1 0 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 (div128Un0 r2.2.1)
      a0 a1 a2 a3 b0 b1 hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN2Shift0Post loopN2UnifiedPost at hp
        simp only [iterN2_true,
          loopIterPostN2_max, loopIterPostN2Max, loopExitPostN2_j0_eq,
          n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN2Shift0UnifiedPost; simp only [iterN2_true, iterN2_false]; xperm_hyp hq)
      hD
  · -- (true, true): j=1 call, j=0 call
    let r1 := iterN2Call b0 b1 (0:Word) (0:Word) a1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN2Call b0 b1 (0:Word) (0:Word) a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n2_shift0_denorm' sp base
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 b1) b0 b1 0 0 a0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 (div128Un0 r1.2.1)
      a0 a1 a2 a3 b0 b1 hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN2Shift0Post loopN2UnifiedPost at hp
        simp only [iterN2_true,
          loopIterPostN2_call, loopIterPostN2Call, loopExitPostN2_j0_eq,
          n2_ub2_off4064, n3_ub1_off4064, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN2Shift0UnifiedPost; simp only [iterN2_true]; xperm_hyp hq)
      hD

-- ============================================================================
-- Full n=2 DIV path (shift=0, unified): base → base+1064
-- ============================================================================

/-- Unified full n=2 DIV path (shift=0), covering all 4 path combinations.
    j=2 always call, j=1/j=0 parameterized by bltu_1/bltu_0.
    Composes pre-loop + 3-iteration loop + shift=0 epilogue. -/
theorem evm_div_n2_full_shift0_unified_spec (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_z : (clzResult b1).1 = 0)
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
    (hbltu_1 : isTrialN2Shift0_j1 bltu_1 a2 a3 b0 b1)
    (hbltu_0 : isTrialN2Shift0_j0 bltu_1 bltu_0 a1 a2 a3 b0 b1) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
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
       (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullDivN2Shift0UnifiedPost bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1) := by
  -- 1. Preloop + loop: base → base+904
  have hA := evm_div_n2_preloop_shift0_spec bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_z hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0
    halign hbltu_1 hbltu_0
  -- 2. Denorm composition (separate theorem, own heartbeat budget)
  have hD := evm_div_n2_shift0_denorm_comp bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1
    ret_mem d_mem dlo_mem scratch_un0
    hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
  -- 3. Compose preloop+denorm
  exact cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hA hD

end EvmAsm.Evm64
