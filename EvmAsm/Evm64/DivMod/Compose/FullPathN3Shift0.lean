/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3Shift0

  Full n=3 DIV path composition for the shift=0 case:
  pre-loop → 2-iteration loop → shift=0 epilogue.
  Composes base → base+1064 for the b[3]=0, b[2]≠0, shift=0 case.

  When shift=0, normalization is identity (v=b, u=a, u4=0).
  Since u4=0 < b2 (b2≠0), the j=1 BLTU condition is always taken → call path.
  j=0 can be either call or max.
  Two variants: call×call and call×max.
-/

import EvmAsm.Evm64.DivMod.LoopComposeN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Condition predicates for n=3 shift=0 (j=1 always call, j=0 varies)
-- ============================================================================

/-- Call trial condition at n=3 shift=0, j=0 after j=1 call:
    updated u3 < b2. -/
def isCallTrialN3Shift0_j0 (a1 a2 a3 b0 b1 b2 : Word) : Prop :=
  BitVec.ult (iterN3Call b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word)).2.2.2.1 b2

/-- Max trial condition at n=3 shift=0, j=0 after j=1 call:
    updated u3 ≥ b2. -/
def isMaxTrialN3Shift0_j0 (a1 a2 a3 b0 b1 b2 : Word) : Prop :=
  ¬BitVec.ult (iterN3Call b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word)).2.2.2.1 b2

-- ============================================================================
-- Lift n=3 loop variants from sharedDivModCode to divCode (shift=0)
-- ============================================================================

/-- n=3 call×call loop lifted to divCode (for shift=0). -/
private theorem divK_loop_n3_shift0_call_call_inst (sp base : Word)
    (clz_hi v11_old j_mem : Word)
    (a0 a1 a2 a3 b0 b1 b2 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
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
    (hb2nz : b2 ≠ 0)
    (hbltu_0 : isCallTrialN3Shift0_j0 a1 a2 a3 b0 b1 b2) :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN3PreWithScratch sp j_mem (3 : Word) (0 : Word) clz_hi (0 : Word) v11_old (0 : Word)
        b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word) a0 (0 : Word) (0 : Word)
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3CallCallPost sp base b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word) a0) := by
  unfold isCallTrialN3Shift0_j0 at hbltu_0
  exact cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n3_call_call_spec sp j_mem (3 : Word) (0 : Word) clz_hi (0 : Word) v11_old (0 : Word)
      b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word) a0 (0 : Word) (0 : Word)
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0 (ult_zero_of_ne hb2nz) hbltu_0)

-- ============================================================================
-- Postcondition for preloop + call×call loop (shift=0): base → base+904
-- ============================================================================

@[irreducible]
def preloopN3Shift0CallCallPost (sp base a0 a1 a2 a3 b0 b1 b2 : Word) : Assertion :=
  loopN3CallCallPost sp base b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word) a0 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word))

-- ============================================================================
-- Preloop + call×call loop composition (shift=0): base → base+904
-- ============================================================================

theorem evm_div_n3_preloop_shift0_call_call_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_z : (clzResult b2).1 = 0)
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
    (hbltu_0 : isCallTrialN3Shift0_j0 a1 a2 a3 b0 b1 b2) :
    cpsTriple base (base + 904) (divCode base)
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
       (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (preloopN3Shift0CallCallPost sp base a0 a1 a2 a3 b0 b1 b2) := by
  -- 1. Pre-loop spec: base → base+448 (shift=0)
  have hPre := evm_div_n3_shift0_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3z hb2nz hshift_z hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift
  have hPreF := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11_old) ** ((sp + signExtend12 3976) ↦ₘ j_mem) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- 2. Loop spec via helper
  have hLoop := divK_loop_n3_shift0_call_call_inst sp base
    ((clzResult b2).2 >>> (63 : Nat)) v11_old j_mem a0 a1 a2 a3 b0 b1 b2
    ret_mem d_mem dlo_mem scratch_un0
    hv_j hv_n
    (by rw [n3_uhi_1_addr]; exact hv_u4) (by rw [n3_ulo_1_addr]; exact hv_u3)
    (by rw [n3_vtop_addr]; exact hvalid 6 (by omega))
    hv_ret hv_d hv_dlo hv_scratch_un0 halign
    (by rw [se12_32]; exact hvalid 4 (by omega))
    (by rw [se12_40]; exact hvalid 5 (by omega))
    (by rw [se12_48]; exact hvalid 6 (by omega))
    (by rw [se12_56]; exact hvalid 7 (by omega))
    (by rw [n3_ub1_off0]; exact hv_u1) (by rw [n3_ub1_off4088]; exact hv_u2)
    (by rw [n3_ub1_off4080]; exact hv_u3) (by rw [n3_ub1_off4072]; exact hv_u4)
    (by rw [n3_ub1_off4064]; exact hv_u5) (by rw [n3_qa1]; exact hv_q1)
    (by rw [n3_uhi_0_addr]; exact hv_u3) (by rw [n3_ulo_0_addr]; exact hv_u2)
    (by rw [n3_ub0_off0]; exact hv_u0) (by rw [n3_qa0]; exact hv_q0)
    hb2nz hbltu_0
  -- Frame loop with a[], spare q[2..3], spare u[6..7], shift_mem
  have hLoopF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))
    (by pcFree) hLoop
  -- 3. Compose preloop + loop
  have hFull := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      simp only [x1_val_n3, hshift_z, hb3z,
        show signExtend12 (0 : BitVec 12) - (0 : Word) = (0 : Word) from by decide] at hp
      delta loopN3PreWithScratch loopN3Pre
      simp only []
      simp only [n3_ub1_off0 sp, n3_ub1_off4088 sp, n3_ub1_off4080 sp,
                  n3_ub1_off4072 sp, n3_ub1_off4064 sp, n3_ub0_off0 sp,
                  n3_qa1 sp, n3_qa0 sp, se12_32, se12_40, se12_48, se12_56, hshift_z]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN3Shift0CallCallPost; simp only [hshift_z] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Full path postcondition for n=3 DIV (shift=0, call×call)
-- ============================================================================

/-- Full path postcondition for n=3 DIV (shift=0, call×call).
    When shift=0, the denorm body is skipped (BEQ taken), so u-cells and x2
    preserve their loop-exit values. -/
@[irreducible]
def fullDivN3Shift0CallCallPost (sp base a0 a1 a2 a3 b0 b1 b2 : Word) : Assertion :=
  let r1 := iterN3Call b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word)
  let r0 := iterN3Call b0 b1 b2 (0 : Word) a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  -- epilogue output (shift=0: denorm body skipped, x2 preserved from loop):
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0.1) ** (.x6 ↦ᵣ r1.1) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ r0.2.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) ** ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + 32) ↦ₘ r0.1) ** ((sp + 40) ↦ₘ r1.1) **
  ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
  -- preserved frame atoms:
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4056) ↦ₘ r0.2.1) ** ((sp + signExtend12 4048) ↦ₘ r0.2.2.1) **
  ((sp + signExtend12 4040) ↦ₘ r0.2.2.2.1) ** ((sp + signExtend12 4032) ↦ₘ r0.2.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  (sp + signExtend12 3968 ↦ₘ (base + 516)) **
  (sp + signExtend12 3960 ↦ₘ b2) **
  (sp + signExtend12 3952 ↦ₘ div128DLo b2) **
  (sp + signExtend12 3944 ↦ₘ div128Un0 r1.2.2.1)

-- ============================================================================
-- Shift=0 epilogue helper (parametric, short WHNF)
-- ============================================================================

/-- Shift=0 epilogue helper for call×call. Takes r0/r1 as explicit params (short WHNF).
    Precondition atom order matches preloopN3Shift0CallCallPost's unfolded form exactly,
    so the perm callback in denorm_comp can use `exact hp` (no xperm needed). -/
private theorem evm_div_n3_shift0_cc_denorm' (sp base : Word)
    (r0_un0 r0_un1 r0_un2 r0_un3 r0_u4 r0_q : Word)
    (r1_q r1_u4 : Word) (c3_0 : Word)
    (r1_un1 : Word)
    (a0 a1 a2 a3 b0 b1 b2 : Word)
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
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + signExtend12 4056) ↦ₘ r0_un0) **
       ((sp + 40) ↦ₘ b1) ** ((sp + signExtend12 4048) ↦ₘ r0_un1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + signExtend12 4040) ↦ₘ r0_un2) **
       ((sp + 56) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4032) ↦ₘ r0_un3) **
       ((sp + signExtend12 4024) ↦ₘ r0_u4) **
       ((sp + signExtend12 4088) ↦ₘ r0_q) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ b2) **
       (sp + signExtend12 3952 ↦ₘ div128DLo b2) **
       (sp + signExtend12 3944 ↦ₘ div128Un0 r1_un1) **
       ((sp + signExtend12 4016) ↦ₘ r1_u4) ** ((sp + signExtend12 4080) ↦ₘ r1_q) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (0 : Word)))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ r0_q) ** (.x6 ↦ᵣ r1_q) ** (.x7 ↦ᵣ (0 : Word)) **
       (.x2 ↦ᵣ r0_un3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4088) ↦ₘ r0_q) ** ((sp + signExtend12 4080) ↦ₘ r1_q) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + 32) ↦ₘ r0_q) ** ((sp + 40) ↦ₘ r1_q) **
       ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ r0_un0) ** ((sp + signExtend12 4048) ↦ₘ r0_un1) **
       ((sp + signExtend12 4040) ↦ₘ r0_un2) ** ((sp + signExtend12 4032) ↦ₘ r0_un3) **
       ((sp + signExtend12 4024) ↦ₘ r0_u4) **
       ((sp + signExtend12 4016) ↦ₘ r1_u4) **
       ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
       (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0_q) **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ b2) **
       (sp + signExtend12 3952 ↦ₘ div128DLo b2) **
       (sp + signExtend12 3944 ↦ₘ div128Un0 r1_un1)) := by
  -- Apply shift=0 epilogue (takes 16 atoms), frame with remaining 20
  have hB := evm_div_shift0_epilogue_spec sp base
    r0_un0 r0_un1 r0_un2 r0_un3
    (0 : Word) r0_un3 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3_0
    r0_q r1_q 0 0
    b0 b1 b2 (0 : Word)
    rfl hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ r0_un0) ** ((sp + signExtend12 4048) ↦ₘ r0_un1) **
     ((sp + signExtend12 4040) ↦ₘ r0_un2) ** ((sp + signExtend12 4032) ↦ₘ r0_un3) **
     ((sp + signExtend12 4024) ↦ₘ r0_u4) **
     ((sp + signExtend12 4016) ↦ₘ r1_u4) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0_q) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ b2) **
     (sp + signExtend12 3952 ↦ₘ div128DLo b2) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 r1_un1))
    (by pcFree) hB
  -- xperm on parameterized atoms (r0_un0 etc.) is cheap -- no deep WHNF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hBF

-- ============================================================================
-- Shift=0 epilogue composition (instantiation wrapper)
-- ============================================================================

/-- Denorm composition for shift=0 call×call: preloopN3Shift0CallCallPost → fullDivN3Shift0CallCallPost.
    Separate theorem with own heartbeat budget. Directly composes the shift=0 epilogue
    with the preloop postcondition. -/
theorem evm_div_n3_shift0_cc_denorm_comp (sp base a0 a1 a2 a3 b0 b1 b2 : Word)
    (hvalid : ValidMemRange sp 8)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true) :
    cpsTriple (base + 904) (base + 1064) (divCode base)
      (preloopN3Shift0CallCallPost sp base a0 a1 a2 a3 b0 b1 b2)
      (fullDivN3Shift0CallCallPost sp base a0 a1 a2 a3 b0 b1 b2) := by
  let r1 := iterN3Call b0 b1 b2 (0 : Word) a1 a2 a3 (0 : Word) (0 : Word)
  let r0 := iterN3Call b0 b1 b2 (0 : Word) a0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  let q_hat_0 := div128Quot r1.2.2.2.1 r1.2.2.1 b2
  let c3_0 := (mulsubN4 q_hat_0 b0 b1 b2 (0 : Word) a0 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  have hD := evm_div_n3_shift0_cc_denorm' sp base
    r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
    r1.1 r1.2.2.2.2.2 c3_0 r1.2.2.1
    a0 a1 a2 a3 b0 b1 b2
    hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      delta preloopN3Shift0CallCallPost at hp
      simp only [loopN3CallCallPost, loopIterPostN3Call, loopExitPostN3_j0_eq,
        n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56] at hp
      xperm_hyp hp)
    (fun h hq => by delta fullDivN3Shift0CallCallPost; xperm_hyp hq)
    hD

-- ============================================================================
-- Full n=3 DIV path (shift=0, call×call): base → base+1064
-- ============================================================================

theorem evm_div_n3_full_shift0_call_call_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_z : (clzResult b2).1 = 0)
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
    (hbltu_0 : isCallTrialN3Shift0_j0 a1 a2 a3 b0 b1 b2) :
    cpsTriple base (base + 1064) (divCode base)
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
       (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
       (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullDivN3Shift0CallCallPost sp base a0 a1 a2 a3 b0 b1 b2) := by
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n3_preloop_shift0_call_call_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2nz hshift_z hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0
    halign hbltu_0
  -- 2. Denorm composition (separate theorem, own heartbeat budget)
  have hD := evm_div_n3_shift0_cc_denorm_comp sp base a0 a1 a2 a3 b0 b1 b2
    hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3
  -- 3. Compose preloop+denorm
  exact cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hA hD

end EvmAsm.Evm64
