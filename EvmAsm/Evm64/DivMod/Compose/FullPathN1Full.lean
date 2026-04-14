/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1Full

  Full n=1 DIV path composition for the shift≠0 case:
  pre-loop → 4-iteration loop → denorm + epilogue.
  Composes base → base+1064 for the b[3]=b[2]=b[1]=0, b[0]≠0, shift≠0 case.

  Unified theorem with (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) covers all 16 combinations.
  Uses a parametric denorm' helper + 16-case denorm_comp.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPath

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Full path postcondition for n=1 DIV (shift≠0, unified)
-- ============================================================================

/-- Unified full path postcondition for n=1 DIV (shift ≠ 0).
    Uses `iterN1` (reduces to `iterN1Max`/`iterN1Call` for concrete bools).
    Scratch cells depend on the path: passthrough for all-max,
    div128 scratch for the last call-path iteration. -/
@[irreducible]
def fullDivN1UnifiedPost (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b0).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
  let r2 := iterN1 bltu_2 v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  let r1 := iterN1 bltu_1 v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let r0 := iterN1 bltu_0 v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  denormDivPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.1 r1.1 r2.1 r3.1 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4024) ↦ₘ r0.2.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ r1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ r2.2.2.2.2.2) **
  ((sp + signExtend12 4000) ↦ₘ r3.2.2.2.2.2) **
  (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0.1) **
  -- Scratch cells: bltu_0=true → j=0 call scratch; all-false → passthrough
  match bltu_3, bltu_2, bltu_1, bltu_0 with
  | false, false, false, false =>
    (sp + signExtend12 3968 ↦ₘ ret_mem) **
    (sp + signExtend12 3960 ↦ₘ d_mem) **
    (sp + signExtend12 3952 ↦ₘ dlo_mem) **
    (sp + signExtend12 3944 ↦ₘ scratch_un0)
  | false, false, false, true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)
  | false, false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1_s)
  | false, false, true,  true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)
  | false, true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u2_s)
  | false, true,  false, true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)
  | false, true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1_s)
  | false, true,  true,  true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)
  | true,  false, false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u3_s)
  | true,  false, false, true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)
  | true,  false, true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1_s)
  | true,  false, true,  true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)
  | true,  true,  false, false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u2_s)
  | true,  true,  false, true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)
  | true,  true,  true,  false =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u1_s)
  | true,  true,  true,  true  =>
    (sp + signExtend12 3968 ↦ₘ (base + 516)) **
    (sp + signExtend12 3960 ↦ₘ v0') **
    (sp + signExtend12 3952 ↦ₘ div128DLo v0') **
    (sp + signExtend12 3944 ↦ₘ div128Un0 u0_s)

-- ============================================================================
-- Shift≠0 denorm+epilogue helper (parametric)
-- ============================================================================

/-- Shift≠0 denorm+epilogue helper for n=1. Takes r0/r1/r2/r3 and scratch
    as explicit params. Uses evm_div_preamble_denorm_epilogue_spec. -/
private theorem evm_div_n1_denorm' (sp base shift : Word)
    (r0_un0 r0_un1 r0_un2 r0_un3 r0_u4 r0_q : Word)
    (r1_q r1_u4 : Word) (c3_0 : Word)
    (r2_q r2_u4 : Word)
    (r3_q r3_u4 : Word)
    (scratch_ret scratch_d scratch_dlo scratch_un0_val : Word)
    (a0 a1 a2 a3 : Word)
    (v0' v1' v2' v3' : Word)
    (hshift_nz : shift ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true) :
    cpsTriple (base + 904) (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
       (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3_0) ** (.x11 ↦ᵣ r0_q) **
       (.x2 ↦ᵣ r0_un3) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + 32) ↦ₘ v0') ** ((sp + signExtend12 4056) ↦ₘ r0_un0) **
       ((sp + 40) ↦ₘ v1') ** ((sp + signExtend12 4048) ↦ₘ r0_un1) **
       ((sp + 48) ↦ₘ v2') ** ((sp + signExtend12 4040) ↦ₘ r0_un2) **
       ((sp + 56) ↦ₘ v3') ** ((sp + signExtend12 4032) ↦ₘ r0_un3) **
       ((sp + signExtend12 4024) ↦ₘ r0_u4) **
       ((sp + signExtend12 4088) ↦ₘ r0_q) **
       (sp + signExtend12 3968 ↦ₘ scratch_ret) **
       (sp + signExtend12 3960 ↦ₘ scratch_d) **
       (sp + signExtend12 3952 ↦ₘ scratch_dlo) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0_val) **
       ((sp + signExtend12 4016) ↦ₘ r1_u4) ** ((sp + signExtend12 4080) ↦ₘ r1_q) **
       ((sp + signExtend12 4008) ↦ₘ r2_u4) ** ((sp + signExtend12 4072) ↦ₘ r2_q) **
       ((sp + signExtend12 4000) ↦ₘ r3_u4) ** ((sp + signExtend12 4064) ↦ₘ r3_q) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ shift))
      (denormDivPost sp shift r0_un0 r0_un1 r0_un2 r0_un3 r0_q r1_q r2_q r3_q **
       ((sp + signExtend12 3992) ↦ₘ shift) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ r0_u4) **
       ((sp + signExtend12 4016) ↦ₘ r1_u4) **
       ((sp + signExtend12 4008) ↦ₘ r2_u4) **
       ((sp + signExtend12 4000) ↦ₘ r3_u4) **
       (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
       (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0_q) **
       (sp + signExtend12 3968 ↦ₘ scratch_ret) **
       (sp + signExtend12 3960 ↦ₘ scratch_d) **
       (sp + signExtend12 3952 ↦ₘ scratch_dlo) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0_val)) := by
  have hB := evm_div_preamble_denorm_epilogue_spec sp base
    r0_un0 r0_un1 r0_un2 r0_un3 shift
    r0_un3 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088) c3_0
    r0_q r1_q r2_q r3_q v0' v1' v2' v3'
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  have hBF := cpsTriple_frame_left _ _ _ _ _
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ r0_u4) **
     ((sp + signExtend12 4016) ↦ₘ r1_u4) **
     ((sp + signExtend12 4008) ↦ₘ r2_u4) **
     ((sp + signExtend12 4000) ↦ₘ r3_u4) **
     (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ r0_q) **
     (sp + signExtend12 3968 ↦ₘ scratch_ret) **
     (sp + signExtend12 3960 ↦ₘ scratch_d) **
     (sp + signExtend12 3952 ↦ₘ scratch_dlo) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0_val))
    (by pcFree) hB
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hBF

-- ============================================================================
-- Shift≠0 denorm composition (16-case split)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 51200000 in
/-- Denorm composition for shift≠0: preloopN1UnifiedPost → fullDivN1UnifiedPost. -/
theorem evm_div_n1_denorm_comp (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (hv_shift : isValidDwordAccess (sp + signExtend12 3992) = true)
    (hv_q0 : isValidDwordAccess (sp + signExtend12 4088) = true)
    (hv_q1 : isValidDwordAccess (sp + signExtend12 4080) = true)
    (hv_q2 : isValidDwordAccess (sp + signExtend12 4072) = true)
    (hv_q3 : isValidDwordAccess (sp + signExtend12 4064) = true)
    (hv_u0 : isValidDwordAccess (sp + signExtend12 4056) = true)
    (hv_u1 : isValidDwordAccess (sp + signExtend12 4048) = true)
    (hv_u2 : isValidDwordAccess (sp + signExtend12 4040) = true)
    (hv_u3 : isValidDwordAccess (sp + signExtend12 4032) = true) :
    cpsTriple (base + 904) (base + 1064) (divCode base)
      (preloopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        ret_mem d_mem dlo_mem scratch_un0)
      (fullDivN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        ret_mem d_mem dlo_mem scratch_un0) := by
  let shift := (clzResult b0).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3_s u4_s (0 : Word) (0 : Word) (0 : Word)
  -- Case-split on all 4 bools to resolve match in pre/postconditions
  cases bltu_3 <;> cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
  -- (F,F,F,F): all max
  · let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      ret_mem d_mem dlo_mem scratch_un0
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_false,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false]; xperm_hyp hq)
      hD
  · -- (F,F,F,T)
    let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_false,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (F,F,T,F)
    let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u1_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (F,F,T,T)
    let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (F,T,F,F)
    let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u2_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (F,T,F,T)
    let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (F,T,T,F)
    let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u1_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (F,T,T,T)
    let r3 := iterN1Max v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,F,F,F)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u3_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,F,F,T)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,F,T,F)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u1_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,F,T,T)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Max v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,T,F,F)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u2_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,T,F,T)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Max v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true, iterN1_false,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,T,T,F)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Max v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (signExtend12 4095 : Word) v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u1_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true,
          loopIterPostN1_max, loopIterPostN1Max, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_false, iterN1_true]; xperm_hyp hq)
      hD
  · -- (T,T,T,T)
    let r3 := iterN1Call v0' v1' v2' v3' u3_s u4_s (0:Word) (0:Word) (0:Word)
    let r2 := iterN1Call v0' v1' v2' v3' u2_s r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    let r1 := iterN1Call v0' v1' v2' v3' u1_s r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    let r0 := iterN1Call v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    have hD := evm_div_n1_denorm' sp base shift
      r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 r0.2.2.2.2.2 r0.1
      r1.1 r1.2.2.2.2.2
      (mulsubN4 (div128Quot r1.2.1 u0_s v0') v0' v1' v2' v3' u0_s r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
      r2.1 r2.2.2.2.2.2 r3.1 r3.2.2.2.2.2
      (base + 516) v0' (div128DLo v0') (div128Un0 u0_s)
      a0 a1 a2 a3 v0' v1' v2' v3'
      hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        delta preloopN1UnifiedPost loopN1UnifiedPost at hp
        simp only [iterN1_true,
          loopIterPostN1_call, loopIterPostN1Call, loopExitPostN1_j0_eq,
          n1_ub3_off4064, n2_ub2_off4064, n3_ub1_off4064, n1_qa3, n2_qa2, n3_qa1,
          se12_32, se12_40, se12_48, se12_56, sepConj_emp_right'] at hp
        xperm_hyp hp)
      (fun h hq => by delta fullDivN1UnifiedPost; simp only [iterN1_true]; xperm_hyp hq)
      hD

-- ============================================================================
-- Full n=1 DIV path (shift≠0, unified): base → base+1064
-- ============================================================================

/-- Unified full n=1 DIV path (shift ≠ 0), covering all 16 path combinations.
    Composes pre-loop + 4-iteration loop + denorm + epilogue. -/
theorem evm_div_n1_full_unified_spec (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
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
    (hbltu_3 : isTrialN1_j3 bltu_3 a3 b0)
    (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3)
    (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
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
      (fullDivN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        ret_mem d_mem dlo_mem scratch_un0) := by
  -- 1. Preloop + loop: base → base+904
  have hA := evm_div_n1_preloop_loop_unified_spec bltu_3 bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem
    ret_mem d_mem dlo_mem scratch_un0
    hbnz hb3z hb2z hb1z hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift hv_j hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hbltu_3 hbltu_2 hbltu_1 hbltu_0
  -- 2. Denorm composition
  have hD := evm_div_n1_denorm_comp bltu_3 bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3
    ret_mem d_mem dlo_mem scratch_un0
    hshift_nz hvalid hv_shift hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3
  -- 3. Compose
  exact cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) hA hD

end EvmAsm.Evm64
