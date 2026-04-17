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
-- Double-addback (_da) condition predicates for n=3 preloop+loop composition
-- ============================================================================

/-- j=1 trial condition for n=3 (double-addback): same as `isTrialN3_j1`
    since the first iteration doesn't use `iterN3`. -/
def isTrialN3_j1_da (bltu : Bool) (a3 b1 b2 : Word) : Prop :=
  let shift := (clzResult b2).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  bltu = BitVec.ult
    (a3 >>> (anti_shift.toNat % 64))
    ((b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64)))

/-- j=0 trial condition for n=3 (double-addback), dependent on j=1 path (bltu_1).
    Checks the BLTU condition after the j=1 iteration result using `iterN3_da`. -/
def isTrialN3_j0_da (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let shift := (clzResult b2).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  let u4_s := a3 >>> (anti_shift.toNat % 64)
  bltu_0 = BitVec.ult
    (iterN3_da bltu_1 v0' v1' v2' v3' u1_s u2_s u3_s u4_s (0 : Word)).2.2.2.1
    v2'

-- ============================================================================
-- Double-addback unified preloop+loop postcondition
-- ============================================================================

/-- Unified postcondition for preloop+loop at n=3 (double-addback).
    Wraps loopN3UnifiedPost_da (with normalized values computed from a[],b[])
    plus frame atoms: a[0..3], spare q[2..3]=0, spare u[6..7]=0, shift. -/
@[irreducible]
def preloopN3UnifiedPost_da (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word) : Assertion :=
  let shift := (clzResult b2).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (anti_shift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (anti_shift.toNat % 64))
  let u0_s := a0 <<< (shift.toNat % 64)
  let u1_s := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (anti_shift.toNat % 64))
  let u2_s := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (anti_shift.toNat % 64))
  let u3_s := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (anti_shift.toNat % 64))
  loopN3UnifiedPost_da bltu_1 bltu_0 sp base
    v0' v1' v2' v3' u1_s u2_s u3_s (a3 >>> (anti_shift.toNat % 64)) (0 : Word) u0_s
    ret_mem d_mem dlo_mem scratch_un0 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1)

-- ============================================================================
-- Double-addback loop instantiation helper (heartbeat isolation)
-- ============================================================================

/-- Helper: instantiate unified n=3 loop (double-addback) with explicit normalized values.
    Separates the loop application from the composition for heartbeat budgeting. -/
private theorem evm_div_n3_loop_unified_da_inst
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift anti_shift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10_old v11_old j_mem : Word)
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
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 = BitVec.ult
      (iterN3_da bltu_1 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2') :
    cpsTriple (base + 448) (base + 908) (divCode base)
      (loopN3PreWithScratch sp j_mem (3 : Word) shift u0 v10_old v11_old anti_shift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3UnifiedPost_da bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        ret_mem d_mem dlo_mem scratch_un0) :=
  divK_loop_n3_unified_da_divCode bltu_1 bltu_0
    sp j_mem (3 : Word) shift u0 v10_old v11_old anti_shift
    b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
    ret_mem d_mem dlo_mem scratch_un0 base
    hv_j hv_n hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
    hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    hbltu_1 hbltu_0

-- ============================================================================
-- Double-addback unified preloop+loop composition (base → base+908)
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12800000 in
/-- Unified preloop+loop for n=3 (double-addback), parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max×max, call×call, max×call, call×max).
    Precondition always includes scratch cells.
    Composes preloop (base→base+448) with unified loop (base+448→base+908). -/
theorem evm_div_n3_preloop_loop_unified_da_spec (bltu_1 bltu_0 : Bool) (sp base : Word)
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
    (hbltu_1 : isTrialN3_j1_da bltu_1 a3 b1 b2)
    (hbltu_0 : isTrialN3_j0_da bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
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
      (preloopN3UnifiedPost_da bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
        ret_mem d_mem dlo_mem scratch_un0) := by
  -- 1. Pre-loop: base → base+448
  have hPre := evm_div_n3_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3z hb2nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift
  -- Frame preloop with .x11, j_mem, scratch cells
  have hPreF := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11_old) ** ((sp + signExtend12 3976) ↦ₘ j_mem) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) **
     (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- 2. Loop: base+448 → base+908 (unified da, with explicit normalized values)
  have hLoop := evm_div_n3_loop_unified_da_inst bltu_1 bltu_0 sp base
    (clzResult b2).1 (signExtend12 (0 : BitVec 12) - (clzResult b2).1)
    (b0 <<< ((clzResult b2).1.toNat % 64))
    ((b1 <<< ((clzResult b2).1.toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((b2 <<< ((clzResult b2).1.toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((b3 <<< ((clzResult b2).1.toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    (a0 <<< ((clzResult b2).1.toNat % 64))
    ((a1 <<< ((clzResult b2).1.toNat % 64)) ||| (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((a2 <<< ((clzResult b2).1.toNat % 64)) ||| (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    ((a3 <<< ((clzResult b2).1.toNat % 64)) ||| (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64)))
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))
    (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b2).1).toNat % 64))
    v11_old j_mem
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
    hbltu_1 hbltu_0
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
      delta loopSetupPost at hp
      simp only [x1_val_n3] at hp
      delta loopN3PreWithScratch loopN3Pre
      simp only []
      simp only [n3_ub1_off0 sp, n3_ub1_off4088 sp, n3_ub1_off4080 sp,
                  n3_ub1_off4072 sp, n3_ub1_off4064 sp, n3_ub0_off0 sp,
                  n3_qa1 sp, n3_qa0 sp, se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN3UnifiedPost_da; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
