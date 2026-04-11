/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

  Lifts n=3 two-iteration loop compositions from sharedDivModCode to divCode,
  and composes with the pre-loop (base → base+448) to produce
  preloop+loop specs (base → base+904).
-/

import EvmAsm.Evm64.DivMod.LoopComposeN3
import EvmAsm.Evm64.DivMod.Compose.FullPathN3

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Lift n=3 max×max loop from sharedDivModCode to divCode
-- ============================================================================

/-- n=3 max×max loop lifted to divCode. -/
theorem divK_loop_n3_max_max_divCode
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (base : Word)
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
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN3Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old)
      (loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n3_max_max_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0 hbltu_1 hbltu_0)

-- ============================================================================
-- Address normalization lemmas for n=3 preloop+loop composition
-- ============================================================================

/-- signExtend12(4) - 3 = 1, for x1 register in loopSetupPost at n=3. -/
private theorem x1_val_n3 : signExtend12 (4 : BitVec 12) - (3 : Word) = (1 : Word) := by decide

private theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
private theorem se12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem se12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
private theorem se12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

-- Shared simp lemmas for address normalization (used with simp only)
private theorem n3_bv6_3 : (3 : BitVec 6).toNat = 3 := by decide
private theorem n3_shl0 : (0 : Word) <<< 3 = (0 : Word) := by decide
private theorem n3_shl1 : (1 : Word) <<< 3 = (8 : Word) := by decide
private theorem n3_se0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem n3_se4056 : signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) := by decide
private theorem n3_se4088 : signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) := by decide
private theorem n3_se4080 : signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) := by decide
private theorem n3_se4072 : signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) := by decide
private theorem n3_se4064 : signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) := by decide
private theorem n3_se4048 : signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) := by decide
private theorem n3_se4040 : signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) := by decide
private theorem n3_se4032 : signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) := by decide
private theorem n3_se4024 : signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) := by decide
private theorem n3_se4016 : signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) := by decide

-- u_base(1) + offset → flat address
private theorem n3_ub1_off0 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4048 := by
  simp only [n3_bv6_3, n3_shl1, n3_se0, n3_se4056, n3_se4048]; bv_omega

private theorem n3_ub1_off4088 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    sp + signExtend12 4040 := by
  simp only [n3_bv6_3, n3_shl1, n3_se4056, n3_se4088, n3_se4040]; bv_omega

private theorem n3_ub1_off4080 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    sp + signExtend12 4032 := by
  simp only [n3_bv6_3, n3_shl1, n3_se4056, n3_se4080, n3_se4032]; bv_omega

private theorem n3_ub1_off4072 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    sp + signExtend12 4024 := by
  simp only [n3_bv6_3, n3_shl1, n3_se4056, n3_se4072, n3_se4024]; bv_omega

private theorem n3_ub1_off4064 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 =
    sp + signExtend12 4016 := by
  simp only [n3_bv6_3, n3_shl1, n3_se4056, n3_se4064, n3_se4016]; bv_omega

-- u_base(0) + offset → flat address
private theorem n3_ub0_off0 (sp : Word) :
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) =
    sp + signExtend12 4056 := by
  simp only [n3_bv6_3, n3_shl0, n3_se0, n3_se4056]; bv_omega

-- q_addr(j) → flat address
private theorem n3_qa1 (sp : Word) :
    sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4080 := by
  simp only [n3_bv6_3, n3_shl1, n3_se4088, n3_se4080]; bv_omega

private theorem n3_qa0 (sp : Word) :
    sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat = sp + signExtend12 4088 := by
  simp only [n3_bv6_3, n3_shl0, n3_se4088]; bv_omega

-- Loop hv_* address equalities (compound loop form → flat preloop form)
private theorem n3_uhi_1_addr (sp : Word) :
    sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4024 := by
  simp only [show (1 + (3 : Word)) = (4 : Word) from by decide,
             show (4 : Word) <<< (3 : BitVec 6).toNat = (32 : Word) from by decide,
             n3_se4056, n3_se4024]; bv_omega

private theorem n3_ulo_1_addr (sp : Word) :
    (sp + signExtend12 4056 - (1 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4032 := by
  simp only [show (1 + (3 : Word)) = (4 : Word) from by decide,
             show (4 : Word) <<< (3 : BitVec 6).toNat = (32 : Word) from by decide,
             n3_se4056, n3_se4032]; bv_omega

private theorem n3_vtop_addr (sp : Word) :
    sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32 = sp + 48 := by
  simp only [show (3 : Word) + signExtend12 (4095 : BitVec 12) = (2 : Word) from by decide,
             show (2 : Word) <<< (3 : BitVec 6).toNat = (16 : Word) from by decide,
             se12_32]; bv_omega

private theorem n3_uhi_0_addr (sp : Word) :
    sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat = sp + signExtend12 4032 := by
  simp only [show (0 + (3 : Word)) = (3 : Word) from by decide,
             show (3 : Word) <<< (3 : BitVec 6).toNat = (24 : Word) from by decide,
             n3_se4056, n3_se4032]; bv_omega

private theorem n3_ulo_0_addr (sp : Word) :
    (sp + signExtend12 4056 - (0 + (3 : Word)) <<< (3 : BitVec 6).toNat) + 8 = sp + signExtend12 4040 := by
  simp only [show (0 + (3 : Word)) = (3 : Word) from by decide,
             show (3 : Word) <<< (3 : BitVec 6).toNat = (24 : Word) from by decide,
             n3_se4056, n3_se4040]; bv_omega

-- ============================================================================
-- Condition predicates for n=3 preloop+loop composition
-- ============================================================================

/-- Max trial condition at n=3, j=1: ¬ult u4_norm b2_norm. -/
def isMaxTrialN3_j1 (a3 b1 b2 : Word) : Prop :=
  let shift := (clzResult b2).1
  let anti_shift := signExtend12 (0 : BitVec 12) - shift
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (anti_shift.toNat % 64))
  let u4 := a3 >>> (anti_shift.toNat % 64)
  ¬BitVec.ult u4 b2'

/-- Max trial condition at n=3, j=0 (after j=1 max iteration). -/
def isMaxTrialN3_j0 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
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
  ¬BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2'

-- ============================================================================
-- Postcondition for n=3 preloop+loop (max×max, shift≠0)
-- ============================================================================

/-- Postcondition for pre-loop + max×max loop at n=3.
    Computes normalized b[], u[] from shift = clz(b2), then wraps loopN3MaxPost
    with frame atoms (a[], spare q[2..3]=0, spare u[6..7]=0, shift_mem). -/
@[irreducible]
def preloopN3MaxMaxPost (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
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
  loopN3MaxPost sp b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ shift)

-- ============================================================================
-- Preloop + max×max loop composition (base → base+904)
-- ============================================================================

/-- n=3 pre-loop + max×max loop helper: instantiate loop spec.
    Separate theorem to get its own heartbeat budget for WHNF. -/
private theorem evm_div_n3_loop_max_max_inst (sp base : Word)
    (shift anti_shift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10_old v11_old j_mem : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n : isValidDwordAccess (sp + signExtend12 3984) = true)
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
    (hbltu_1 : ¬BitVec.ult u4 b2')
    (hbltu_0 : ¬BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2') :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN3Pre sp j_mem (3 : Word) shift u0 v10_old v11_old anti_shift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word))
      (loopN3MaxPost sp b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0) :=
  divK_loop_n3_max_max_divCode
    sp j_mem (3 : Word) shift u0 v10_old v11_old anti_shift
    b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
    base
    hv_j hv_n hv_uhi_1 hv_ulo_1 hv_vtop hv_v0 hv_v1 hv_v2 hv_v3
    hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
    hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0
    hbltu_1 hbltu_0

/-- n=3 pre-loop + max×max loop: base → base+904 (shift ≠ 0). -/
theorem evm_div_n3_preloop_max_max_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11_old : Word)
    (q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem j_mem : Word)
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
    (hbltu_1 : isMaxTrialN3_j1 a3 b1 b2)
    (hbltu_0 : isMaxTrialN3_j0 a0 a1 a2 a3 b0 b1 b2 b3) :
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
       ((sp + signExtend12 3976) ↦ₘ j_mem))
      (preloopN3MaxMaxPost sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  -- 1. Pre-loop spec: base → base+448
  have hPre := evm_div_n3_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0_old u1_old u2_old u3_old u4_old u5 u6 u7 n_mem shift_mem
    hbnz hb3z hb2nz hshift_nz hvalid
    hv_q0 hv_q1 hv_q2 hv_q3 hv_u0 hv_u1 hv_u2 hv_u3 hv_u4
    hv_u5 hv_u6 hv_u7 hv_n hv_shift
  have hPreF := cpsTriple_frame_left _ _ _ _ _
    ((.x11 ↦ᵣ v11_old) ** ((sp + signExtend12 3976) ↦ₘ j_mem))
    (by pcFree) hPre
  -- 2. Loop spec via helper (no let bindings to avoid WHNF timeout)
  have hLoop := evm_div_n3_loop_max_max_inst sp base
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
    hv_j hv_n
    (by rw [n3_uhi_1_addr]; exact hv_u4) (by rw [n3_ulo_1_addr]; exact hv_u3)
    (by rw [n3_vtop_addr]; exact hvalid 6 (by omega))
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
      delta loopN3Pre
      simp only []
      simp only [n3_ub1_off0 sp, n3_ub1_off4088 sp, n3_ub1_off4080 sp,
                  n3_ub1_off4072 sp, n3_ub1_off4064 sp, n3_ub0_off0 sp,
                  n3_qa1 sp, n3_qa0 sp, se12_32, se12_40, se12_48, se12_56]
      xperm_hyp hp) hPreF hLoopF
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopN3MaxMaxPost; xperm_hyp hq)
    hFull

-- ============================================================================
-- Lift remaining loop variants from sharedDivModCode to divCode
-- ============================================================================

/-- n=3 call×call loop lifted to divCode. -/
theorem divK_loop_n3_call_call_divCode
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
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n3_call_call_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0 hbltu_1 hbltu_0)

/-- n=3 max×call loop lifted to divCode. -/
theorem divK_loop_n3_max_call_divCode
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
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n3_max_call_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0 hbltu_1 hbltu_0)

/-- n=3 call×max loop lifted to divCode. -/
theorem divK_loop_n3_call_max_divCode
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
    (hbltu_1 : BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1 v2) :
    cpsTriple (base + 448) (base + 904) (divCode base)
      (loopN3PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN3CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) :=
  cpsTriple_extend_code (hmono := sharedDivModCode_sub_divCode base)
    (divK_loop_n3_call_max_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
      ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi_1 hv_ulo_1 hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_v1 hv_v2 hv_v3
      hv_u0_1 hv_u1_1 hv_u2_1 hv_u3_1 hv_u4_1 hv_q1
      hv_uhi_0 hv_ulo_0 hv_u0_0 hv_q0 hbltu_1 hbltu_0)

end EvmAsm.Evm64
