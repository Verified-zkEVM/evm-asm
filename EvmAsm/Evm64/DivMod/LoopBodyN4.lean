/-
  EvmAsm.Evm64.DivMod.LoopBodyN4

  Fixed loop body compositions for n=4 (4-limb divisor, m=0, single iteration).
  Eliminates the u_addr/window-cell and vtop/v3 overlaps in the generic spec.

  For n=4, three address overlaps exist:
  1. u_addr = u_base + signExtend12 4064  (both refer to u[j+4])
  2. u_addr + 8 = u_base + signExtend12 4072  (both refer to u[j+3])
  3. vtop_base + signExtend12 32 = sp + signExtend12 56  (both refer to v[3])

  This file eliminates these overlaps by:
  - Expanding the trial spec's let-bindings via dsimp
  - Rewriting u_addr and vtop_base to canonical u_base-relative form
  - Framing only with cells NOT already in the trial spec
  - Composing without cell duplication in any separating conjunction
-/

import EvmAsm.Evm64.DivMod.LoopBody
import EvmAsm.Evm64.DivMod.LoopDefs

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address rewriting lemmas for n=4 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=4: u_addr = u_base + signExtend12 4064 -/
theorem u_addr_eq_n4 (sp j : Word) :
    sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide]
  bv_omega

/-- For n=4: (u_base + signExtend12 4064) + 8 = u_base + signExtend12 4072 -/
theorem u_addr8_eq_n4 (sp j : Word) :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide]
  bv_omega

/-- For n=4: vtop_base + signExtend12 32 = sp + signExtend12 56 -/
theorem vtop_eq_v3_n4 (sp : Word) :
    (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 56 := by
  simp only [show (3 : BitVec 6).toNat = 3 from by decide,
    show signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) from by decide,
    show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
    show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]
  bv_omega

-- ============================================================================
-- Section 12n4: Full loop body cpsBranch for n=4, BLTU not-taken + BEQ skip
-- Non-vacuous: no overlapping cells in precondition.
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU ntaken + BEQ skip) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_max_skip_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095  -- MAX64
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsBranch (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (base + 448) (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top)
      (base + 908) (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  -- TODO (Step 5): needs BEQ bridge between addback (→880) and store_loop (884→)
  sorry

-- ============================================================================
-- Section 13n4: Full loop body cpsBranch for n=4, BLTU not-taken + BEQ addback
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU ntaken + BEQ addback) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_max_addback_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let q_hat : Word := signExtend12 4095  -- MAX64
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranch (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (base + 448) (loopBodyN4AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top)
      (base + 908) (loopBodyN4AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  -- TODO (Step 5): needs BEQ bridge
  sorry

-- ============================================================================
-- Section 14n4: Full loop body cpsBranch for n=4, BLTU taken + BEQ skip
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU taken + BEQ skip) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_call_skip_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let d_hi := v3 >>> (32 : BitVec 6).toNat
    let d_lo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_top d_hi
    let rhat := u_top - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow = 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word) →
    cpsBranch (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
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
      (base + 448)
      (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      (base + 908)
      (loopBodyN4SkipPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  -- TODO (Step 5): needs BEQ bridge between addback (→880) and store_loop (884→)
  sorry

-- ============================================================================
-- Section 15n4: Full loop body cpsBranch for n=4, BLTU taken + BEQ addback
-- ============================================================================

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
/-- Full loop body (BLTU taken + BEQ addback) for n=4.
    No overlapping cells: u_hi=u_top, u_lo=u3, v_top=v3.
    Entry: base+448, cpsBranch to base+448/904. -/
theorem divK_loop_body_n4_call_addback_spec
    (sp j j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u_top v3) :
    let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    -- div128 intermediates
    let d_hi := v3 >>> (32 : BitVec 6).toNat
    let d_lo := (v3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u_top d_hi
    let rhat := u_top - q1 * d_hi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + d_hi
    let q_dlo := q1c * d_lo
    let rhat_un1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhat_un1 q_dlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhat_un1 q_dlo then rhatc + d_hi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * d_lo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * d_lo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let q_hat := (q1' <<< (32 : BitVec 6).toNat) ||| q0'
    let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    -- Hypothesis: borrow ≠ 0
    (if BitVec.ult u_top (mulsubN4_c3 q_hat v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) ≠ (0 : Word) →
    cpsBranch (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
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
      (base + 448)
      (loopBodyN4AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0))
      (base + 908)
      (loopBodyN4AddbackPost sp j q_hat v0 v1 v2 v3 u0 u1 u2 u3 u_top **
       (sp + signExtend12 3968 ↦ₘ (base + 516)) **
       (sp + signExtend12 3960 ↦ₘ v3) **
       (sp + signExtend12 3952 ↦ₘ d_lo) **
       (sp + signExtend12 3944 ↦ₘ div_un0)) := by
  -- TODO (Step 5): needs BEQ bridge
  sorry

-- ============================================================================
-- Section 16n4: Combined loop body cpsBranch for n=4 (all 4 paths unified)
-- ============================================================================

/-- Postcondition for one loop iteration at n=4.
    Output values are concrete parameters (not existentially quantified),
    preserving the relationship between outputs and inputs for semantic
    correctness proofs. -/
def loopBodyPostN4
    (sp j v0 v1 v2 v3 : Word)
    (x2v x10v x11v : Word)
    (un0v un1v un2v un3v u4v qv : Word)
    (retv dv dlov sunv : Word) : Assertion :=
  let u_base := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
  let j' := j + signExtend12 4095
  let q_addr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ j') **
  (.x5 ↦ᵣ j <<< (3 : BitVec 6).toNat) ** (.x6 ↦ᵣ u_base) **
  (.x7 ↦ᵣ q_addr) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  (.x2 ↦ᵣ x2v) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ un0v) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ un1v) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ un2v) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ un3v) **
  ((u_base + signExtend12 4064) ↦ₘ u4v) **
  (q_addr ↦ₘ qv) **
  (sp + signExtend12 3968 ↦ₘ retv) **
  (sp + signExtend12 3960 ↦ₘ dv) **
  (sp + signExtend12 3952 ↦ₘ dlov) **
  (sp + signExtend12 3944 ↦ₘ sunv)


end EvmAsm.Evm64
