/-
  EvmAsm.Evm64.DivMod.LoopComposeN2

  Three-iteration loop composition for n=2: unified (skip/addback)
  per-iteration specs that build on the raw per-iteration specs in LoopIterN2.

  For n=2, the loop runs 3 iterations:
  - j=2 (first): cpsTriple base+448 → base+448 (loop-back)
  - j=1 (middle): cpsTriple base+448 → base+448 (loop-back)
  - j=0 (final): cpsTriple base+448 → base+904 (loop exit)

  This file provides:
  1. Address linking lemmas for j=2 → j=1 transition
  2. Unified max-path per-iteration specs for j=2, j=1, and j=0
-/

import EvmAsm.Evm64.DivMod.LoopIterN2
import EvmAsm.Evm64.DivMod.LoopComposeN3

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address equality lemmas for j=2 output → j=1 input transition
--
-- j=2 postcondition uses u_base(2) = sp + signExtend12(4056) - 16
-- j=1 precondition uses u_base(1) = sp + signExtend12(4056) - 8
-- The overlap: u_base(2) + offset_k = u_base(1) + offset_{k-1}
-- ============================================================================

/-- j=2 un0 at u_base(2)+0 = j=1 u1 at u_base(1)-8 -/
theorem u_j2_0_eq_j1_4088 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  simp only [
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]
  bv_omega

/-- j=2 un1 at u_base(2)-8 = j=1 u2 at u_base(1)-16 -/
theorem u_j2_4088_eq_j1_4080 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]
  bv_omega

/-- j=2 un2 at u_base(2)-16 = j=1 u3 at u_base(1)-24 -/
theorem u_j2_4080_eq_j1_4072 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]
  bv_omega

/-- j=2 un3 at u_base(2)-24 = j=1 u_top at u_base(1)-32 -/
theorem u_j2_4072_eq_j1_4064 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide,
    show (2 : Word) <<< 3 = (16 : Word) from by decide]
  bv_omega

-- ============================================================================
-- Unified per-iteration specs: case-split skip/addback internally
-- ============================================================================

/-- Unified j=2 max-path spec: handles both skip and addback internally.
    Produces loopIterPostN2Max which uses iterN2Max for the result values. -/
theorem divK_loop_body_n2_max_unified_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u2 v1) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_max_addback_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J2
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Max iterN2Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN2AddbackPost at hp
        exact hp)
      (J2 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J2 := divK_loop_body_n2_max_skip_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J2
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Max iterN2Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN2SkipPost at hp
        exact hp)
      (J2 hborrow)

/-- Unified j=1 max-path spec: handles both skip and addback internally.
    Produces loopIterPostN2Max which uses iterN2Max for the result values. -/
theorem divK_loop_body_n2_max_unified_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u2 v1) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_max_addback_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Max iterN2Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN2AddbackPost at hp
        exact hp)
      (J1 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n2_max_skip_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Max iterN2Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN2SkipPost at hp
        exact hp)
      (J1 hborrow)

/-- Unified j=0 max-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n2_max_unified_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : ¬BitVec.ult u2 v1) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_max_addback_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Max iterN2Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN2AddbackPost at hp
        exact hp)
      (J0 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n2_max_skip_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Max iterN2Max mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN2SkipPost at hp
        exact hp)
      (J0 hborrow)

-- ============================================================================
-- Unified per-iteration call-path specs
-- ============================================================================

/-- Unified j=2 call-path spec: handles both skip and addback internally. -/
theorem divK_loop_body_n2_call_unified_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (2 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u2 v1) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
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
      (loopIterPostN2Call sp base (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_call_addback_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J2
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Call iterN2Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN2CallAddbackPostJ loopBodyN2AddbackPost at hp
        exact hp)
      J2
  · -- skip path
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J2 := divK_loop_body_n2_call_skip_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J2
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Call iterN2Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN2CallSkipPostJ loopBodyN2SkipPost at hp
        exact hp)
      J2

/-- Unified j=1 call-path spec: handles both skip and addback internally. -/
theorem divK_loop_body_n2_call_unified_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (1 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u2 v1) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 448) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
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
      (loopIterPostN2Call sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_call_addback_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Call iterN2Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN2CallAddbackPostJ loopBodyN2AddbackPost at hp
        exact hp)
      J1
  · -- skip path
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J1 := divK_loop_body_n2_call_skip_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J1
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Call iterN2Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN2CallSkipPostJ loopBodyN2SkipPost at hp
        exact hp)
      J1

/-- Unified j=0 call-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n2_call_unified_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (hv_j : isValidDwordAccess (sp + signExtend12 3976) = true)
    (hv_n1 : isValidDwordAccess (sp + signExtend12 3984) = true)
    (hv_uhi : isValidDwordAccess (sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) = true)
    (hv_ulo : isValidDwordAccess ((sp + signExtend12 4056 - (0 + (2 : Word)) <<< (3 : BitVec 6).toNat) + 8) = true)
    (hv_vtop : isValidDwordAccess (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) = true)
    (hv_ret : isValidDwordAccess (sp + signExtend12 3968) = true)
    (hv_d   : isValidDwordAccess (sp + signExtend12 3960) = true)
    (hv_dlo : isValidDwordAccess (sp + signExtend12 3952) = true)
    (hv_scratch_un0 : isValidDwordAccess (sp + signExtend12 3944) = true)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hv_v0 : isValidDwordAccess (sp + signExtend12 32) = true)
    (hv_u0 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0) = true)
    (hv_v1 : isValidDwordAccess (sp + signExtend12 40) = true)
    (hv_u1 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088) = true)
    (hv_v2 : isValidDwordAccess (sp + signExtend12 48) = true)
    (hv_u2 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080) = true)
    (hv_v3 : isValidDwordAccess (sp + signExtend12 56) = true)
    (hv_u3 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072) = true)
    (hv_u4 : isValidDwordAccess ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064) = true)
    (hv_q : isValidDwordAccess (sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) = true)
    (hbltu : BitVec.ult u2 v1) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + 448) (base + 904) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
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
      (loopIterPostN2Call sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr
  by_cases hb : BitVec.ult u_top (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_call_addback_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Call iterN2Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_pos hb] at ⊢
        delta loopBodyN2CallAddbackPostJ loopBodyN2AddbackPost at hp
        exact hp)
      J0
  · -- skip path
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J0 := divK_loop_body_n2_call_skip_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      hv_j hv_n1 hv_uhi hv_ulo hv_vtop hv_ret hv_d hv_dlo hv_scratch_un0 halign
      hv_v0 hv_u0 hv_v1 hv_u1 hv_v2 hv_u2 hv_v3 hv_u3 hv_u4 hv_q hbltu hborrow
    intro_lets at J0
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => hp)
      (fun h hp => by
        delta loopIterPostN2Call iterN2Call mulsubN4_c3 at hb ⊢
        simp only [] at ⊢
        simp only [if_neg hb] at ⊢
        delta loopBodyN2CallSkipPostJ loopBodyN2SkipPost at hp
        exact hp)
      J0

end EvmAsm.Evm64
