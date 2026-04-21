/-
  EvmAsm.Evm64.DivMod.LoopComposeN1

  Four-iteration loop composition for n=1: unified (skip/addback)
  per-iteration specs that build on the raw per-iteration specs in LoopIterN1.

  For n=1, the loop runs 4 iterations:
  - j=3 (first): cpsTriple base+448 → base+448 (loop-back)
  - j=2 (middle): cpsTriple base+448 → base+448 (loop-back)
  - j=1 (middle): cpsTriple base+448 → base+448 (loop-back)
  - j=0 (final): cpsTriple base+448 → base+904 (loop exit)

  This file provides:
  1. Address linking lemmas for j=3 → j=2, j=2 → j=1, j=1 → j=0 transitions
  2. Unified max-path per-iteration specs for j=3, j=2, j=1, and j=0
  3. Unified call-path per-iteration specs for j=3, j=2, j=1, and j=0
-/

import EvmAsm.Evm64.DivMod.LoopIterN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address equality lemmas for j=3 output → j=2 input transition
--
-- j=3 postcondition uses uBase(3) = sp + signExtend12(4056) - 24
-- j=2 precondition uses uBase(2) = sp + signExtend12(4056) - 16
-- The overlap: uBase(3) + offset_k = uBase(2) + offset_{k-1}
-- ============================================================================

/-- j=3 un0 at uBase(3)+0 = j=2 u1 at uBase(2)-8 -/
theorem u_n1_j3_0_eq_j2_4088 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- j=3 un1 at uBase(3)-8 = j=2 u2 at uBase(2)-16 -/
theorem u_n1_j3_4088_eq_j2_4080 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- j=3 un2 at uBase(3)-16 = j=2 u3 at uBase(2)-24 -/
theorem u_n1_j3_4080_eq_j2_4072 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- j=3 un3 at uBase(3)+4072 = j=2 uTop at uBase(2)+4064 -/
theorem u_n1_j3_4072_eq_j2_4064 (sp : Word) :
    (sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

-- ============================================================================
-- Address equality lemmas for j=2 output → j=1 input transition
--
-- j=2 postcondition uses uBase(2) = sp + signExtend12(4056) - 16
-- j=1 precondition uses uBase(1) = sp + signExtend12(4056) - 8
-- ============================================================================

/-- j=2 un0 at uBase(2)+0 = j=1 u1 at uBase(1)-8 -/
theorem u_n1_j2_0_eq_j1_4088 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- j=2 un1 at uBase(2)-8 = j=1 u2 at uBase(1)-16 -/
theorem u_n1_j2_4088_eq_j1_4080 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- j=2 un2 at uBase(2)-16 = j=1 u3 at uBase(1)-24 -/
theorem u_n1_j2_4080_eq_j1_4072 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- j=2 un3 at uBase(2)+4072 = j=1 uTop at uBase(1)+4064 -/
theorem u_n1_j2_4072_eq_j1_4064 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

-- ============================================================================
-- Address equality lemmas for j=1 output → j=0 input transition
--
-- j=1 postcondition uses uBase(1) = sp + signExtend12(4056) - 8
-- j=0 precondition uses uBase(0) = sp + signExtend12(4056) - 0
-- ============================================================================

/-- j=1 un0 at uBase(1)+0 = j=0 u1 at uBase(0)-8 -/
theorem u_n1_j1_0_eq_j0_4088 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- j=1 un1 at uBase(1)-8 = j=0 u2 at uBase(0)-16 -/
theorem u_n1_j1_4088_eq_j0_4080 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- j=1 un2 at uBase(1)-16 = j=0 u3 at uBase(0)-24 -/
theorem u_n1_j1_4080_eq_j0_4072 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- j=1 un3 at uBase(1)+4072 = j=0 uTop at uBase(0)+4064 -/
theorem u_n1_j1_4072_eq_j0_4064 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

-- ============================================================================
-- Double-addback () unified per-iteration specs
-- These use _beq specs in the addback branch and _skip specs in the skip branch,
-- producing loopIterPostN1Max / loopIterPostN1Call postconditions.
-- ============================================================================

-- ============================================================================
-- Unified per-iteration max-path  specs
-- ============================================================================

/-- Unified j=3 max-path  spec: uses _beq spec for addback, _skip for skip. -/
theorem divK_loop_body_n1_max_unified_j3_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J3 := divK_loop_body_n1_max_addback_j3_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
      hcarry2_nz
    intro_lets at J3
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]; exact hp)
      (J3 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J3 := divK_loop_body_n1_max_skip_j3_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
    intro_lets at J3
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]; exact hp)
      (J3 hborrow)

/-- Unified j=2 max-path  spec: uses _beq spec for addback, _skip for skip. -/
theorem divK_loop_body_n1_max_unified_j2_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J2 := divK_loop_body_n1_max_addback_j2_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
      hcarry2_nz
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]; exact hp)
      (J2 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J2 := divK_loop_body_n1_max_skip_j2_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]; exact hp)
      (J2 hborrow)

/-- Unified j=1 max-path  spec: uses _beq spec for addback, _skip for skip. -/
theorem divK_loop_body_n1_max_unified_j1_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n1_max_addback_j1_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
      hcarry2_nz
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]; exact hp)
      (J1 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n1_max_skip_j1_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]; exact hp)
      (J1 hborrow)

/-- Unified j=0 max-path  spec: uses _beq spec for addback, _skip for skip.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n1_max_unified_j0_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n1_max_addback_j0_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
      hcarry2_nz
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_addback hb]; exact hp)
      (J0 hborrow)
  · -- skip path
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n1_max_skip_j0_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Max_skip hb]; exact hp)
      (J0 hborrow)

-- ============================================================================
-- Unified per-iteration call-path  specs
-- ============================================================================

/-- Unified j=3 call-path  spec: uses _beq spec for addback, _skip for skip. -/
theorem divK_loop_body_n1_call_unified_j3_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (3 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopIterPostN1Call sp base (3 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN1Call; simp only []; rw [if_pos hb]; decide
    have J3 := divK_loop_body_n1_call_addback_j3_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    intro_lets at J3
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_addback hb]; exact hp)
      J3
  · -- skip path
    have hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J3 := divK_loop_body_n1_call_skip_j3_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J3
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_skip hb]; exact hp)
      J3

/-- Unified j=2 call-path  spec: uses _beq spec for addback, _skip for skip. -/
theorem divK_loop_body_n1_call_unified_j2_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (2 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopIterPostN1Call sp base (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN1Call; simp only []; rw [if_pos hb]; decide
    have J2 := divK_loop_body_n1_call_addback_j2_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_addback hb]; exact hp)
      J2
  · -- skip path
    have hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J2 := divK_loop_body_n1_call_skip_j2_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_skip hb]; exact hp)
      J2

/-- Unified j=1 call-path  spec: uses _beq spec for addback, _skip for skip. -/
theorem divK_loop_body_n1_call_unified_j1_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (1 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopIterPostN1Call sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN1Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n1_call_addback_j1_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_addback hb]; exact hp)
      J1
  · -- skip path
    have hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J1 := divK_loop_body_n1_call_skip_j1_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_skip hb]; exact hp)
      J1

/-- Unified j=0 call-path  spec: uses _beq spec for addback, _skip for skip.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+904. -/
theorem divK_loop_body_n1_call_unified_j0_spec
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (loopIterPostN1Call sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path
    have hborrow : isAddbackBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN1Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n1_call_addback_j0_beq_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_addback hb]; exact hp)
      J0
  · -- skip path
    have hborrow : isSkipBorrowN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J0 := divK_loop_body_n1_call_skip_j0_spec sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN1Call_skip hb]; exact hp)
      J0

-- ============================================================================
-- Fin-parametric iter specs for n=1
-- ============================================================================

/-- Fin-parametric unified max-path iter spec for n=1. -/
theorem divK_loop_body_n1_max_iter_spec (j : Fin 4)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (j.val : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (j.val : Word) <<< (3 : BitVec 6).toNat
    let exit_addr := if j.val = 0 then base + denormOff else base + loopBodyOff
    cpsTriple (base + loopBodyOff) exit_addr (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (j.val : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((u_base + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((u_base + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((u_base + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((u_base + signExtend12 4072) ↦ₘ u3) **
       ((u_base + signExtend12 4064) ↦ₘ u_top) **
       (q_addr ↦ₘ q_old))
      (loopIterPostN1Max sp (j.val : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr exit_addr
  fin_cases j
  · exact divK_loop_body_n1_max_unified_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu hcarry2_nz
  · exact divK_loop_body_n1_max_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu hcarry2_nz
  · exact divK_loop_body_n1_max_unified_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu hcarry2_nz
  · exact divK_loop_body_n1_max_unified_j3_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu hcarry2_nz

/-- Fin-parametric unified call-path iter spec for n=1. -/
theorem divK_loop_body_n1_call_iter_spec (j : Fin 4)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u1 v0)
    (hcarry2_nz : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (j.val : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (j.val : Word) <<< (3 : BitVec 6).toNat
    let exit_addr := if j.val = 0 then base + denormOff else base + loopBodyOff
    cpsTriple (base + loopBodyOff) exit_addr (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ (j.val : Word)) **
       (.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) **
       (.x7 ↦ᵣ v7_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x2 ↦ᵣ v2_old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ j_old) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
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
      (loopIterPostN1Call sp base (j.val : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro u_base q_addr exit_addr
  fin_cases j
  · exact divK_loop_body_n1_call_unified_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base halign hbltu hcarry2_nz
  · exact divK_loop_body_n1_call_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base halign hbltu hcarry2_nz
  · exact divK_loop_body_n1_call_unified_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base halign hbltu hcarry2_nz
  · exact divK_loop_body_n1_call_unified_j3_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base halign hbltu hcarry2_nz

-- ============================================================================
-- Single `(j : Fin 4) (bltu : Bool)` iter spec for n=1
-- ============================================================================

/-- Unified iter spec for n=1: one theorem covering all 16 original path combinations.
    Uses `if bltu then ... else ...` hypothesis API so concrete-bltu call sites don't
    need vacuous dischargers — they pass the reduced hypothesis directly. -/
theorem divK_loop_body_n1_iter_spec (j : Fin 4) (bltu : Bool)
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : if bltu then ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516
              else True)
    (hbltu : if bltu then BitVec.ult u1 v0 else ¬BitVec.ult u1 v0)
    (hcarry : if bltu then isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 u_top
              else isAddbackCarry2NzN1Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let exit_addr := if j.val = 0 then base + denormOff else base + loopBodyOff
    cpsTriple (base + loopBodyOff) exit_addr (sharedDivModCode base)
      (match bltu with
       | true => loopBodyPreWithScratch (1 : Word) sp (j.val : Word) j_old
                   v5_old v6_old v7_old v10_old v11_old v2_old
                   v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old
                   ret_mem d_mem dlo_mem scratch_un0
       | false => loopBodyPre (1 : Word) sp (j.val : Word) j_old
                    v5_old v6_old v7_old v10_old v11_old v2_old
                    v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old)
      (loopIterPostN1 bltu sp base (j.val : Word) v0 v1 v2 v3 u0 u1 u2 u3 u_top) := by
  intro exit_addr
  cases bltu
  · -- false (max): halign reduces to True, hbltu to ¬ult, hcarry to max variant
    rw [if_neg (by decide)] at hbltu hcarry
    have H := divK_loop_body_n1_max_iter_spec j sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu hcarry
    intro_lets at H
    exact cpsTriple_weaken
      (fun _ hp => by delta loopBodyPre at hp; xperm_hyp hp)
      (fun _ hp => by unfold loopIterPostN1; simp only []; rw [sepConj_emp_right']; exact hp)
      H
  · -- true (call): halign, hbltu, hcarry reduce to call-path types
    rw [if_pos rfl] at halign hbltu hcarry
    have H := divK_loop_body_n1_call_iter_spec j sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base halign hbltu hcarry
    intro_lets at H
    exact cpsTriple_weaken
      (fun _ hp => by delta loopBodyPreWithScratch loopBodyPre at hp; xperm_hyp hp)
      (fun _ hp => by unfold loopIterPostN1; simp only []; exact hp)
      H

end EvmAsm.Evm64
