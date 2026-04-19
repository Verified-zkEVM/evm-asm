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
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1)

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
  divmod_addr

/-- j=2 un1 at u_base(2)-8 = j=1 u2 at u_base(1)-16 -/
theorem u_j2_4088_eq_j1_4080 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- j=2 un2 at u_base(2)-16 = j=1 u3 at u_base(1)-24 -/
theorem u_j2_4080_eq_j1_4072 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- j=2 un3 at u_base(2)-24 = j=1 u_top at u_base(1)-32 -/
theorem u_j2_4072_eq_j1_4064 (sp : Word) :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

-- ============================================================================
-- Double-addback () unified per-iteration max-path specs
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN2Max.
-- ============================================================================

/-- Unified  j=2 max-path spec: handles both skip and addback internally.
    Produces loopIterPostN2Max which uses AddbackBeqPost/SkipPost. -/
theorem divK_loop_body_n2_max_unified_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
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
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_max_addback_j2_beq_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu
      hcarry2_nz
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      (J2 hborrow)
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J2 := divK_loop_body_n2_max_skip_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      (J2 hborrow)

/-- Unified  j=1 max-path spec: handles both skip and addback internally.
    Produces loopIterPostN2Max which uses AddbackBeqPost/SkipPost. -/
theorem divK_loop_body_n2_max_unified_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
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
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_max_addback_j1_beq_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base hbltu
      hcarry2_nz
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      (J1 hborrow)
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n2_max_skip_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hbltu
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      (J1 hborrow)

/-- Unified  j=0 max-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+908. -/
theorem divK_loop_body_n2_max_unified_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
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
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_max_addback_j0_beq_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hbltu
      hcarry2_nz
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      (J0 hborrow)
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : (if BitVec.ult u_top (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n2_max_skip_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old base
      hbltu
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      (J0 hborrow)

-- ============================================================================
-- Double-addback () unified per-iteration call-path specs
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN2Call.
-- ============================================================================

/-- Unified  j=2 call-path spec: handles both skip and addback internally. -/
theorem divK_loop_body_n2_call_unified_j2_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
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
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_call_addback_j2_beq_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      J2
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J2 := divK_loop_body_n2_call_skip_j2_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J2
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      J2

/-- Unified  j=1 call-path spec: handles both skip and addback internally. -/
theorem divK_loop_body_n2_call_unified_j1_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
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
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_call_addback_j1_beq_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      J1
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J1 := divK_loop_body_n2_call_skip_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J1
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      J1

/-- Unified  j=0 call-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTriple to base+908. -/
theorem divK_loop_body_n2_call_unified_j0_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top) :
    let u_base := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let q_addr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
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
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_call_addback_j0_beq_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      halign hbltu hborrow
      hcarry2_nz
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      J0
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top := if_neg hb
    have J0 := divK_loop_body_n2_call_skip_j0_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
      v0 v1 v2 v3 u0 u1 u2 u3 u_top q_old ret_mem d_mem dlo_mem scratch_un0 base
      halign
      hbltu hborrow
    intro_lets at J0
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip _ _ _ _ _ _ _ _ _ _ _ _ hb]; exact hp)
      J0

-- ============================================================================
-- Double-addback () two-iteration max×max composition for n=2
-- j=1 max path, j=0 max path. Scratch cells in the frame throughout.
-- ============================================================================

theorem divK_loop_n2_max_max_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (base : Word)
    (hbltu_1 : ¬BitVec.ult u2 v1)
    (hbltu_0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10Pre sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old)
      (loopN2MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1  iteration spec
  have J1 := divK_loop_body_n2_max_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 u_top : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top)
  intro_lets at J1
  -- Frame j=1 with u0_orig and q0_old
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J1
  -- 3. j=0  iteration spec (inputs from j=1 via iterN2Max)
  have J0 := divK_loop_body_n2_max_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old base

    hbltu_0
    (hcarry2 (signExtend12 4095) u0_orig
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1  postcondition → j=0 precondition
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN2MaxPost
      exact hp)
    full

-- ============================================================================
-- Double-addback () two-iteration call×call composition for n=2
-- ============================================================================

theorem divK_loop_n2_call_call_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu_1 : BitVec.ult u2 v1)
    (hbltu_0 : BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN2CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 call  iteration spec
  have J1 := divK_loop_body_n2_call_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old ret_mem d_mem dlo_mem scratch_un0 base halign hbltu_1
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 u_top : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top)
  intro_lets at J1
  -- Frame j=1 with u0_orig and q0_old
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J1
  -- 3. j=0 call  iteration spec (inputs from j=1 via iterN2Call)
  have J0 := divK_loop_body_n2_call_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old
    (base + 516) v1 (div128DLo v1) (div128Un0 u1)
    base halign

    hbltu_0
    (hcarry2 (div128Quot (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
                          (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v1)
      u0_orig
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1  postcondition → j=0 precondition
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN2CallCallPost
      exact hp)
    full

-- ============================================================================
-- Double-addback () two-iteration max×call composition for n=2
-- j=1 max path, j=0 call path. Scratch cells are in the frame for j=1,
-- consumed/written by j=0 call.
-- ============================================================================

theorem divK_loop_n2_max_call_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    -- Branch conditions: j=1 max (BLTU not taken), j=0 call (BLTU taken)
    (hbltu_1 : ¬BitVec.ult u2 v1)
    (hbltu_0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN2MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 max  spec (no scratch cells)
  have J1 := divK_loop_body_n2_max_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 u_top : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top)
  intro_lets at J1
  -- Frame j=1 with u0_orig, q0_old, AND scratch cells (max doesn't touch scratch)
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old) **
     (sp + signExtend12 3968 ↦ₘ ret_mem) ** (sp + signExtend12 3960 ↦ₘ d_mem) **
     (sp + signExtend12 3952 ↦ₘ dlo_mem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) J1
  -- 3. j=0 call  spec (inputs from j=1 via iterN2Max, scratch from frame)
  have J0 := divK_loop_body_n2_call_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old
    ret_mem d_mem dlo_mem scratch_un0
    base
    halign

    hbltu_0
    (hcarry2 (div128Quot (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
                          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1 v1)
      u0_orig
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 u_top).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1 max  postcondition → j=0 precondition
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN2MaxCallPost
      exact hp)
    full

-- ============================================================================
-- Double-addback () two-iteration call×max composition for n=2
-- j=1 call path, j=0 max path. Scratch cells from j=1 call are carried
-- through as frame atoms for j=0 max.
-- ============================================================================

theorem divK_loop_n2_call_max_spec
    (sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
     v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old : Word)
    (ret_mem d_mem dlo_mem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    -- Branch conditions: j=1 call (BLTU taken), j=0 max (BLTU not taken)
    (hbltu_1 : BitVec.ult u2 v1)
    (hbltu_0 : ¬BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTriple (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10PreWithScratch sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
        v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig q1_old q0_old
        ret_mem d_mem dlo_mem scratch_un0)
      (loopN2CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 u_top u0_orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 call  spec (with scratch cells)
  have J1 := divK_loop_body_n2_call_unified_j1_spec sp j_old v5_old v6_old v7_old v10_old v11_old v2_old
    v0 v1 v2 v3 u0 u1 u2 u3 u_top q1_old ret_mem d_mem dlo_mem scratch_un0 base
    halign
    hbltu_1
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 u_top : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top)
  intro_lets at J1
  -- Frame j=1 with u0_orig and q0_old
  have J1f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_0 + signExtend12 0) ↦ₘ u0_orig) ** (q_addr_0 ↦ₘ q0_old))
    (by pcFree) J1
  -- 3. j=0 max  spec (inputs from j=1 via iterN2Call)
  have J0 := divK_loop_body_n2_max_unified_j0_spec sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
    v0 v1 v2 v3
    u0_orig
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1
    q0_old base

    hbltu_0
    (hcarry2 (signExtend12 4095) u0_orig
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.1)
  intro_lets at J0
  -- Frame j=0 with j=1's carried atoms (u4, q[1]) AND j=1's scratch cells
  have J0f := cpsTriple_frame_left _ _ _ _ _
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 u_top).1) **
     (sp + signExtend12 3968 ↦ₘ (base + 516)) **
     (sp + signExtend12 3960 ↦ₘ v1) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1 call  postcondition → j=0 precondition
  have full := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088 sp, u_j1_4088_eq_j0_4080 sp,
          u_j1_4080_eq_j0_4072 sp, u_j1_4072_eq_j0_4064 sp] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN2CallMaxPost
      exact hp)
    full

end EvmAsm.Evm64
