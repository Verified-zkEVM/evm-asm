/-
  EvmAsm.Evm64.DivMod.LoopComposeN2

  Three-iteration loop composition for n=2: unified (skip/addback)
  per-iteration specs that build on the raw per-iteration specs in LoopIterN2.

  For n=2, the loop runs 3 iterations:
  - j=2 (first): cpsTripleWithin base+448 → base+448 (loop-back)
  - j=1 (middle): cpsTripleWithin base+448 → base+448 (loop-back)
  - j=0 (final): cpsTripleWithin base+448 → base+904 (loop exit)

  This file provides:
  1. Address linking lemmas for j=2 → j=1 transition
  2. Unified max-path per-iteration specs for j=2, j=1, and j=0

  The compose surfaces in this file still thread the legacy universal
  Carry2NzAll package. They are compatibility surfaces for older callers; new
  v4 N2 stack/callable work should use selected/reachable carry wrappers.
-/

import EvmAsm.Evm64.DivMod.LoopIterN2
import EvmAsm.Evm64.DivMod.LoopIterN2NoNop
import EvmAsm.Evm64.DivMod.LoopComposeN3

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1)

-- ============================================================================
-- Address equality lemmas for j=2 output → j=1 input transition
--
-- j=2 postcondition uses uBase(2) = sp + signExtend12(4056) - 16
-- j=1 precondition uses uBase(1) = sp + signExtend12(4056) - 8
-- The overlap: uBase(2) + offset_k = uBase(1) + offset_{k-1}
-- ============================================================================

/-- j=2 un0 at uBase(2)+0 = j=1 u1 at uBase(1)-8 -/
theorem u_j2_0_eq_j1_4088 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- j=2 un1 at uBase(2)-8 = j=1 u2 at uBase(1)-16 -/
theorem u_j2_4088_eq_j1_4080 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- j=2 un2 at uBase(2)-16 = j=1 u3 at uBase(1)-24 -/
theorem u_j2_4080_eq_j1_4072 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- j=2 un3 at uBase(2)-24 = j=1 uTop at uBase(1)-32 -/
theorem u_j2_4072_eq_j1_4064 {sp : Word} :
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

-- ============================================================================
-- Double-addback () unified per-iteration max-path specs
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN2Max.
-- ============================================================================

/-- Bundled j=2 loop-body precondition for n=2 composition. Hides the
    `uBase`/`qAddr` address lets from public unified max-path theorem types. -/
@[irreducible]
def loopBodyN2J2Pre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld)

/-- Named unfold for `loopBodyN2J2Pre`. -/
theorem loopBodyN2J2Pre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) :
    loopBodyN2J2Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld =
    (let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (2 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld)) := by
  delta loopBodyN2J2Pre; rfl

/-- Unified  j=2 max-path spec: handles both skip and addback internally.
    Produces loopIterPostN2Max which uses AddbackBeqPost/SkipPost. -/
theorem divK_loop_body_n2_max_unified_j2_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyN2J2Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_max_addback_jgt0_beq_spec_within (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
        hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J2Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback hb]; exact hp)
      (J2 hborrow)
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J2 := divK_loop_body_n2_max_skip_jgt0_spec_within (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J2Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip hb]; exact hp)
      (J2 hborrow)

/-- No-NOP variant of `divK_loop_body_n2_max_unified_j2_spec_within`. -/
theorem divK_loop_body_n2_max_unified_j2_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      (loopBodyN2J2Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_max_addback_jgt0_beq_spec_within_noNop (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
        hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J2Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback hb]; exact hp)
      (J2 hborrow)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J2 := divK_loop_body_n2_max_skip_jgt0_spec_within_noNop (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J2Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip hb]; exact hp)
      (J2 hborrow)

/-- Unified  j=1 max-path spec: handles both skip and addback internally.
    Produces loopIterPostN2Max which uses AddbackBeqPost/SkipPost. -/
@[irreducible]
def loopBodyN2J1Pre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld)

theorem loopBodyN2J1Pre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) :
    loopBodyN2J1Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld =
    (let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld)) := by
  delta loopBodyN2J1Pre; rfl

theorem divK_loop_body_n2_max_unified_j1_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyN2J1Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_max_addback_jgt0_beq_spec_within (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
        hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J1Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback hb]; exact hp)
      (J1 hborrow)
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n2_max_skip_jgt0_spec_within (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J1Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip hb]; exact hp)
      (J1 hborrow)

/-- No-NOP variant of `divK_loop_body_n2_max_unified_j1_spec_within`. -/
theorem divK_loop_body_n2_max_unified_j1_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      (loopBodyN2J1Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN2Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_max_addback_jgt0_beq_spec_within_noNop (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu
        hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J1Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback hb]; exact hp)
      (J1 hborrow)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J1 := divK_loop_body_n2_max_skip_jgt0_spec_within_noNop (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J1Pre_unfold] at hp
        rw [loopBodyN2MaxJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip hb]; exact hp)
      (J1 hborrow)

/-- Unified  j=0 max-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTripleWithin 152 to base+908. -/
@[irreducible]
def loopBodyN2J0Pre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld)

theorem loopBodyN2J0Pre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) :
    loopBodyN2J0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld =
    (let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld)) := by
  delta loopBodyN2J0Pre; rfl

theorem divK_loop_body_n2_max_unified_j0_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopBodyN2J0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_max_addback_j0_beq_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J0Pre_unfold] at hp; rw [loopBodyN2MaxSkipJ0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback hb]; exact hp)
      (J0 hborrow)
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n2_max_skip_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J0Pre_unfold] at hp; rw [loopBodyN2MaxSkipJ0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip hb]; exact hp)
      (J0 hborrow)

/-- No-NOP variant of `divK_loop_body_n2_max_unified_j0_spec_within`. -/
theorem divK_loop_body_n2_max_unified_j0_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopBodyN2J0Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) ≠ (0 : Word) := by rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_max_addback_j0_beq_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J0Pre_unfold] at hp
        rw [loopBodyN2MaxSkipJ0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_addback hb]; exact hp)
      (J0 hborrow)
  · have hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
                    then (1 : Word) else 0) = (0 : Word) := if_neg hb
    have J0 := divK_loop_body_n2_max_skip_j0_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
      hbltu
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J0Pre_unfold] at hp
        rw [loopBodyN2MaxSkipJ0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Max_skip hb]; exact hp)
      (J0 hborrow)

-- ============================================================================
-- Double-addback () unified per-iteration call-path specs
-- Uses _beq LoopIter specs with borrow-branching loopIterPostN2Call.
-- ============================================================================

@[irreducible]
def loopBodyN2J2CallPre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (2 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld) **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

theorem loopBodyN2J2CallPre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) :
    loopBodyN2J2CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 =
    (let uBase := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (2 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1) := by
  delta loopBodyN2J2CallPre; rfl

/-- Unified  j=2 call-path spec: handles both skip and addback internally. -/
theorem divK_loop_body_n2_call_unified_j2_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyN2J2CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN2Call sp base (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_call_addback_jgt0_beq_spec_within (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J2CallPre_unfold] at hp; rw [loopBodyN2CallJgt0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback hb]; exact hp)
      J2
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J2 := divK_loop_body_n2_call_skip_jgt0_spec_within (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
        halign
        hbltu hborrow
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J2CallPre_unfold] at hp
        rw [loopBodyN2CallJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip hb]; exact hp)
      J2

/-- No-NOP variant of `divK_loop_body_n2_call_unified_j2_spec_within`. -/
theorem divK_loop_body_n2_call_unified_j2_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      (loopBodyN2J2CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN2Call sp base (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J2 := divK_loop_body_n2_call_addback_jgt0_beq_spec_within_noNop (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J2CallPre_unfold] at hp; rw [loopBodyN2CallJgt0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback hb]; exact hp)
      J2
  · have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J2 := divK_loop_body_n2_call_skip_jgt0_spec_within_noNop (2 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
        halign
        hbltu hborrow
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J2CallPre_unfold] at hp
        rw [loopBodyN2CallJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip hb]; exact hp)
      J2

@[irreducible]
def loopBodyN2J1CallPre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld) **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

theorem loopBodyN2J1CallPre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) :
    loopBodyN2J1CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 =
    (let uBase := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (1 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1) := by
  delta loopBodyN2J1CallPre; rfl

/-- Unified  j=1 call-path spec: handles both skip and addback internally. -/
theorem divK_loop_body_n2_call_unified_j1_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCode base)
      (loopBodyN2J1CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN2Call sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_call_addback_jgt0_beq_spec_within (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J1CallPre_unfold] at hp; rw [loopBodyN2CallJgt0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback hb]; exact hp)
      J1
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J1 := divK_loop_body_n2_call_skip_jgt0_spec_within (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
        halign
        hbltu hborrow
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J1CallPre_unfold] at hp
        rw [loopBodyN2CallJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip hb]; exact hp)
      J1

/-- No-NOP variant of `divK_loop_body_n2_call_unified_j1_spec_within`. -/
theorem divK_loop_body_n2_call_unified_j1_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop base)
      (loopBodyN2J1CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN2Call sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J1 := divK_loop_body_n2_call_addback_jgt0_beq_spec_within_noNop (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J1CallPre_unfold] at hp; rw [loopBodyN2CallJgt0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback hb]; exact hp)
      J1
  · have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J1 := divK_loop_body_n2_call_skip_jgt0_spec_within_noNop (1 : Word)
      EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
        halign
        hbltu hborrow
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J1CallPre_unfold] at hp
        rw [loopBodyN2CallJgt0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip hb]; exact hp)
      J1

/-- Unified  j=0 call-path spec: handles both skip and addback internally.
    Since j=0, the BGE loop-back is not taken, giving a cpsTripleWithin 202 to base+908. -/
@[irreducible]
def loopBodyN2J0CallPre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
  ((uBase + signExtend12 4064) ↦ₘ uTop) **
  (qAddr ↦ₘ qOld) **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1

theorem loopBodyN2J0CallPre_unfold
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word) :
    loopBodyN2J0CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 =
    (let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
     let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
     (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
     (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
     (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
     (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (2 : Word)) **
     ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
     ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
     ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
     ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
     ((uBase + signExtend12 4064) ↦ₘ uTop) **
     (qAddr ↦ₘ qOld) **
     (sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1) := by
  delta loopBodyN2J0CallPre; rfl

theorem divK_loop_body_n2_call_unified_j0_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopBodyN2J0CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN2Call sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · -- addback path: use _beq spec
    have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_call_addback_j0_beq_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign hbltu hborrow
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J0CallPre_unfold] at hp; rw [loopBodyN2CallSkipJ0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback hb]; exact hp)
      J0
  · -- skip path: use existing skip spec (unchanged)
    have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J0 := divK_loop_body_n2_call_skip_j0_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by rw [loopBodyN2J0CallPre_unfold] at hp; rw [loopBodyN2CallSkipJ0Pre_unfold]; exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip hb]; exact hp)
      J0

/-- No-NOP variant of `divK_loop_body_n2_call_unified_j0_spec_within`. -/
theorem divK_loop_body_n2_call_unified_j0_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 202 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopBodyN2J0CallPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0)
      (loopIterPostN2Call sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  by_cases hb : BitVec.ult uTop (mulsubN4_c3 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow : isAddbackBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      delta isAddbackBorrowN2Call; simp only []; rw [if_pos hb]; decide
    have J0 := divK_loop_body_n2_call_addback_j0_beq_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign hbltu hborrow
      hcarry2_nz
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J0CallPre_unfold] at hp
        rw [loopBodyN2CallSkipJ0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_addback hb]; exact hp)
      J0
  · have hborrow : isSkipBorrowN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := if_neg hb
    have J0 := divK_loop_body_n2_call_skip_j0_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 base
      halign
      hbltu hborrow
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => by
        rw [loopBodyN2J0CallPre_unfold] at hp
        rw [loopBodyN2CallSkipJ0Pre_unfold]
        exact hp)
      (fun h hp => by
        rw [← loopIterPostN2Call_skip hb]; exact hp)
      J0

-- ============================================================================
-- Double-addback () two-iteration max×max composition for n=2
-- j=1 max path, j=0 max path. Scratch cells in the frame throughout.
-- ============================================================================

theorem divK_loop_n2_max_max_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (base : Word)
    (hbltu_1 : ¬BitVec.ult u2 v1)
    (hbltu_0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 304 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old)
      (loopN2MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1  iteration spec
  have J1 := divK_loop_body_n2_max_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  -- Frame j=1 with u0Orig and q0Old
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- 3. j=0  iteration spec (inputs from j=1 via iterN2Max)
  have J0 := divK_loop_body_n2_max_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base

    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1  postcondition → j=0 precondition
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0Pre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1Pre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2MaxPost
      exact hp)
    full

/-- No-NOP variant of `divK_loop_n2_max_max_spec_within`. -/
theorem divK_loop_n2_max_max_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (base : Word)
    (hbltu_1 : ¬BitVec.ult u2 v1)
    (hbltu_0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 304 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2Iter10Pre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old)
      (loopN2MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n2_max_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  have J0 := divK_loop_body_n2_max_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base
    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0Pre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1Pre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2MaxPost
      exact hp)
    full

-- ============================================================================
-- Double-addback () two-iteration call×call composition for n=2
-- ============================================================================

theorem divK_loop_n2_call_call_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u2 v1)
    (hbltu_0 : BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 call  iteration spec
  have J1 := divK_loop_body_n2_call_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base halign hbltu_1
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  -- Frame j=1 with u0Orig and q0Old
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- 3. j=0 call  iteration spec (inputs from j=1 via iterN2Call)
  have J0 := divK_loop_body_n2_call_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    (base + div128CallRetOff) v1 (div128DLo v1) (div128Un0 u1)
    base halign

    hbltu_0
    (hcarry2 (div128Quot (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
                          (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      u0Orig
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1  postcondition → j=0 precondition
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0CallPre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1CallPre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2CallCallPost
      exact hp)
    full

/-- No-NOP variant of `divK_loop_n2_call_call_spec_within`. -/
theorem divK_loop_n2_call_call_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u2 v1)
    (hbltu_0 : BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2CallCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n2_call_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base halign hbltu_1
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  have J0 := divK_loop_body_n2_call_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    (base + div128CallRetOff) v1 (div128DLo v1) (div128Un0 u1)
    base halign
    hbltu_0
    (hcarry2 (div128Quot (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
                          (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      u0Orig
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0CallPre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1CallPre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2CallCallPost
      exact hp)
    full

-- ============================================================================
-- Double-addback () two-iteration max×call composition for n=2
-- j=1 max path, j=0 call path. Scratch cells are in the frame for j=1,
-- consumed/written by j=0 call.
-- ============================================================================

theorem divK_loop_n2_max_call_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    -- Branch conditions: j=1 max (BLTU not taken), j=0 call (BLTU taken)
    (hbltu_1 : ¬BitVec.ult u2 v1)
    (hbltu_0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 max  spec (no scratch cells)
  have J1 := divK_loop_body_n2_max_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  -- Frame j=1 with u0Orig, q0Old, AND scratch cells (max doesn't touch scratch)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
    (by pcFree) J1
  -- 3. j=0 call  spec (inputs from j=1 via iterN2Max, scratch from frame)
  have J0 := divK_loop_body_n2_call_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    retMem dMem dloMem scratch_un0
    base
    halign

    hbltu_0
    (hcarry2 (div128Quot (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
                          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      u0Orig
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  -- Frame j=0 with j=1's carried atoms (u4, q[1])
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  -- 4. Compose: rewrite j=1 max  postcondition → j=0 precondition
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0CallPre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1Pre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2MaxCallPost
      exact hp)
    full

/-- No-NOP variant of `divK_loop_n2_max_call_spec_within`. -/
theorem divK_loop_n2_max_call_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : ¬BitVec.ult u2 v1)
    (hbltu_0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2MaxCallPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n2_max_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old base
    hbltu_1
    (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) ** regOwn .x1)
    (by pcFree) J1
  have J0 := divK_loop_body_n2_call_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old
    retMem dMem dloMem scratch_un0
    base
    halign
    hbltu_0
    (hcarry2 (div128Quot (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
                          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
      u0Orig
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Max loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0CallPre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1Pre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2MaxCallPost
      exact hp)
    full

-- ============================================================================
-- Double-addback () two-iteration call×max composition for n=2
-- j=1 call path, j=0 max path. Scratch cells from j=1 call are carried
-- through as frame atoms for j=0 max.
-- ============================================================================

theorem divK_loop_n2_call_max_spec_within
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    -- Branch conditions: j=1 call (BLTU taken), j=0 max (BLTU not taken)
    (hbltu_1 : BitVec.ult u2 v1)
    (hbltu_0 : ¬BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- 1. j=1 call  spec (with scratch cells)
  have J1 := divK_loop_body_n2_call_unified_j1_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base
    halign
    hbltu_1
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  -- Frame j=1 with u0Orig and q0Old
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- 3. j=0 max  spec (inputs from j=1 via iterN2Call)
  have J0 := divK_loop_body_n2_max_unified_j0_spec_within sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base

    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  -- Frame j=0 with j=1's carried atoms (u4, q[1]) AND j=1's scratch cells
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v1) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u1) ** regOwn .x1)
    (by pcFree) J0
  -- 4. Compose: rewrite j=1 call  postcondition → j=0 precondition
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0Pre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  -- 5. Clean up postcondition
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1CallPre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2CallMaxPost
      exact hp)
    full

/-- No-NOP variant of `divK_loop_n2_call_max_spec_within`. -/
theorem divK_loop_n2_call_max_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u2 v1)
    (hbltu_0 : ¬BitVec.ult (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 354 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN2Iter10PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN2CallMaxPost sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig) := by
  delta loopN2Iter10PreWithScratch loopN2Iter10Pre; simp only []
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J1 := divK_loop_body_n2_call_unified_j1_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 base
    halign
    hbltu_1
    (hcarry2 (div128Quot u2 u1 v1) u0 u1 u2 u3 uTop : isAddbackCarry2NzN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  have J0 := divK_loop_body_n2_max_unified_j0_spec_within_noNop sp (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)
    ((iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    v0 v1 v2 v3
    u0Orig
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old base
    hbltu_0
    (hcarry2 (signExtend12 4095) u0Orig
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     (q_addr_1 ↦ₘ (iterN2Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).1) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ v1) **
     (sp + signExtend12 3952 ↦ₘ div128DLo v1) **
     (sp + signExtend12 3944 ↦ₘ div128Un0 u1) ** regOwn .x1)
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN2Call loopExitPostN2 loopExitPost at hp
      simp only [] at hp ⊢
      have hj' := jpred_1
      rw [hj', u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
          u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064] at hp
      rw [loopBodyN2J0Pre_unfold]
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by rw [loopBodyN2J1CallPre_unfold]; xperm_hyp hp)
    (fun h hp => by
      delta loopN2CallMaxPost
      exact hp)
    full

end EvmAsm.Evm64
