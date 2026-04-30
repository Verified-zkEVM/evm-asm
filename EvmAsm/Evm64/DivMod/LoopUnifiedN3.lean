/-
  EvmAsm.Evm64.DivMod.LoopUnifiedN3

  Bool-parameterized (unified) loop composition for n=3.
  Issue #262: Unify max/call branch paths via Bool parameter.

  Instead of 4 separate two-iteration composition theorems (max×max, call×call,
  max×call, call×max), this file provides a single theorem parameterized by
  `(bltu_1 bltu_0 : Bool)` that covers all 4 combinations.

  The proofs delegate to the existing per-path theorems in LoopComposeN3.lean
  via `cases bltu`, then bridge the pre/postconditions to the unified forms.
-/

import EvmAsm.Evm64.DivMod.LoopComposeN3

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Double-addback () unified two-iteration composition
-- Same pattern as divK_loop_n3_unified_spec_within but with  postconditions.
-- Uses iterN3 for the j=0 branch condition.
-- ============================================================================

/-- Unified n=3 two-iteration loop composition with double addback,
    parameterized by `(bltu_1 bltu_0 : Bool)`.
    Covers all 4 path combinations (max×max, call×call, max×call, call×max).
    Postcondition is loopN3UnifiedPost which uses iterN* values. -/
theorem divK_loop_n3_unified_spec_within (bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    -- Unified branch conditions (using iterN3 for j=0)
    (hbltu_1 : bltu_1 = BitVec.ult u3 v2)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN3 bltu_1 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (sharedDivModCode base)
      (loopN3PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN3UnifiedPost bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0) := by
  cases bltu_1 <;> cases bltu_0 <;> simp only [iterN3_true, iterN3_false] at hbltu_0
  · -- (false, false) = max×max
    have hbltu_1' : ¬BitVec.ult u3 v2 := by
      rw [show BitVec.ult u3 v2 = false from hbltu_1.symm]; decide
    have hbltu_0' : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      rw [show BitVec.ult _ v2 = false from hbltu_0.symm]; decide
    have hMM := divK_loop_n3_max_max_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old base
      hbltu_1' hbltu_0' hcarry2
    have hMMF := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (by pcFree) hMM
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => by delta loopN3PreWithScratch at hp; xperm_hyp hp)
      (fun h hp => by delta loopN3UnifiedPost; xperm_hyp hp)
      hMMF
  · -- (false, true) = max×call
    have hbltu_1' : ¬BitVec.ult u3 v2 := by
      rw [show BitVec.ult u3 v2 = false from hbltu_1.symm]; decide
    have hbltu_0' : BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 :=
      hbltu_0.symm ▸ rfl
    have hMC := divK_loop_n3_max_call_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN3UnifiedPost; exact hp)
      hMC
  · -- (true, false) = call×max
    have hbltu_1' : BitVec.ult u3 v2 := hbltu_1.symm ▸ rfl
    have hbltu_0' : ¬BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 := by
      rw [show BitVec.ult _ v2 = false from hbltu_0.symm]; decide
    have hCM := divK_loop_n3_call_max_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN3UnifiedPost; exact hp)
      hCM
  · -- (true, true) = call×call
    have hbltu_1' : BitVec.ult u3 v2 := hbltu_1.symm ▸ rfl
    have hbltu_0' : BitVec.ult (iterN3Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2 :=
      hbltu_0.symm ▸ rfl
    have hCC := divK_loop_n3_call_call_spec_within sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_1' hbltu_0' hcarry2
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by delta loopN3UnifiedPost; exact hp)
      hCC

end EvmAsm.Evm64
