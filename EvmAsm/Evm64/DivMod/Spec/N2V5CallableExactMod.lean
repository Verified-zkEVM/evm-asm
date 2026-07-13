/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallableExactMod

  MOD mirror of `N2V5CallableExact`: the unified-bound n=2 v5 MOD callable
  exact-frame lane.  Applies the mod post bridge to weaken the unified loop post
  to the mod callable exact-frame dispatch post, weakens the scratch cell to
  `memOwn`, and lifts the body count to `unifiedDivBound`.  `hbody` should be
  produced by `evm_mod_n2_stack_pre_to_unified_post_v5_noNop`; free incoming
  `x9In`/`x2In` (both dead — overwritten by loopSetup/phaseC2).
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5ModPostShared
import EvmAsm.Evm64.DivMod.Spec.UnifiedBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified-bound n=2 MOD v5 body spec over `modCode_noNop_v5` with exact
    caller-framed `x1` in the postcondition; the trial-call scratch cell at
    `sp + signExtend12 3936` is existentially closed (`memOwn`); free `x9In`/`x2In`. -/
theorem evm_mod_n2_stack_spec_noNop_v5_preNoX1_callableExactFrame_uni
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal x9In x2In : Word)
    (hdivWord : fullModN2RemainderWordV5 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.mod a b)
    (hbody : cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 702) + (2 + 23 + 10))
      base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        x2In
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullModN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
       (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        x9In raVal
        x2In
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) :=
  cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hq => by
        obtain ⟨h1, h2, hd, hu, hframe, hscratch⟩ := hq
        exact ⟨h1, h2, hd, hu, hframe, memIs_implies_memOwn h2 hscratch⟩)
      (cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun h hq =>
          fullModN2UnifiedPostNoX1V5_frame_to_modStackDispatchPostCallableExactFrame_scratch_word
            bltu_2 bltu_1 bltu_0 sp base a b
            retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hq)
        hbody)

end EvmAsm.Evm64
