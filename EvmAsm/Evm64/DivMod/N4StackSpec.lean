/-
  EvmAsm.Evm64.DivMod.N4StackSpec

  n=4 (b.getLimbN 3 ≠ 0) DIV/MOD top-level dispatcher: case-splits on
  `(clzResult (b.getLimbN 3)).1 = 0` (the shift-flag), routing the
  `shift = 0` branch to `evm_{div,mod}_n4_shift0_stack_spec` and the
  `shift ≠ 0` branch to `evm_{div,mod}_n4_call_stack_spec[_within]`.

  Both sub-paths share the same precondition (`{div,mod}N4StackPreCall`)
  and postcondition (`{div,mod}N4CallSkipStackPost`), so the unified
  `evm_{div,mod}_n4_stack_spec` is a thin dispatcher.

  Step bound: `max(284, 340) = 340` (cf. constituent specs at
  Shift0Dispatcher.lean:54 and Spec/CallAddbackMod.lean:404).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
  Refs: GH #61, beads `evm-asm-17hg` (precursor under `evm-asm-pb40`).
-/

import EvmAsm.Evm64.DivMod.Shift0Dispatcher
import EvmAsm.Evm64.DivMod.Spec.CallAddbackMod

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **n=4 DIV top-level dispatcher** (any shift). Case-splits on the
    runtime shift flag `(clzResult (b.getLimbN 3)).1 = 0`:

    * `shift = 0`  →  `evm_div_n4_shift0_stack_spec`
    * `shift ≠ 0`  →  `evm_div_n4_call_stack_spec`

    Step bound is the max of the two branches (`shift_nz` is the
    expensive path at 340 steps; the `shift0` 284-step branch is
    weakened to 340 via `cpsTripleWithin_mono_nSteps`).

    The `shift_nz`-only hypotheses (`hbltu`, `hcarry2_nz_addback`,
    `hsem_addback`) are demanded unconditionally because the caller
    does not know the shift at proof time. This matches the shape the
    fully unified `evm_div_stack_spec` (slice 3, beads
    `evm-asm-4keh`) will consume for its `b ≠ 0`, n=4 branch. -/
theorem evm_div_n4_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin 340 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) := by
  by_cases hshift : (clzResult (b.getLimbN 3)).1 = 0
  · exact cpsTripleWithin_mono_nSteps (by decide) <|
      evm_div_n4_shift0_stack_spec sp base a b
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        hbnz hb3nz hshift halign
  · exact evm_div_n4_call_stack_spec sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift halign hbltu hcarry2_nz_addback hsem_addback

/-- **n=4 MOD top-level dispatcher** (any shift). Mirror of
    `evm_div_n4_stack_spec`. The MOD shift_nz wrapper has a `_within`
    suffix in `Spec/CallAddbackMod.lean`; we inherit that suffix here
    for naming symmetry across MOD entry points. -/
theorem evm_mod_n4_stack_spec_within (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz_addback :
      isAddbackBorrowN4CallEvm a b → isAddbackCarry2NzN4CallEvm a b)
    (hsem_addback :
      isAddbackBorrowN4CallEvm a b → n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin 340 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) := by
  by_cases hshift : (clzResult (b.getLimbN 3)).1 = 0
  · exact cpsTripleWithin_mono_nSteps (by decide) <|
      evm_mod_n4_shift0_stack_spec sp base a b
        v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratch_un0
        hbnz hb3nz hshift halign
  · exact evm_mod_n4_call_stack_spec_within sp base a b
      v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0
      hbnz hb3nz hshift halign hbltu hcarry2_nz_addback hsem_addback

end EvmAsm.Evm64
