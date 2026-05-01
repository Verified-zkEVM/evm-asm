/-
  EvmAsm.Evm64.DivMod.N4StackSpecWithin

  Dispatcher-surface wrappers for the n=4 (b.getLimbN 3 ≠ 0) DIV/MOD top-level
  paths: lift `evm_div_n4_stack_spec` / `evm_mod_n4_stack_spec_within` (which
  speak in `divN4StackPreCall` / `{div,mod}N4CallSkipStackPost`) into the
  unified dispatcher contract `divModStackDispatchPre` /
  `{div,mod}StackDispatchPost` used by n=1, n=2, n=3.

  These are thin bridges: the postconditions
  `divN4CallSkipStackPost sp a b` and `divStackDispatchPost sp a b` are
  syntactically identical after `_unfold`, and the precondition only needs
  an `xperm_hyp` to permute the register/scratch atoms.

  Once these wrappers exist the unified `evm_div_stack_spec` /
  `evm_mod_stack_spec` (slice 4keh / 3muq under `evm-asm-pb40`, GH #61) can
  dispatch the n=4 case uniformly without touching the call-skip surface.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
  Refs: GH #61, beads `evm-asm-p3zs` (parent `evm-asm-pb40`).
-/

import EvmAsm.Evm64.DivMod.N4StackSpec
import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Dispatcher-surface wrapper for the n=4 DIV path. Lifts
    `evm_div_n4_stack_spec` from `divN4StackPreCall` /
    `divN4CallSkipStackPost` into `divModStackDispatchPre` /
    `divStackDispatchPost`, matching the shape of
    `evm_div_n{1,2,3}_stack_spec_within`. -/
theorem evm_div_n4_stack_spec_within_dispatch (sp base : Word)
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
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  have hN4 := evm_div_n4_stack_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz halign hbltu hcarry2_nz_addback hsem_addback
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      delta divModStackDispatchPre at hp
      rw [divN4StackPreCall_unfold]
      xperm_hyp hp)
    (fun _ hq => by
      rw [divN4CallSkipStackPost_unfold] at hq
      rw [divStackDispatchPost_unfold]
      exact hq)
    hN4

/-- Dispatcher-surface wrapper for the n=4 MOD path. Mirror of
    `evm_div_n4_stack_spec_within`. -/
theorem evm_mod_n4_stack_spec_within_dispatch (sp base : Word)
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
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  have hN4 := evm_mod_n4_stack_spec_within sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz halign hbltu hcarry2_nz_addback hsem_addback
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      delta divModStackDispatchPre at hp
      rw [modN4StackPreCall_unfold]
      xperm_hyp hp)
    (fun _ hq => by
      rw [modN4CallSkipStackPost_unfold] at hq
      rw [modStackDispatchPost_unfold]
      exact hq)
    hN4

end EvmAsm.Evm64
