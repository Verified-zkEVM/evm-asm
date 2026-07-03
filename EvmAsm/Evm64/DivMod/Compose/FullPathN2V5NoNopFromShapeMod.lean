/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopFromShapeMod

  Borrow-dispatched n=2 v5 entry→nopOff full path, with the carry hypothesis
  DISCHARGED FROM SHAPE.  Wraps `evm_mod_n2_stack_pre_to_unified_post_v5_noNop_borrowCarry`
  (#7452): instead of taking `loopN2SelectedBorrowCarryV5` as a hypothesis, it
  discharges it via `loopN2SelectedBorrowCarryV5_of_shape` (#7461), and accepts
  the borrow flags in the CLEAN `ult (fullDivN2R{2,1}V5 …).2.2.1 vTop` form
  (rather than #7452's `iterN2Max`/`iterWithDoubleAddback` `match` form), bridged
  via the dispatch-form equalities (#7463).  This removes the last shape-derived
  obligation from the n=2 execution path — the direct input to the n=2 lane.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallablePostSelectedBorrowCarryMod
import EvmAsm.Evm64.DivMod.Spec.N2V5BundleOfShape
import EvmAsm.Evm64.DivMod.Spec.N2V5R2R1Dispatch

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem evm_mod_n2_stack_pre_to_unified_post_v5_noNop_fromShape (sp base : Word)
    (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal x9In x2In : Word)
    (bltu_2 bltu_1 bltu_0 : Bool)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0) (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 =
      BitVec.ult (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN2R2V5 bltu_2 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1)
    (hbltu_0 : bltu_0 =
      BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1) :
    cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 702) + (2 + 23 + 10))
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
       (.x1 ↦ᵣ raVal)) := by
  apply evm_mod_n2_stack_pre_to_unified_post_v5_noNop_borrowCarry sp base a b
    v5 v6 v7 v10 v11Old q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In
    hbnz hb3z hb2z hb1nz hshift_nz halign hbltu_2
  case hbltu_1 =>
    -- match form, from clean form via dispatch-eq (full simp reduces the
    -- proof-discriminated match)
    cases bltu_2 <;> simpa [fullDivN2R2V5_eq_dispatch] using hbltu_1
  case hbltu_0 =>
    cases bltu_2 <;> cases bltu_1 <;>
      simpa [fullDivN2R1V5_eq_dispatch, fullDivN2R2V5_eq_dispatch] using hbltu_0
  case hcarry =>
    -- discharge from shape (#7461); flags trivial from clean form
    apply loopN2SelectedBorrowCarryV5_of_shape
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz
    · intro h; rw [← hbltu_2]; exact h
    · intro h; rw [← hbltu_2, h]; decide
    · intro h; rw [← hbltu_1]; exact h
    · intro h; rw [← hbltu_1, h]; decide
    · intro h; rw [← hbltu_0]; exact h
    · intro h; rw [← hbltu_0, h]; decide

end EvmAsm.Evm64
