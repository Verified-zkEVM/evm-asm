/-
  EvmAsm.Evm64.DivMod.Spec.CallSkipUnconditional

  Unconditional wrappers for the n=4 call-skip stack specs.

  Split from `Spec/CallSkip.lean` to keep that file under the per-file
  size cap. Provides:
  - `isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm` (skip/addback dichotomy)
  - `evm_div_n4_call_skip_stack_spec_unconditional` (DIV, NOP variant)
  - `evm_div_n4_call_skip_stack_spec_unconditional_noNop` (DIV, no-NOP variant)
  - `evm_mod_n4_call_skip_stack_spec_unconditional_within` (MOD within-bound variant)
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallSkip
public import EvmAsm.Evm64.DivMod.Spec.CallSkipExactX1

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **`isSkipBorrowN4CallEvm` and `isAddbackBorrowN4CallEvm` are
    complementary** (CLOSED).

    The two predicates differ only in `=` vs `≠ 0` at the bottom level
    (an `if-then-1-else-0` indicator), so exactly one holds for any
    inputs. Useful for shift_nz top-level dispatchers that route to
    skip vs. addback paths. -/
theorem isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm (a b : EvmWord) :
    isSkipBorrowN4CallEvm a b ∨ isAddbackBorrowN4CallEvm a b := by
  rw [isSkipBorrowN4CallEvm_def, isAddbackBorrowN4CallEvm_def]
  unfold isSkipBorrowN4Call isAddbackBorrowN4Call
  simp only []
  by_cases h : (if BitVec.ult ((a.getLimbN 3) >>>
        ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (mulsubN4_c3 (div128Quot ((a.getLimbN 3) >>>
            ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))))
          ((b.getLimbN 0) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (((b.getLimbN 1) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 0) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 2) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 1) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((b.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          ((a.getLimbN 0) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (((a.getLimbN 1) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 0) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((a.getLimbN 2) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 1) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
            ((a.getLimbN 2) >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))))
        then (1 : Word) else 0) = (0 : Word)
  · exact Or.inl h
  · exact Or.inr h

/-- **v4 call-path skip/addback dichotomy** at the EvmWord predicate surface.

    This mirrors `isSkipBorrowN4CallEvm_or_isAddbackBorrowN4CallEvm`, but for
    the v4 trial-call surface. The two predicates split on the same mulsub
    borrow indicator, so one of skip/addback always holds. -/
theorem isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm (a b : EvmWord) :
    isSkipBorrowN4CallV4Evm a b ∨ isAddbackBorrowN4CallV4Evm a b := by
  rw [isSkipBorrowN4CallV4Evm_def, isAddbackBorrowN4CallV4Evm_def]
  unfold isSkipBorrowN4CallV4Ab isAddbackBorrowN4CallV4Ab
  unfold loopBodyN4CallSkipJ0BorrowV4 loopBodyN4CallAddbackBorrowV4
  simp only []
  let shift := (clzResult (b.getLimbN 3)).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := ((b.getLimbN 3) <<< (shift.toNat % 64)) |||
    ((b.getLimbN 2) >>> (antiShift.toNat % 64))
  let b2' := ((b.getLimbN 2) <<< (shift.toNat % 64)) |||
    ((b.getLimbN 1) >>> (antiShift.toNat % 64))
  let b1' := ((b.getLimbN 1) <<< (shift.toNat % 64)) |||
    ((b.getLimbN 0) >>> (antiShift.toNat % 64))
  let b0' := (b.getLimbN 0) <<< (shift.toNat % 64)
  let u4 := (a.getLimbN 3) >>> (antiShift.toNat % 64)
  let u3 := ((a.getLimbN 3) <<< (shift.toNat % 64)) |||
    ((a.getLimbN 2) >>> (antiShift.toNat % 64))
  let u2 := ((a.getLimbN 2) <<< (shift.toNat % 64)) |||
    ((a.getLimbN 1) >>> (antiShift.toNat % 64))
  let u1 := ((a.getLimbN 1) <<< (shift.toNat % 64)) |||
    ((a.getLimbN 0) >>> (antiShift.toNat % 64))
  let u0 := (a.getLimbN 0) <<< (shift.toNat % 64)
  let qHat := divKTrialCallV4QHat u4 u3 b3'
  let c3 := mulsubN4_c3 qHat b0' b1' b2' b3' u0 u1 u2 u3
  by_cases h : (if BitVec.ult u4 c3 then (1 : Word) else 0) = (0 : Word)
  · left
    unfold mulsubN4NoBorrow
    subst qHat
    subst c3
    simp only []
    exact h
  · right
    subst qHat
    subst c3
    exact h

/-- **`evm_div_n4_call_skip_stack_spec` without `hsem`** — discharges the
    semantic hypothesis from the call-trial preconditions (CLOSED).

    Wrapper that calls `evm_div_n4_call_skip_stack_spec` with
    `hsem := n4CallSkipSemanticHolds_of_call_trial _ _ hb3nz hshift_nz hbltu`,
    eliminating the externally-supplied semantic predicate from the API. -/
theorem evm_div_n4_call_skip_stack_spec_unconditional (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) :=
  evm_div_n4_call_skip_stack_spec sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
    (n4CallSkipSemanticHolds_of_call_trial a b hb3nz hshift_nz hbltu)

/-- No-NOP variant of `evm_div_n4_call_skip_stack_spec_unconditional`. -/
theorem evm_div_n4_call_skip_stack_spec_unconditional_noNop (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (divCode_noNop base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPost sp a b) :=
  evm_div_n4_call_skip_stack_spec_noNop sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
    (n4CallSkipSemanticHolds_of_call_trial a b hb3nz hshift_nz hbltu)


theorem evm_div_n4_call_skip_stack_spec_unconditional_exact_x1 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divN4CallSkipStackPostNoX1 sp a b **
        (.x9 ↦ᵣ signExtend12 (4095 : BitVec 12))) :=
  evm_div_n4_call_skip_stack_spec_exact_x1 sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
    (n4CallSkipSemanticHolds_of_call_trial a b hb3nz hshift_nz hbltu)

/-- **`evm_mod_n4_call_skip_stack_spec_within` without `hsem`** — same idea
    for MOD. -/
theorem evm_mod_n4_call_skip_stack_spec_unconditional_within (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTripleWithin 264 base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modN4CallSkipStackPost sp a b) :=
  evm_mod_n4_call_skip_stack_spec_within sp base a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
    (n4CallSkipSemanticHolds_of_call_trial a b hb3nz hshift_nz hbltu)

end EvmAsm.Evm64
