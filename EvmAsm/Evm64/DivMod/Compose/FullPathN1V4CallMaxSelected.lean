module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-only assumptions for the bundled N1 call/max/max/max input
    path. Unlike `loopN1CallMaxmaxmaxExactInputHypotheses`, this package
    does not carry a universal `Carry2NzAll` premise. -/
@[irreducible]
def loopN1CallMaxmaxmaxSelectedInputHypotheses
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  BitVec.ult I.u1 I.v0 ∧
  loopN1CallMaxmaxmaxBranchFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 ∧
  loopN1CallMaxmaxmaxSelectedCarryFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0

/-- Compatibility projection from the old exact-hypotheses bundle to the
    selected-only input package. -/
theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_of_exact
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses
  exact ⟨loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3 I hh,
    loopN1CallMaxmaxmaxExactInputHypotheses_branches I hh,
    loopN1CallMaxmaxmaxExactInputHypotheses_selectedCarry I hh⟩

/-- Build selected-only bundled N1 call/max/max/max hypotheses from bundled
    branch facts and selected carry facts. -/
theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_of_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0) :
    loopN1CallMaxmaxmaxSelectedInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses
  exact ⟨hbltu3, hbranches, hselected⟩

/-- Build selected-only bundled N1 call/max/max/max hypotheses directly from
    the four path branch facts and selected carry facts. -/
theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_of_bltu_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0) :
    loopN1CallMaxmaxmaxSelectedInputHypotheses I := by
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_of_branches I hbltu3
    (loopN1CallMaxmaxmaxBranchFacts_of_bltu
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
      hbltu2 hbltu1 hbltu0)
    hselected

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu3
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    BitVec.ult I.u1 I.v0 := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact hh.1

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact hh.2.1

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedCarryFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact hh.2.2

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarryIfBorrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_of_selected
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryCall
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    isAddbackCarry2NzN1CallV4
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop := by
  have hselected := loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.1

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowCall
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    isAddbackCarry2NzN1CallV4
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_call
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    isAddbackCarry2NzN1Max
      I.v0 I.v1 I.v2 I.v3 I.u0Orig2
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.2.2.1 := by
  have hselected := loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.1

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    selectedN1MaxCarryIfBorrow
      I.v0 I.v1 I.v2 I.v3 I.u0Orig2
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.2.1
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop).2.2.2.2.1 := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    isAddbackCarry2NzN1Max
      I.v0 I.v1 I.v2 I.v3 I.u0Orig1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.2.2.1 := by
  have hselected := loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.2.1

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    selectedN1MaxCarryIfBorrow
      I.v0 I.v1 I.v2 I.v3 I.u0Orig1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.2.1
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.2.2.2.1 := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    isAddbackCarry2NzN1Max
      I.v0 I.v1 I.v2 I.v3 I.u0Orig0
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.2.2.1 := by
  have hselected := loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.2.2

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    selectedN1MaxCarryIfBorrow
      I.v0 I.v1 I.v2 I.v3 I.u0Orig0
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.2.1
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.2.2.2.1 := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_max0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarryIfBorrow I hh)

/-- Bundled first j=3 call-body step over the full `divCode_v4` bundle,
    from selected-only input hypotheses. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4
  exact divK_loop_n1_call_j3_exact_x1_framed_v4 I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxSelectedInputHypotheses_carryCall I hh))

/-- Bundled all-max tail after the first j=3 call-body step over the full
    `divCode_v4` bundle, from selected-only input hypotheses. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpecV4
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h))

/-- Bundled all-max tail after the first j=3 call-body step over the full
    `divCode_v4` bundle, from selected-only input hypotheses, using
    conditional max carry evidence for taken addback branches. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_input_of_selected_if_borrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpecV4
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h))

/-- Bundled framed all-max tail pre/post over the full `divCode_v4` bundle,
    from selected-only input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have H210 := cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h))
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Bundled framed all-max tail pre/post over the full `divCode_v4` bundle,
    from selected-only input hypotheses, using conditional max carry evidence
    for taken addback branches. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected_if_borrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have H210 := cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h))
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over the full `divCode_v4` bundle, from
    selected-only input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxJ3PostInput I)
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) := by
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected I hh)

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over the full `divCode_v4` bundle, from
    selected-only input hypotheses, using conditional max carry evidence for
    taken addback branches. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_input_of_selected_if_borrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxJ3PostInput I)
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) := by
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected_if_borrow I hh)

/-- Full bundled N1 call/max/max/max exact path over the full `divCode_v4`
    bundle, using selected-only input hypotheses. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxExactInputSpecV4
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_input_of_selected I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4 at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_input_of_selected I hh
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Full bundled N1 call/max/max/max exact path over the full `divCode_v4`
    bundle, using selected-only input hypotheses and conditional max carry
    evidence for taken addback branches. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_of_selected_if_borrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxExactInputSpecV4
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_input_of_selected I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4 at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_input_of_selected_if_borrow I hh
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Bundled first j=3 call-body step over the full `divCode_v4` bundle,
    using the selected call carry from the bundled path facts. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4
  exact divK_loop_n1_call_j3_exact_x1_framed_v4 I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxExactInputHypotheses_carry2Call I hh))

/-- Bundled all-max tail after the first j=3 call-body step over the full
    `divCode_v4` bundle, routed through the selected-carry no-NOP wrapper. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpecV4
  have H := divK_loop_n1_call_iter210_exact_x1_framed_v4_noNop_input I hh
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpec at H
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    H

/-- Bundled framed all-max tail pre/post over the full `divCode_v4` bundle,
    routed through the selected-carry no-NOP wrapper. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input I hh)

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over the full `divCode_v4` bundle, routed
    through the selected-carry no-NOP wrapper. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxJ3PostInput I)
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) := by
  have H := divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input I hh
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec at H
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    H

/-- Selected-only hypotheses specialized to the canonical full-DIV n=1
    call/max/max/max bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxSelectedInputHypotheses (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxSelectedInputHypotheses
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Compatibility projection from the old canonical full-DIV n=1
    call/max/max/max exact hypotheses to the selected-only package. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_of_exact
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxExactInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses
  unfold fullDivN1CallMaxmaxmaxExactInputHypotheses at hh
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_of_exact
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    hh

/-- Build the canonical full-DIV n=1 call/max/max/max selected hypothesis
    wrapper directly from path branch facts and selected carry facts. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_of_bltu_selected
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1) :
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_of_bltu_selected
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (fullDivN1CallMaxmaxmaxExactInputs_hbltu3 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3)
    hbltu2 hbltu1 hbltu0 hselected

/-- Project the raw j=3 branch fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_hbltu3
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    BitVec.ult
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu3
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    hh

/-- Project the caller-facing j=3 trial predicate from canonical full-DIV
    n=1 call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_isTrial_j3
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    isTrialN1_j3 true a3 b0 := by
  have hraw :=
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses_hbltu3 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hh
  unfold isTrialN1_j3
  unfold fullDivN1NormU fullDivN1NormV fullDivN1AntiShift fullDivN1Shift at hraw
  exact hraw.symm

/-- Project the bundled branch facts from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_branches
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    loopN1CallMaxmaxmaxBranchFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1 := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_branches
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    hh

/-- Project the j=2 max-branch fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    hh

/-- Project the j=1 max-branch fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    hh

/-- Project the j=0 max-branch fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1 := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    hh

/-- Project the selected carry package from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1 := by
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    hh

/-- Project the j=3 call selected-carry fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_carryCall
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    isAddbackCarry2NzN1CallV4
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word) := by
  have hselected :=
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.1

/-- Project the j=2 max selected-carry fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_carryMax2
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    isAddbackCarry2NzN1Max
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.2.1
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.2.2.1
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.2.2.2.1 := by
  have hselected :=
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.1

/-- Project the j=1 max selected-carry fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_carryMax1
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    isAddbackCarry2NzN1Max
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.2.1
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.2.2.1
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.2.2.2.1 := by
  have hselected :=
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.2.1

/-- Project the j=0 max selected-carry fact from canonical full-DIV n=1
    call/max/max/max selected hypotheses. -/
theorem fullDivN1CallMaxmaxmaxSelectedInputHypotheses_carryMax0
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    isAddbackCarry2NzN1Max
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.2.1 := by
  have hselected :=
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.2.2

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs over the full `divCode_v4` bundle, using the selected-only
    input hypothesis surface. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_selected
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpecV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_of_selected
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs over the full `divCode_v4` bundle, using selected-only
    hypotheses and conditional max carry evidence for taken addback branches. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_selected_if_borrow
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpecV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_of_selected_if_borrow
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

end EvmAsm.Evm64
