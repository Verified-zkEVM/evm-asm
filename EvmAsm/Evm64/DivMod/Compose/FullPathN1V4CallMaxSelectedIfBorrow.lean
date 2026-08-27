/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelectedIfBorrow

  Selected-if-borrow input hypotheses for the n=1 v4 call/max/max/max path.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelected

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-if-borrow assumptions for the bundled N1 call/max/max/max input
    path. This package replaces unconditional max carry facts with facts
    needed only when each max step takes the addback branch. -/
@[irreducible]
def loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  BitVec.ult I.u1 I.v0 ∧
  loopN1CallMaxmaxmaxBranchFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 ∧
  loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0

/-- Compatibility projection from selected-only inputs to selected-if-borrow
    inputs. -/
theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
  exact ⟨hh.1, hh.2.1,
    loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_of_selected
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 hh.2.2⟩

/-- Build selected-if-borrow bundled N1 call/max/max/max hypotheses from
    bundled branch facts and conditional selected carry facts. -/
theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_of_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hbltu3 : BitVec.ult I.u1 I.v0)
    (hbranches : loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0) :
    loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
  exact ⟨hbltu3, hbranches, hselected⟩

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu3
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    BitVec.ult I.u1 I.v0 := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact hh.1

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact hh.2.1

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3
        I.uTop I.u0Orig2 I.u0Orig1).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 := by
  unfold loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact hh.2.2

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowCall
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    isAddbackCarry2NzN1CallV4
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop := by
  exact loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts_call
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
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
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
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
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

theorem loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
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
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_selectedCarryIfBorrow I hh)

/-- Bundled first j=3 call-body step over the full `divCode_v4` bundle,
    using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_input_of_selected_if_borrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4
  exact divK_loop_n1_call_j3_exact_x1_framed_v4 I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowCall I hh))

/-- Bundled all-max tail after the first j=3 call-body step over the full
    `divCode_v4` bundle, using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
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
      exact loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h))

/-- Bundled framed all-max tail pre/post over the full `divCode_v4` bundle,
    using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
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
      exact loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h))
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over the full `divCode_v4` bundle, using
    selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxJ3PostInput I)
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) := by
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected_if_borrow_input I hh)

/-- Full bundled N1 call/max/max/max exact path over the full `divCode_v4`
    bundle, using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxExactInputSpecV4
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_input_of_selected_if_borrow
    I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4 at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_input_of_selected_if_borrow_input
    I hh
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Selected-if-borrow hypotheses specialized to the canonical full-DIV n=1
    call/max/max/max bundled inputs. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)

/-- Build the canonical full-DIV n=1 call/max/max/max selected-if-borrow
    hypothesis wrapper directly from path branch facts and conditional
    selected carry facts. -/
theorem fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_of_bltu_selected
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
    (hselected : loopN1CallMaxmaxmaxSelectedCarryIfBorrowFacts
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
    fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses
  exact loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_of_branches
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (fullDivN1CallMaxmaxmaxExactInputs_hbltu3 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3)
    (loopN1CallMaxmaxmaxBranchFacts_of_bltu
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      hbltu2 hbltu1 hbltu0)
    hselected

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs over the full `divCode_v4` bundle, using the
    selected-if-borrow input hypothesis surface. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_of_selected_if_borrow_input
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpecV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpecV4
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_of_selected_if_borrow_input
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

end EvmAsm.Evm64
