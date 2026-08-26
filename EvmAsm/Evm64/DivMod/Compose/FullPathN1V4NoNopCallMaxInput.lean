/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMaxInput

  Bundled call/max/max/max proofs for the n=1 v4/no-NOP full DIV path.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMax

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1 jpred_2 jpred_3 slt_jpos_1 slt_jpos_2 slt_jpos_3)

/-- Bundled statement for the first j=3 call-body step of the N1
    call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxJ3ExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  cpsTripleWithin 224 (I.base + loopBodyOff) (I.base + loopBodyOff)
    (divCode_noNop_v4 I.base)
    (loopN1CallMaxmaxmaxScratchPreNoX1 I.sp
      I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
      I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem ** (.x1 ↦ᵣ I.raVal))
    (loopIterPostN1CallScratchNoX1 I.sp I.base (3 : Word)
      (divKTrialCallV4QHat I.u1 I.u0 I.v0)
      (divKTrialCallV4DLo I.v0)
      (divKTrialCallV4Un0 I.u0)
      (divKTrialCallV4ScratchOut I.u1 I.u0 I.v0 I.scratchMem)
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop **
      (.x1 ↦ᵣ I.raVal) **
      ((I.sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig2) **
      ((I.sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q2Old) **
      ((I.sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig1) **
      ((I.sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q1Old) **
      ((I.sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
        signExtend12 0) ↦ₘ I.u0Orig0) **
      ((I.sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q0Old))

/-- Prove the bundled first j=3 call-body step from the bundled input
    alignment and branch/carry hypotheses. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec
  exact divK_loop_n1_call_j3_exact_x1_framed_v4_noNop I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxExactInputHypotheses_carry2Call I hh))

theorem loopN1CallMaxmaxmaxExactInputHypotheses_selectedCarry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (h : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedCarryFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 := by
  unfold loopN1CallMaxmaxmaxExactInputHypotheses at h
  unfold loopN1CallMaxmaxmaxExactHypotheses at h
  exact h.2.2.2

theorem loopN1CallMaxmaxmaxExactInputHypotheses_carryMax2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
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
  have hselected := loopN1CallMaxmaxmaxExactInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.1

theorem loopN1CallMaxmaxmaxExactInputHypotheses_carryMax1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
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
  have hselected := loopN1CallMaxmaxmaxExactInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.2.1

theorem loopN1CallMaxmaxmaxExactInputHypotheses_carryMax0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
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
  have hselected := loopN1CallMaxmaxmaxExactInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  exact hselected.2.2.2

/-- Bundled statement for the j=2/j=1/j=0 all-max tail after the first
    j=3 call-body step in the N1 call/max/max/max exact path. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210ExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
    (divCode_noNop_v4 I.base)
    (loopN1Iter210PreWithScratchNoX1 I.sp
      I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
      I.v0 I.v1 I.v2 I.v3
      I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
      (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
      (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal))
    (loopN1Iter210PostNoX1 false false false I.sp I.base I.v0 I.v1 I.v2 I.v3
      I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      I.u0Orig1 I.u0Orig0 (I.base + div128CallRetOff) I.v0
      (divKTrialCallV4DLo I.v0) (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal))

/-- Prove the bundled all-max tail after the first j=3 call-body step. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpec
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  exact divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_carryMax2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_carryMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_carryMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)

/-- Actual assertion produced by the bundled j=3 call-body step, including
    the cells framed for the following all-max tail. -/
@[irreducible]
def loopN1CallMaxmaxmaxJ3PostInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  loopIterPostN1CallScratchNoX1 I.sp I.base (3 : Word)
    (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0)
    (divKTrialCallV4ScratchOut I.u1 I.u0 I.v0 I.scratchMem)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop **
  (.x1 ↦ᵣ I.raVal) **
  ((I.sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat +
    signExtend12 0) ↦ₘ I.u0Orig2) **
  ((I.sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q2Old) **
  ((I.sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat +
    signExtend12 0) ↦ₘ I.u0Orig1) **
  ((I.sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q1Old) **
  ((I.sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat +
    signExtend12 0) ↦ₘ I.u0Orig0) **
  ((I.sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ I.q0Old)

/-- Frame cells carried around the j=2/j=1/j=0 all-max tail after the
    bundled j=3 call-body step. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FrameInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  ((uBase3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) **
  (qAddr3 ↦ₘ r3.1) **
  (I.sp + signExtend12 3936 ↦ₘ divKTrialCallV4ScratchOut I.u1 I.u0 I.v0 I.scratchMem)

/-- The j=3 frame carried around the all-max tail is PC-free. -/
theorem loopN1CallMaxmaxmaxIter210FrameInput_pcFree
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    (loopN1CallMaxmaxmaxIter210FrameInput I).pcFree := by
  delta loopN1CallMaxmaxmaxIter210FrameInput
  pcFree

instance pcFreeInst_loopN1CallMaxmaxmaxIter210FrameInput
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    Assertion.PCFree (loopN1CallMaxmaxmaxIter210FrameInput I) :=
  ⟨loopN1CallMaxmaxmaxIter210FrameInput_pcFree I⟩

/-- Bundled framed all-max tail from the actual j=3 post to the final
    N1 call/max/max/max scratch post. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FramedExactInputSpec
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
    (divCode_noNop_v4 I.base)
    (loopN1CallMaxmaxmaxJ3PostInput I)
    (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal))

/-- The precondition required by the framed all-max tail after the actual
    bundled j=3 call-body step. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FramedPreInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  (loopN1Iter210PreWithScratchNoX1 I.sp
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal)) **
  loopN1CallMaxmaxmaxIter210FrameInput I

/-- Rearrange the actual bundled j=3 post into the framed all-max tail
    precondition. -/
theorem loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    ∀ h,
      loopN1CallMaxmaxmaxJ3PostInput I h →
      loopN1CallMaxmaxmaxIter210FramedPreInput I h := by
  intro h hp
  delta loopN1CallMaxmaxmaxJ3PostInput loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FrameInput at hp ⊢
  delta loopIterPostN1CallScratchNoX1 loopN1Iter210PreWithScratchNoX1
    loopN1Iter210Pre loopExitPostN1 loopExitPost at hp ⊢
  dsimp only at hp ⊢
  have hj' := jpred_3
  rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
      u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
  simp only [se12_32, se12_40, se12_48, se12_56] at hp ⊢
  unfold loopN1CallMaxmaxmaxR3
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- The post produced by framing the bundled all-max tail with the j=3
    q/top/scratch cells. -/
@[irreducible]
def loopN1CallMaxmaxmaxIter210FramedPostInput
    (I : LoopN1CallMaxmaxmaxExactInputs) : Assertion :=
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  (loopN1Iter210PostNoX1 false false false I.sp I.base I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 (I.base + div128CallRetOff) I.v0
    (divKTrialCallV4DLo I.v0) (divKTrialCallV4Un0 I.u0) ** (.x1 ↦ᵣ I.raVal)) **
  loopN1CallMaxmaxmaxIter210FrameInput I

/-- Rearrange the framed all-max tail post into the final bundled N1
    call/max/max/max scratch post. -/
theorem loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost
    (I : LoopN1CallMaxmaxmaxExactInputs) :
    ∀ h,
      loopN1CallMaxmaxmaxIter210FramedPostInput I h →
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) h := by
  intro h hp
  delta loopN1CallMaxmaxmaxIter210FramedPostInput
    loopN1CallMaxmaxmaxIter210FrameInput loopN1CallMaxmaxmaxScratchPostNoX1 at hp ⊢
  unfold loopN1CallMaxmaxmaxR3 at hp
  rw [sepConj_assoc'] at hp
  xperm_hyp hp

/-- The framed all-max tail over the compact pre/post assertions that sit
    between the j=3 call-body step and the final scratch post. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_noNop_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have H210 := divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxExactInputHypotheses_carryMax2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_carryMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxExactInputHypotheses_carryMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210FramedExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input I hh)

/-- Full bundled N1 call/max/max/max exact path: j=3 uses the v4 call
    path and j=2/j=1/j=0 all use the all-max path. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxExactInputSpec
  unfold loopN1CallMaxmaxmaxExactX1ScratchSpec
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input I hh
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec at Htail
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Final bundled N1 call/max/max/max exact path, with hypotheses supplied
    directly as path branch facts plus the universal carry2 assumption. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop_of_bltu
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
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
    (hcarry2 : Carry2NzAll I.v0 I.v1 I.v2 I.v3) :
    loopN1CallMaxmaxmaxExactInputSpec I := by
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop I halign
    (loopN1CallMaxmaxmaxExactInputHypotheses_of_bltu I
      hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxExactInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpec sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpec
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxExactInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max
    bundled inputs, with hypotheses supplied directly as path branch facts
    plus the universal carry2 assumption. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop_of_bltu
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
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
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1CallMaxmaxmaxExactInputSpec sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  exact fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    halign
    (fullDivN1CallMaxmaxmaxExactInputHypotheses_of_bltu sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hcarry2)


end EvmAsm.Evm64
