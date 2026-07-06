/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFramePre

  With-state precondition helpers that instantiate the saved-limb induction
  frame selected by the fixed-loop control counter.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStatePre

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedIterPreNWithInductionFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) : Assertion :=
  expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
    e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
    (expTwoMulFixedInductionFrameN exponentWord k controlC6 ptr)

theorem expTwoMulFixedIterPreNWithInductionFrame_unfold
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedInductionFrameN exponentWord k controlC6 ptr) := by
  delta expTwoMulFixedIterPreNWithInductionFrame
  rfl

theorem expTwoMulFixedIterPreNWithInductionFrame_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11).pcFree := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterPreNWithInductionFrame
    (k : Nat) (baseWord exponentWord : EvmWord) (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11) :=
  ⟨expTwoMulFixedIterPreNWithInductionFrame_pcFree⟩

theorem expTwoMulFixedIterPreNWithInductionFrame_pure
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (hPre :
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold] at hPre
  exact expTwoMulFixedIterPreNWithStateFrame_pure hPre

theorem expTwoMulFixedIterPreNWithInductionFrame_pure_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
  obtain ⟨_, _, _, _, hPre, _⟩ := hPreR
  exact expTwoMulFixedIterPreNWithInductionFrame_pure hPre

theorem expTwoMulFixedIterPreNWithInductionFrame_pure_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
  obtain ⟨ps, _h_compat, hPreRps⟩ := hPreR
  exact expTwoMulFixedIterPreNWithInductionFrame_pure_from_framed_pre hPreRps

theorem expTwoMulFixedIterPreNWithInductionFrame_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (hPre :
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
      nextLimb evmSp :=
  (expTwoMulFixedIterPreNWithInductionFrame_pure hPre).2.2.1

theorem expTwoMulFixedIterPreNWithInductionFrame_control_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps) :
    expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
      nextLimb evmSp :=
  (expTwoMulFixedIterPreNWithInductionFrame_pure_from_framed_pre hPreR).2.2.1

theorem expTwoMulFixedIterPreNWithInductionFrame_control_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s) :
    expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
      nextLimb evmSp :=
  (expTwoMulFixedIterPreNWithInductionFrame_pure_from_holdsFor hPreR).2.2.1

theorem expTwoMulFixedIterPreNWithInductionFrame_nextLimb
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (hPre :
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ps) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) :=
  expTwoMulFixedControlInvariant_nextLimb
    (expTwoMulFixedIterPreNWithInductionFrame_control hPre)

theorem expTwoMulFixedIterPreNWithInductionFrame_nextLimb_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) :=
  expTwoMulFixedControlInvariant_nextLimb
    (expTwoMulFixedIterPreNWithInductionFrame_control_from_framed_pre hPreR)

theorem expTwoMulFixedIterPreNWithInductionFrame_nextLimb_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) := by
  obtain ⟨ps, _h_compat, hPreRps⟩ := hPreR
  exact expTwoMulFixedIterPreNWithInductionFrame_nextLimb_from_framed_pre hPreRps

theorem expTwoMulFixedIterPreNWithInductionFrame_nextLimb_succ_no_reload
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (hPre :
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ps)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) :=
  expTwoMulFixedControlInvariant_nextLimb_succ_no_reload
    (expTwoMulFixedIterPreNWithInductionFrame_control hPre) hC6

theorem expTwoMulFixedIterPreNWithInductionFrame_nextLimb_succ_no_reload_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) :=
  expTwoMulFixedControlInvariant_nextLimb_succ_no_reload
    (expTwoMulFixedIterPreNWithInductionFrame_control_from_framed_pre hPreR)
    hC6

theorem expTwoMulFixedIterPreNWithInductionFrame_nextLimb_succ_no_reload_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) := by
  obtain ⟨ps, _h_compat, hPreRps⟩ := hPreR
  exact expTwoMulFixedIterPreNWithInductionFrame_nextLimb_succ_no_reload_from_framed_pre
    hPreRps hC6

theorem expTwoMulFixedIterPreNWithInductionFrame_control_step_cases_from_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (hPre :
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ps) :
    controlC6 + signExtend12 (-1 : BitVec 12) = 0 ∨
      (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1 ∨
      (controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
        (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1 ∧
        k % 64 < 62) :=
  expTwoMulFixedControlInvariant_step_cases
    (expTwoMulFixedIterPreNWithInductionFrame_control hPre)

theorem expTwoMulFixedIterPreNWithInductionFrame_control_step_cases_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps) :
    controlC6 + signExtend12 (-1 : BitVec 12) = 0 ∨
      (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1 ∨
      (controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
        (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1 ∧
        k % 64 < 62) :=
  expTwoMulFixedControlInvariant_step_cases
    (expTwoMulFixedIterPreNWithInductionFrame_control_from_framed_pre hPreR)

theorem expTwoMulFixedIterPreNWithInductionFrame_control_step_cases_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s) :
    controlC6 + signExtend12 (-1 : BitVec 12) = 0 ∨
      (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1 ∨
      (controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
        (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1 ∧
        k % 64 < 62) := by
  obtain ⟨ps, _h_compat, hPreRps⟩ := hPreR
  exact expTwoMulFixedIterPreNWithInductionFrame_control_step_cases_from_framed_pre
    hPreRps

theorem expTwoMulFixedIterPreNWithInductionFrame_reload_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedReloadTailFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold,
    expTwoMulFixedInductionFrameN_reload_of_control hC6]

theorem expTwoMulFixedIterPreNWithInductionFrame_pre_reload_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold,
    expTwoMulFixedInductionFrameN_pre_reload_of_control hC6]

theorem expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold,
    expTwoMulFixedInductionFrameN_ordinary_of_control hC6 hNotPre]

theorem expTwoMulFixedIterPreNWithInductionFrame_reload_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedReloadTailFrameN exponentWord k ptr) ** R) ps := by
  rwa [← expTwoMulFixedIterPreNWithInductionFrame_reload_of_control hC6]

theorem expTwoMulFixedIterPreNWithInductionFrame_reload_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedReloadTailFrameN exponentWord k ptr) ** R).holdsFor s := by
  obtain ⟨ps, h_compat, hPreRps⟩ := hPreR
  exact ⟨ps, h_compat,
    expTwoMulFixedIterPreNWithInductionFrame_reload_from_framed_pre
      hPreRps hC6⟩

theorem expTwoMulFixedIterPreNWithInductionFrame_pre_reload_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedPreReloadFrameN exponentWord k ptr) ** R) ps := by
  rwa [← expTwoMulFixedIterPreNWithInductionFrame_pre_reload_of_control hC6]

theorem expTwoMulFixedIterPreNWithInductionFrame_pre_reload_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedPreReloadFrameN exponentWord k ptr) ** R).holdsFor s := by
  obtain ⟨ps, h_compat, hPreRps⟩ := hPreR
  exact ⟨ps, h_compat,
    expTwoMulFixedIterPreNWithInductionFrame_pre_reload_from_framed_pre
      hPreRps hC6⟩

theorem expTwoMulFixedIterPreNWithInductionFrame_ordinary_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) ** R) ps := by
  rwa [← expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
    hC6 hNotPre]

theorem expTwoMulFixedIterPreNWithInductionFrame_ordinary_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) ** R).holdsFor s := by
  obtain ⟨ps, h_compat, hPreRps⟩ := hPreR
  exact ⟨ps, h_compat,
    expTwoMulFixedIterPreNWithInductionFrame_ordinary_from_framed_pre
      hPreRps hC6 hNotPre⟩

theorem expTwoMulFixedIterPreNWithInductionFrame_step_cases_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
        nextLimb evmSp) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord k ptr) ∨
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedPreReloadFrameN exponentWord k ptr) ∨
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
            controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
            tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
            a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) ∧
        k % 64 < 62) := by
  rcases expTwoMulFixedControlInvariant_step_cases hControl with
    hReload | hPre | ⟨hOrd, hNotPre, hMod⟩
  · exact Or.inl
      (expTwoMulFixedIterPreNWithInductionFrame_reload_of_control hReload)
  · exact Or.inr (Or.inl
      (expTwoMulFixedIterPreNWithInductionFrame_pre_reload_of_control hPre))
  · exact Or.inr (Or.inr
      ⟨expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
          hOrd hNotPre,
        hMod⟩)

theorem expTwoMulFixedIterPreNWithInductionFrame_step_cases_from_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (hPre :
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord k ptr) ∨
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedPreReloadFrameN exponentWord k ptr) ∨
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
            controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
            tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
            a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) ∧
        k % 64 < 62) :=
  expTwoMulFixedIterPreNWithInductionFrame_step_cases_of_control
    (expTwoMulFixedIterPreNWithInductionFrame_control hPre)

theorem expTwoMulFixedIterPreNWithInductionFrame_step_cases_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord k ptr) ∨
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedPreReloadFrameN exponentWord k ptr) ∨
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
            controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
            tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
            a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) ∧
        k % 64 < 62) :=
  expTwoMulFixedIterPreNWithInductionFrame_step_cases_of_control
    (expTwoMulFixedIterPreNWithInductionFrame_control_from_framed_pre hPreR)

theorem expTwoMulFixedIterPreNWithInductionFrame_step_cases_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord k ptr) ∨
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedPreReloadFrameN exponentWord k ptr) ∨
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
            controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
            tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
            a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) ∧
        k % 64 < 62) := by
  obtain ⟨ps, _h_compat, hPreRps⟩ := hPreR
  exact expTwoMulFixedIterPreNWithInductionFrame_step_cases_from_framed_pre
    hPreRps

theorem expTwoMulFixedIterPreNWithInductionFrame_succ_no_reload_cases_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
        nextLimb evmSp)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    (expTwoMulFixedControlInvariant exponentWord (k + 1)
        (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
        (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
        v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) ∧
        (k + 1) % 64 < 62) := by
  rcases expTwoMulFixedControlInvariant_succ_no_reload_induction_frame_cases
      hControl hC6 with hReload | hPre | hOrd
  · exact Or.inl ⟨hReload.1, by
      rw [expTwoMulFixedIterPreNWithInductionFrame_unfold, hReload.2]⟩
  · exact Or.inr (Or.inl ⟨hPre.1, by
      rw [expTwoMulFixedIterPreNWithInductionFrame_unfold, hPre.2]⟩)
  · exact Or.inr (Or.inr ⟨hOrd.1, by
      rw [expTwoMulFixedIterPreNWithInductionFrame_unfold, hOrd.2.1],
      hOrd.2.2⟩)

theorem expTwoMulFixedIterPreNWithInductionFrame_succ_no_reload_cases_from_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (hPre :
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ps)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    (expTwoMulFixedControlInvariant exponentWord (k + 1)
        (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
        (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
        v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) ∧
        (k + 1) % 64 < 62) := by
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithInductionFrame_pure hPre
  exact
    expTwoMulFixedIterPreNWithInductionFrame_succ_no_reload_cases_of_control
      hState.2.2.1 hC6


theorem expTwoMulFixedIterPreNWithInductionFrame_succ_no_reload_cases_from_framed_pre
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {ps : PartialState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R) ps)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    (expTwoMulFixedControlInvariant exponentWord (k + 1)
        (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
        (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
        v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) ∧
        (k + 1) % 64 < 62) := by
  obtain ⟨_, _, _, _, hPre, _⟩ := hPreR
  exact
    expTwoMulFixedIterPreNWithInductionFrame_succ_no_reload_cases_from_pre
      hPre hC6

theorem expTwoMulFixedIterPreNWithInductionFrame_succ_no_reload_cases_from_holdsFor
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {R : Assertion} {s : MachineState}
    (hPreR :
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 ** R).holdsFor s)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    (expTwoMulFixedControlInvariant exponentWord (k + 1)
        (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
        (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
        v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr)) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedIterPreNWithInductionFrame (k + 1) baseWord exponentWord
          (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
          v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
          e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12)) e machineC6 iterCount
            v10 v18 ptr nextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) ∧
        (k + 1) % 64 < 62) := by
  obtain ⟨ps, _h_compat, hPreRps⟩ := hPreR
  exact expTwoMulFixedIterPreNWithInductionFrame_succ_no_reload_cases_from_framed_pre
    hPreRps hC6

end EvmAsm.Evm64.Exp.Compose
