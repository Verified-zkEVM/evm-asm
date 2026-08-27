/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterState

  Bundled fixed-loop iteration state for the Nat-induction EXP path.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoolStep
public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCount

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The pure invariant carried by the fixed-loop induction:
    semantic accumulator, exponent cursor, semantic control counter, and
    machine remaining-iteration counter. -/
def expTwoMulFixedIterStateInvariant
    (baseWord exponentWord : EvmWord) (k : Nat)
    (iterCount e controlC6 ptr nextLimb evmSp : Word)
    (r0 r1 r2 r3 : Word) : Prop :=
  expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3 ∧
  expTwoMulFixedCursorInvariant exponentWord k e ∧
  expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb evmSp ∧
  expTwoMulFixedIterCountInvariant k iterCount

theorem expTwoMulFixedIterStateInvariant_zero
    (baseWord exponentWord : EvmWord) (ptr evmSp : Word) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord 0
      (256 : Word) (exponentWord.getLimbN 3) 64 ptr
      (exponentWord.getLimbN 2) evmSp 1 0 0 0 := by
  exact
    ⟨expTwoMulFixedAccumulatorInvariant_zero_one baseWord exponentWord,
      expTwoMulFixedCursorInvariant_zero exponentWord,
      expTwoMulFixedControlInvariant_zero exponentWord ptr evmSp,
      expTwoMulFixedIterCountInvariant_zero⟩

theorem expTwoMulFixedIterStateInvariant_succ_no_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {iterCount e controlC6 ptr nextLimb evmSp
      a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      (e <<< (1 : BitVec 6).toNat)
      (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) := by
  rcases hState with ⟨hAcc, hCursor, hControl, hCount⟩
  rcases expTwoMulFixedNoReloadInvariants_succ_of_branchResult
      hk hBase hBit hCursor hControl hC6 hAcc with
    ⟨hAccNext, hCursorNext, hControlNext⟩
  exact
    ⟨hAccNext, hCursorNext, hControlNext,
      expTwoMulFixedIterCountInvariant_succ hk hCount⟩

theorem expTwoMulFixedIterStateInvariant_succ_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {iterCount controlC6 ptr nextLimb nextNextLimb evmSp
      a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount nextLimb controlC6 ptr nextLimb evmSp r0 r1 r2 r3) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      nextLimb 64 (ptr + signExtend12 (-8 : BitVec 12))
      nextNextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) := by
  rcases hState with ⟨hAcc, _hCursor, hControl, hCount⟩
  rcases expTwoMulFixedReloadInvariants_succ_of_branchResult
      hk hBase hBit hControl hC6 hNextNext hAcc with
    ⟨hAccNext, hCursorNext, hControlNext⟩
  exact
    ⟨hAccNext, hCursorNext, hControlNext,
      expTwoMulFixedIterCountInvariant_succ hk hCount⟩

theorem expTwoMulFixedIterStateInvariant_full_result
    {baseWord exponentWord : EvmWord}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 256
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3) :
    expResultWord r0 r1 r2 r3 = EvmWord.exp baseWord exponentWord :=
  expTwoMulFixedAccumulatorInvariant_full hState.1

theorem expTwoMulFixedIterStateInvariant_full_count_zero
    {baseWord exponentWord : EvmWord}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 256
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3) :
    iterCount = 0 := by
  apply BitVec.eq_of_toNat_eq
  exact hState.2.2.2

theorem expTwoMulFixedIterStateInvariant_succ_count_ne_zero
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    (hk : k + 1 < 256)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3) :
    expTwoMulIterCountNew iterCount ≠ 0 :=
  expTwoMulFixedIterCountInvariant_succ_ne_zero hk hState.2.2.2

theorem expTwoMulFixedIterStateInvariant_succ_count_eq_zero
    {baseWord exponentWord : EvmWord}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 255
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3) :
    expTwoMulIterCountNew iterCount = 0 :=
  expTwoMulFixedIterCountInvariant_succ_eq_zero hState.2.2.2

@[irreducible]
def expTwoMulFixedIterStateAssertion
    (baseWord exponentWord : EvmWord) (k : Nat)
    (iterCount e controlC6 ptr nextLimb evmSp : Word)
    (r0 r1 r2 r3 : Word) : Assertion :=
  ⌜expTwoMulFixedIterStateInvariant baseWord exponentWord k
    iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3⌝

theorem expTwoMulFixedIterStateAssertion_unfold
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word} :
    expTwoMulFixedIterStateAssertion baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 =
      ⌜expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3⌝ := by
  delta expTwoMulFixedIterStateAssertion
  rfl

theorem expTwoMulFixedIterStateAssertion_pcFree
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word} :
    (expTwoMulFixedIterStateAssertion baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3).pcFree := by
  rw [expTwoMulFixedIterStateAssertion_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterStateAssertion
    (baseWord exponentWord : EvmWord) (k : Nat)
    (iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterStateAssertion baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3) :=
  ⟨expTwoMulFixedIterStateAssertion_pcFree⟩

theorem expTwoMulFixedIterStateAssertion_pure
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterStateAssertion baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
  rw [expTwoMulFixedIterStateAssertion_unfold] at h
  exact h.2

theorem expTwoMulFixedIterStateAssertion_full_result
    {baseWord exponentWord : EvmWord}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterStateAssertion baseWord exponentWord 256
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 ps) :
    expResultWord r0 r1 r2 r3 = EvmWord.exp baseWord exponentWord :=
  expTwoMulFixedIterStateInvariant_full_result
    (expTwoMulFixedIterStateAssertion_pure h)

theorem expTwoMulFixedIterStateAssertion_full_count_zero
    {baseWord exponentWord : EvmWord}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterStateAssertion baseWord exponentWord 256
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 ps) :
    iterCount = 0 :=
  expTwoMulFixedIterStateInvariant_full_count_zero
    (expTwoMulFixedIterStateAssertion_pure h)

theorem expTwoMulFixedIterStateAssertion_succ_count_ne_zero
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    {ps : PartialState}
    (hk : k + 1 < 256)
    (h :
      expTwoMulFixedIterStateAssertion baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 ps) :
    expTwoMulIterCountNew iterCount ≠ 0 :=
  expTwoMulFixedIterStateInvariant_succ_count_ne_zero hk
    (expTwoMulFixedIterStateAssertion_pure h)

theorem expTwoMulFixedIterStateAssertion_succ_count_eq_zero
    {baseWord exponentWord : EvmWord}
    {iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterStateAssertion baseWord exponentWord 255
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 ps) :
    expTwoMulIterCountNew iterCount = 0 :=
  expTwoMulFixedIterStateInvariant_succ_count_eq_zero
    (expTwoMulFixedIterStateAssertion_pure h)

theorem expTwoMulFixedIterStateAssertion_succ_no_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {iterCount e controlC6 ptr nextLimb evmSp
      a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (h :
      expTwoMulFixedIterStateAssertion baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      (e <<< (1 : BitVec 6).toNat)
      (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) :=
  expTwoMulFixedIterStateInvariant_succ_no_reload
    hk hBase hBit hC6 (expTwoMulFixedIterStateAssertion_pure h)

theorem expTwoMulFixedIterStateAssertion_succ_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {iterCount controlC6 ptr nextLimb nextNextLimb evmSp
      a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (h :
      expTwoMulFixedIterStateAssertion baseWord exponentWord k
        iterCount nextLimb controlC6 ptr nextLimb evmSp r0 r1 r2 r3 ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      nextLimb 64 (ptr + signExtend12 (-8 : BitVec 12))
      nextNextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) :=
  expTwoMulFixedIterStateInvariant_succ_reload
    hk hBase hBit hC6 hNextNext (expTwoMulFixedIterStateAssertion_pure h)

end EvmAsm.Evm64.Exp.Compose
