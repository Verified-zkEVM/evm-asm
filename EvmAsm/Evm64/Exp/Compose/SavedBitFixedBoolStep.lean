/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoolStep

  Bool-indexed semantic result bridge for one fixed saved-bit EXP iteration.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Concrete accumulator word produced by one fixed-loop iteration, indexed by
    the consumed exponent bit. This packages the skip and cond-mul result
    shapes behind a single Bool for the future induction step. -/
def expTwoMulFixedBranchResult
    (bit : Bool) (a0 a1 a2 a3 r0 r1 r2 r3 : Word) : EvmWord :=
  if bit then
    expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3
  else
    expSquaringCallSquareW r0 r1 r2 r3

theorem expTwoMulFixedBranchResult_false
    (a0 a1 a2 a3 r0 r1 r2 r3 : Word) :
    expTwoMulFixedBranchResult false a0 a1 a2 a3 r0 r1 r2 r3 =
      expSquaringCallSquareW r0 r1 r2 r3 := by
  rfl

theorem expTwoMulFixedBranchResult_true
    (a0 a1 a2 a3 r0 r1 r2 r3 : Word) :
    expTwoMulFixedBranchResult true a0 a1 a2 a3 r0 r1 r2 r3 =
      expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3 := by
  rfl

theorem expTwoMulFixedBranchResult_decide_highBit_eq_squareW_of_zero
    {e a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hBitZero : (e >>> (63 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) = 0) :
    expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3 =
      expSquaringCallSquareW r0 r1 r2 r3 := by
  have hDecide :
      decide ((e >>> (63 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) ≠ 0) = false := by
    rw [hBitZero]
    decide
  rw [hDecide, expTwoMulFixedBranchResult_false]

theorem expTwoMulFixedBranchResult_decide_highBit_eq_condRw_of_ne_zero
    {e a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hBitNe : (e >>> (63 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) ≠ 0) :
    expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3 =
      expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3 := by
  have hDecide :
      decide ((e >>> (63 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) ≠ 0) = true := by
    exact decide_eq_true hBitNe
  rw [hDecide, expTwoMulFixedBranchResult_true]

theorem expTwoMulFixedAccumulatorStep_eq_branchResult
    {baseWord : EvmWord} {bit : Bool}
    {a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hBase : baseWord = expResultWord a0 a1 a2 a3) :
    expTwoMulFixedAccumulatorStep baseWord
        (expResultWord r0 r1 r2 r3) bit =
      expTwoMulFixedBranchResult bit a0 a1 a2 a3 r0 r1 r2 r3 := by
  cases bit
  · exact expTwoMulFixedAccumulatorStep_false_eq_squareW
      baseWord r0 r1 r2 r3
  · exact expTwoMulFixedAccumulatorStep_true_eq_condRw hBase

/-- Bool-unified semantic accumulator successor for the concrete branch result.

    The machine-level one-step proof can establish the output accumulator is
    `expTwoMulFixedBranchResult bit ...`; this lemma advances the semantic
    invariant for either branch without exposing separate skip/cond-mul names
    to the induction theorem. -/
theorem expTwoMulFixedAccumulatorInvariant_succ_of_branchResult
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) := by
  refine
    expTwoMulFixedAccumulatorInvariant_succ_of_step (bit := bit)
      hInv ?_ ?_
  · rw [expResultWord_getLimbN_self]
    exact (expTwoMulFixedAccumulatorStep_eq_branchResult hBase).symm
  · rw [hBit]
    exact expTwoMulFixedAccumulatorStep_eq_target_succ
      baseWord exponentWord hk

/-- The concrete high-bit branch condition agrees with the semantic processed
    exponent bit carried by the cursor invariant. -/
theorem expTwoMulFixedProcessedBit_eq_decide_highBit_ne_zero
    {exponentWord : EvmWord} {k : Nat} {e : Word}
    (hk : k < 256)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e) :
    decide ((e >>> (63 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) ≠ 0) =
      expTwoMulFixedProcessedBit exponentWord k := by
  have hBitWord :=
    expTwoMulFixedCursorInvariant_highBit_eq_processedBitWord hCursor hk
  rw [show (63 : BitVec 6).toNat = 63 by decide]
  rw [hBitWord]
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide

/-- Bool-unified no-reload invariant successor.

    This combines the semantic accumulator bridge with the cursor/control
    successor facts that do not depend on whether the cond-mul branch was
    taken. -/
theorem expTwoMulFixedNoReloadInvariants_succ_of_branchResult
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {e c6 ptr nextLimb evmSp a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1)
      (e <<< (1 : BitVec 6).toNat) ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp := by
  exact
    ⟨expTwoMulFixedAccumulatorInvariant_succ_of_branchResult
        hk hBase hBit hInv,
      expTwoMulFixedCursorInvariant_succ_of_control_no_reload
        hCursor hControl hC6,
      expTwoMulFixedControlInvariant_succ_no_reload hControl hC6⟩

/-- Bool-unified reload invariant successor.

    This is the reload counterpart to
    `expTwoMulFixedNoReloadInvariants_succ_of_branchResult`; only the control
    and cursor successor shape differs. -/
theorem expTwoMulFixedReloadInvariants_succ_of_branchResult
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {c6 ptr nextLimb nextNextLimb evmSp
      a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp := by
  exact
    ⟨expTwoMulFixedAccumulatorInvariant_succ_of_branchResult
        hk hBase hBit hInv,
      expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6,
      expTwoMulFixedControlInvariant_succ_reload
        hControl hC6 hNextNext⟩

/-- No-reload successor using the machine high-bit condition as the Bool index.

    This is the shape expected from the composed one-iteration path: the branch
    Bool is the actual `beq` condition, but the semantic proof only sees the
    processed exponent bit through the cursor invariant. -/
theorem expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e c6 ptr nextLimb evmSp a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1)
      (e <<< (1 : BitVec 6).toNat) ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp := by
  exact
    expTwoMulFixedNoReloadInvariants_succ_of_branchResult
      hk hBase
      (expTwoMulFixedProcessedBit_eq_decide_highBit_ne_zero
        hk hCursor)
      hCursor hControl hC6 hInv

/-- Reload successor using the machine high-bit condition as the Bool index. -/
theorem expTwoMulFixedReloadInvariants_succ_of_decideBranchResult
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e c6 ptr nextLimb nextNextLimb evmSp
      a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult
        (decide ((e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0))
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp := by
  exact
    expTwoMulFixedReloadInvariants_succ_of_branchResult
      hk hBase
      (expTwoMulFixedProcessedBit_eq_decide_highBit_ne_zero
        hk hCursor)
      hControl hC6 hNextNext hInv

end EvmAsm.Evm64.Exp.Compose
