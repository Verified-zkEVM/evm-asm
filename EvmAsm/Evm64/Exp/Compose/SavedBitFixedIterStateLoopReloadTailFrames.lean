/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadTailFrames

  Opaque continuation-frame definitions for reload-tail direct adapters.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expReloadTailDirectTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr nextNextLimb : Word) :
    Assertion :=
  expReloadDirectTailFrame ptr nextNextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expReloadTailDirectTailFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word} :
    expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb =
      (((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12)))) := by
  rw [expReloadTailDirectTailFrameN, expReloadDirectTailFrame_unfold]

@[irreducible]
def expReloadTailDirectFalseFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expReloadTailDirectFalseFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadTailDirectFalseFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) = 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expReloadTailDirectFalseFrameN, expReloadDirectFalseFrame_unfold]

@[irreducible]
def expReloadTailDirectTrueFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expReloadTailDirectTrueFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadTailDirectTrueFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expReloadTailDirectTrueFrameN, expReloadDirectTrueFrame_unfold]

end EvmAsm.Evm64.Exp.Compose
