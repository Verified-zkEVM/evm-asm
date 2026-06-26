/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame

  Small control-invariant helpers for the fixed-loop induction frame.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

private theorem controlFrame_signExtend12_neg1_toNat :
    (signExtend12 (-1 : BitVec 12)).toNat = 2^64 - 1 := by
  decide

private theorem controlFrame_word_add_neg1_toNat
    {w : Word} (hPos : 1 ≤ w.toNat) :
    (w + signExtend12 (-1 : BitVec 12)).toNat = w.toNat - 1 := by
  rw [BitVec.toNat_add, controlFrame_signExtend12_neg1_toNat]
  rw [show w.toNat + (2^64 - 1) = (w.toNat - 1) + 2^64 from by
    have := w.isLt
    omega]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by have := w.isLt; omega)

@[irreducible]
def expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (-8 : BitVec 12)) +
    signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)

theorem expTwoMulFixedSavedNextLimbFrame_unfold
    {ptr nextNextLimb : Word} :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      ((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) := by
  delta expTwoMulFixedSavedNextLimbFrame
  rfl

theorem expTwoMulFixedSavedNextLimbFrame_pcFree
    (ptr nextNextLimb : Word) :
    (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb).pcFree := by
  rw [expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb) :=
  ⟨expTwoMulFixedSavedNextLimbFrame_pcFree ptr nextNextLimb⟩

@[irreducible]
def expTwoMulFixedSavedNextLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrame ptr
    (exponentWord.getLimbN (2 - (k + 1) / 64))

theorem expTwoMulFixedSavedNextLimbFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrame ptr
        (exponentWord.getLimbN (2 - (k + 1) / 64)) := by
  delta expTwoMulFixedSavedNextLimbFrameN
  rfl

theorem expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold, hNextNext]

theorem expTwoMulFixedSavedNextLimbFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr).pcFree := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedSavedNextLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) :=
  ⟨expTwoMulFixedSavedNextLimbFrameN_pcFree exponentWord k ptr⟩

theorem expTwoMulFixedSavedNextLimbFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 62) :
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_unfold]
  rw [expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  congr 1
  have hdiv : (k + 2) / 64 = (k + 1) / 64 := by
    omega
  rw [show (k + 1 + 1) / 64 = (k + 2) / 64 by ring, hdiv]

@[irreducible]
def expTwoMulFixedReloadLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrame ptr
    (exponentWord.getLimbN (1 - k / 64))

theorem expTwoMulFixedReloadLimbFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrame ptr
        (exponentWord.getLimbN (1 - k / 64)) := by
  delta expTwoMulFixedReloadLimbFrameN
  rfl

theorem expTwoMulFixedReloadLimbFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 63) :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_unfold]
  congr 1
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]

theorem expTwoMulFixedReloadLimbFrameN_succ_of_control_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr :=
  expTwoMulFixedReloadLimbFrameN_succ_no_reload
    (expTwoMulFixedControlInvariant_no_reload_mod hControl hC6)

theorem expTwoMulFixedControlInvariant_pre_reload_mod
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    k % 64 = 62 := by
  unfold expTwoMulFixedControlInvariant at hControl
  rcases hControl with ⟨hNat, _⟩
  have hPos : 1 ≤ c6.toNat := by
    rw [hNat]
    have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
    omega
  have hDec := controlFrame_word_add_neg1_toNat (w := c6) hPos
  rw [hDec, hNat] at hC6
  have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

theorem expTwoMulFixedControlInvariant_ordinary_no_reload_mod
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre :
      (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    k % 64 < 62 := by
  have hNoReload :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  by_contra hNot
  have hMod : k % 64 = 62 := by omega
  unfold expTwoMulFixedControlInvariant at hControl
  rcases hControl with ⟨hNat, _⟩
  have hPos : 1 ≤ c6.toNat := by
    rw [hNat]
    omega
  have hDec := controlFrame_word_add_neg1_toNat (w := c6) hPos
  apply hNotPre
  rw [hDec, hNat, hMod]

theorem expTwoMulFixedControlInvariant_step_cases
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∨
      (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1 ∨
      (c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
        (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1 ∧
        k % 64 < 62) := by
  by_cases hZero : c6 + signExtend12 (-1 : BitVec 12) = 0
  · exact Or.inl hZero
  · by_cases hPre :
        (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1
    · exact Or.inr (Or.inl hPre)
    · exact Or.inr (Or.inr
        ⟨hZero, hPre,
          expTwoMulFixedControlInvariant_ordinary_no_reload_mod
            hControl hZero hPre⟩)

theorem expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_pre_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 = 62) :
    expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_unfold]
  rw [expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  congr 1
  have hdiv : (k + 1 + 1) / 64 = (k + 1) / 64 + 1 := by
    omega
  rw [hdiv]
  have hCases : (k + 1) / 64 = 0 ∨ 1 ≤ (k + 1) / 64 := by
    omega
  rcases hCases with hZero | hGe
  · rw [hZero]
  · rw [Nat.sub_eq_zero_of_le (by omega : 2 ≤ (k + 1) / 64 + 1),
      Nat.sub_eq_zero_of_le hGe]

theorem expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_control_pre_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr := by
  apply expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_pre_reload
  exact expTwoMulFixedControlInvariant_pre_reload_mod hControl hC6

@[irreducible]
def expTwoMulFixedPreReloadFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
  expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
    (ptr + signExtend12 (-8 : BitVec 12))

theorem expTwoMulFixedPreReloadFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedPreReloadFrameN exponentWord k ptr =
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
        (ptr + signExtend12 (-8 : BitVec 12))) := by
  delta expTwoMulFixedPreReloadFrameN
  rfl

theorem expTwoMulFixedPreReloadFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    (expTwoMulFixedPreReloadFrameN exponentWord k ptr).pcFree := by
  rw [expTwoMulFixedPreReloadFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedPreReloadFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedPreReloadFrameN exponentWord k ptr) :=
  ⟨expTwoMulFixedPreReloadFrameN_pcFree exponentWord k ptr⟩

theorem expTwoMulFixedPreReloadFrameN_handoff_of_control
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedPreReloadFrameN exponentWord k ptr =
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  -- Use the address-parametric value lemma keyed on `k % 64 = 62`, extracted
  -- from the control invariant — avoids juggling `hControl`'s pointer argument
  -- (which would trigger a non-matching-atom def-eq blowup).
  have hMod : k % 64 = 62 :=
    expTwoMulFixedControlInvariant_pre_reload_mod hControl hC6
  rw [expTwoMulFixedPreReloadFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_eq_succ_reload_limb_of_pre_reload
      (ptr := ptr + signExtend12 (-8 : BitVec 12)) hMod]

theorem expTwoMulFixedReloadLimbFrameN_eq_of_reload_nextNext
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hMod : k % 64 = 63)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedReloadLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold, hNextNext]
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 + 1 := by
    omega
  rw [hdiv]
  have hCases : k / 64 = 0 ∨ k / 64 = 1 ∨ 2 ≤ k / 64 := by
    omega
  rcases hCases with hZero | hOne | hGe
  · rw [hZero]
  · rw [hOne]
  · rw [Nat.sub_eq_zero_of_le (by omega : 2 ≤ k / 64 + 1),
      Nat.sub_eq_zero_of_le (by omega : 1 ≤ k / 64)]

theorem expTwoMulFixedReloadLimbFrameN_eq_of_control_reload_nextNext
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedReloadLimbFrameN exponentWord k ptr :=
  expTwoMulFixedReloadLimbFrameN_eq_of_reload_nextNext
    (expTwoMulFixedControlInvariant_reload_mod hControl hC6)
    hNextNext

@[irreducible]
def expTwoMulFixedReloadTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
  expTwoMulFixedSavedNextLimbFrame (ptr + signExtend12 (-8 : BitVec 12))
    (exponentWord.getLimbN (0 - k / 64))

theorem expTwoMulFixedReloadTailFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
      expTwoMulFixedSavedNextLimbFrame
        (ptr + signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN (0 - k / 64))) := by
  delta expTwoMulFixedReloadTailFrameN
  rfl

theorem expTwoMulFixedReloadTailFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    (expTwoMulFixedReloadTailFrameN exponentWord k ptr).pcFree := by
  rw [expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedReloadTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedReloadTailFrameN exponentWord k ptr) :=
  ⟨expTwoMulFixedReloadTailFrameN_pcFree exponentWord k ptr⟩

theorem expTwoMulFixedReloadTailFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 63) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_succ_no_reload hMod]
  congr 1
  rw [expTwoMulFixedSavedNextLimbFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]

theorem expTwoMulFixedReloadTailFrameN_succ_of_control_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr :=
  expTwoMulFixedReloadTailFrameN_succ_no_reload
    (expTwoMulFixedControlInvariant_no_reload_mod hControl hC6)

theorem expTwoMulFixedReloadTailFrameN_second_eq_succ_reload_limb
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 = 63) :
    expTwoMulFixedSavedNextLimbFrame
        (ptr + signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN (0 - k / 64)) =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
        (ptr + signExtend12 (-8 : BitVec 12)) := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold]
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 + 1 := by
    omega
  rw [hdiv]
  have hCases : k / 64 = 0 ∨ 1 ≤ k / 64 := by
    omega
  rcases hCases with hZero | hGe
  · rw [hZero]
  · rw [Nat.sub_eq_zero_of_le (Nat.zero_le (k / 64)),
      Nat.sub_eq_zero_of_le (by omega : 1 ≤ k / 64 + 1)]

theorem expTwoMulFixedReloadTailFrameN_handoff
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 = 63) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expTwoMulFixedReloadTailFrameN_unfold,
    expTwoMulFixedReloadTailFrameN_second_eq_succ_reload_limb hMod]

theorem expTwoMulFixedReloadTailFrameN_handoff_of_control
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedReloadTailFrameN exponentWord k ptr =
      (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12))) :=
  expTwoMulFixedReloadTailFrameN_handoff
    (expTwoMulFixedControlInvariant_reload_mod hControl hC6)

@[irreducible]
def expTwoMulFixedControlDec (c6 : Word) : Word :=
  c6 + signExtend12 (-1 : BitVec 12)

theorem expTwoMulFixedControlDec_unfold {c6 : Word} :
    expTwoMulFixedControlDec c6 =
      c6 + signExtend12 (-1 : BitVec 12) := by
  delta expTwoMulFixedControlDec
  rfl

@[irreducible]
def expTwoMulFixedInductionFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) : Assertion :=
  if expTwoMulFixedControlDec c6 = (0 : Word) then
    expTwoMulFixedReloadTailFrameN exponentWord k ptr
  else if (expTwoMulFixedControlDec c6).toNat = 1 then
    expTwoMulFixedPreReloadFrameN exponentWord k ptr
  else
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr

theorem expTwoMulFixedInductionFrameN_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 = (0 : Word)) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr := by
  rw [expTwoMulFixedInductionFrameN]
  simp [hC6]

theorem expTwoMulFixedInductionFrameN_pre_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (expTwoMulFixedControlDec c6).toNat = 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr := by
  rw [expTwoMulFixedInductionFrameN]
  split
  · rename_i hZero
    have hNatZero :
        (expTwoMulFixedControlDec c6).toNat = 0 := by
      rw [hZero]
      decide
    omega
  · rfl

theorem expTwoMulFixedInductionFrameN_ordinary
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 ≠ (0 : Word))
    (hNotPre : (expTwoMulFixedControlDec c6).toNat ≠ 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedInductionFrameN]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl

theorem expTwoMulFixedInductionFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr :=
  expTwoMulFixedInductionFrameN_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)

theorem expTwoMulFixedInductionFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr :=
  expTwoMulFixedInductionFrameN_pre_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)

theorem expTwoMulFixedInductionFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr :=
  expTwoMulFixedInductionFrameN_ordinary
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hC6)
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hNotPre)

theorem expTwoMulFixedInductionFrameN_succ_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedInductionFrameN exponentWord (k + 1) 64
        (ptr + signExtend12 (-8 : BitVec 12)) =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
        (ptr + signExtend12 (-8 : BitVec 12)) := by
  apply expTwoMulFixedInductionFrameN_ordinary_of_control
  · decide
  · decide

theorem expTwoMulFixedControlInvariant_succ_reload_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr loadedLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr loadedLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedControlInvariant exponentWord (k + 1) 64
        (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1) 64
          (ptr + signExtend12 (-8 : BitVec 12)) =
        expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12)) := by
  exact ⟨expTwoMulFixedControlInvariant_succ_reload hControl hC6 hNext,
    expTwoMulFixedInductionFrameN_succ_reload⟩

theorem expTwoMulFixedInductionFrameN_step_cases_of_control
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
        expTwoMulFixedReloadTailFrameN exponentWord k ptr ∨
      expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
        expTwoMulFixedPreReloadFrameN exponentWord k ptr ∨
      (expTwoMulFixedInductionFrameN exponentWord k c6 ptr =
          expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr ∧
        k % 64 < 62) := by
  rcases expTwoMulFixedControlInvariant_step_cases hControl with
    hReload | hPre | ⟨hOrd, hNotPre, hMod⟩
  · exact Or.inl
      (expTwoMulFixedInductionFrameN_reload_of_control hReload)
  · exact Or.inr (Or.inl
      (expTwoMulFixedInductionFrameN_pre_reload_of_control hPre))
  · exact Or.inr (Or.inr
      ⟨expTwoMulFixedInductionFrameN_ordinary_of_control hOrd hNotPre,
        hMod⟩)

theorem expTwoMulFixedControlInvariant_succ_ordinary_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hSuccOrd : (k + 1) % 64 < 62) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  have hControlSucc :=
    expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
  have hSuccNotReload :
      c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12) ≠ 0 := by
    intro hReload
    have hMod :=
      expTwoMulFixedControlInvariant_reload_mod hControlSucc hReload
    omega
  have hSuccNotPre :
      (c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12)).toNat ≠ 1 := by
    intro hPre
    have hMod :=
      expTwoMulFixedControlInvariant_pre_reload_mod hControlSucc hPre
    omega
  exact ⟨hControlSucc,
    expTwoMulFixedInductionFrameN_ordinary_of_control
      hSuccNotReload hSuccNotPre⟩

theorem expTwoMulFixedControlInvariant_succ_pre_reload_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr := by
  have hNonzero : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 := by
    intro hZero
    have hNatZero : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by
      rw [hZero]
      decide
    omega
  have hControlSucc :=
    expTwoMulFixedControlInvariant_succ_no_reload hControl hNonzero
  have hReload :
      c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, controlFrame_signExtend12_neg1_toNat, hC6]
    decide
  exact ⟨hControlSucc,
    expTwoMulFixedInductionFrameN_reload_of_control hReload⟩

theorem expTwoMulFixedControlInvariant_succ_to_pre_reload_with_induction_frame
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hSuccPre :
      (c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr := by
  have hControlSucc :=
    expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
  exact ⟨hControlSucc,
    expTwoMulFixedInductionFrameN_pre_reload_of_control hSuccPre⟩

theorem expTwoMulFixedControlInvariant_succ_no_reload_induction_frame_cases
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    (expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr =
        expTwoMulFixedReloadTailFrameN exponentWord (k + 1) ptr) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedInductionFrameN exponentWord (k + 1)
            (c6 + signExtend12 (-1 : BitVec 12)) ptr =
          expTwoMulFixedPreReloadFrameN exponentWord (k + 1) ptr) ∨
      (expTwoMulFixedControlInvariant exponentWord (k + 1)
          (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp ∧
        expTwoMulFixedInductionFrameN exponentWord (k + 1)
            (c6 + signExtend12 (-1 : BitVec 12)) ptr =
          expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr ∧
        (k + 1) % 64 < 62) := by
  by_cases hReload :
      c6 + signExtend12 (-1 : BitVec 12) +
          signExtend12 (-1 : BitVec 12) = 0
  · have hControlSucc :=
      expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
    exact Or.inl
      ⟨hControlSucc, expTwoMulFixedInductionFrameN_reload_of_control hReload⟩
  · by_cases hSuccPre :
        (c6 + signExtend12 (-1 : BitVec 12) +
            signExtend12 (-1 : BitVec 12)).toNat = 1
    · exact Or.inr (Or.inl
        (expTwoMulFixedControlInvariant_succ_to_pre_reload_with_induction_frame
          hControl hC6 hSuccPre))
    · have hControlSucc :=
        expTwoMulFixedControlInvariant_succ_no_reload hControl hC6
      have hSuccOrd : (k + 1) % 64 < 62 :=
        expTwoMulFixedControlInvariant_ordinary_no_reload_mod
          hControlSucc hReload hSuccPre
      have hOrd :=
        expTwoMulFixedControlInvariant_succ_ordinary_with_induction_frame
          hControl hC6 hSuccOrd
      exact Or.inr (Or.inr ⟨hOrd.1, hOrd.2, hSuccOrd⟩)

theorem expTwoMulFixedInductionFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    (expTwoMulFixedInductionFrameN exponentWord k c6 ptr).pcFree := by
  rw [expTwoMulFixedInductionFrameN]
  split
  · exact expTwoMulFixedReloadTailFrameN_pcFree exponentWord k ptr
  · split
    · exact expTwoMulFixedPreReloadFrameN_pcFree exponentWord k ptr
    · exact expTwoMulFixedSavedNextLimbFrameN_pcFree exponentWord k ptr

instance pcFreeInst_expTwoMulFixedInductionFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedInductionFrameN exponentWord k c6 ptr) :=
  ⟨expTwoMulFixedInductionFrameN_pcFree exponentWord k c6 ptr⟩

@[irreducible]
def expTwoMulFixedDirectHeadFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) : Assertion :=
  if expTwoMulFixedControlDec c6 = (0 : Word) then
    expTwoMulFixedReloadTailFrameN exponentWord k ptr
  else if (expTwoMulFixedControlDec c6).toNat = 1 then
    expTwoMulFixedPreReloadFrameN exponentWord k ptr
  else
    expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr

theorem expTwoMulFixedDirectHeadFrameN_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 = (0 : Word)) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr := by
  rw [expTwoMulFixedDirectHeadFrameN]
  simp [hC6]

theorem expTwoMulFixedDirectHeadFrameN_pre_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (expTwoMulFixedControlDec c6).toNat = 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr := by
  rw [expTwoMulFixedDirectHeadFrameN]
  split
  · rename_i hZero
    have hNatZero :
        (expTwoMulFixedControlDec c6).toNat = 0 := by
      rw [hZero]
      decide
    omega
  · rfl

theorem expTwoMulFixedDirectHeadFrameN_ordinary
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : expTwoMulFixedControlDec c6 ≠ (0 : Word))
    (hNotPre : (expTwoMulFixedControlDec c6).toNat ≠ 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedDirectHeadFrameN]
  split
  · rename_i hZero
    exact False.elim (hC6 hZero)
  · rfl

theorem expTwoMulFixedDirectHeadFrameN_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedReloadTailFrameN exponentWord k ptr :=
  expTwoMulFixedDirectHeadFrameN_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)

theorem expTwoMulFixedDirectHeadFrameN_pre_reload_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedPreReloadFrameN exponentWord k ptr :=
  expTwoMulFixedDirectHeadFrameN_pre_reload (by
    rw [expTwoMulFixedControlDec_unfold]
    exact hC6)

theorem expTwoMulFixedDirectHeadFrameN_ordinary_of_control
    {exponentWord : EvmWord} {k : Nat} {c6 ptr : Word}
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (c6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr :=
  expTwoMulFixedDirectHeadFrameN_ordinary
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hC6)
    (by
      rw [expTwoMulFixedControlDec_unfold]
      exact hNotPre)

theorem expTwoMulFixedDirectHeadFrameN_pcFree
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    (expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr).pcFree := by
  rw [expTwoMulFixedDirectHeadFrameN]
  split
  · exact expTwoMulFixedReloadTailFrameN_pcFree exponentWord k ptr
  · split
    · exact expTwoMulFixedPreReloadFrameN_pcFree exponentWord k ptr
    · exact expTwoMulFixedSavedNextLimbFrameN_pcFree exponentWord (k + 1) ptr

instance pcFreeInst_expTwoMulFixedDirectHeadFrameN
    (exponentWord : EvmWord) (k : Nat) (c6 ptr : Word) :
    Assertion.PCFree
      (expTwoMulFixedDirectHeadFrameN exponentWord k c6 ptr) :=
  ⟨expTwoMulFixedDirectHeadFrameN_pcFree exponentWord k c6 ptr⟩

theorem expTwoMulFixedControlInvariant_nextLimb
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) := by
  exact hControl.2

theorem expTwoMulFixedControlInvariant_nextLimb_succ_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) := by
  have hMod :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  rw [expTwoMulFixedControlInvariant_nextLimb hControl]
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]

end EvmAsm.Evm64.Exp.Compose
