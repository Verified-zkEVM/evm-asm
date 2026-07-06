/-
  EvmAsm.Evm64.SDiv.Compose.Words

  Pure word-level helpers shared by SDIV div-call composition files.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Evm64.EvmWordArith.Arithmetic
import EvmAsm.Rv64.BitAux

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.BitAux

/-- Conditional four-limb two's-complement negation by a Boolean `sign` word.
    `mask = 0 - sign` is `0` when `sign = 0` and all-ones when `sign = 1`, so a
    ripple-carry chain over `(limbᵢ ^^^ mask) + carryᵢ₋₁` (seeded with `sign`)
    yields the source word when `sign = 0` and its two's-complement negation when
    `sign = 1`. This is the shared kernel of every SDIV/SMOD sign/absolute-value
    and result-sign-fixup block; the per-operand defs below are thin
    specializations that only differ in how `sign` is computed. -/
def rippleNegWord (limb0 limb1 limb2 limb3 sign : Word) : EvmWord :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => sum0 | 1 => sum1 | 2 => sum2 | 3 => sum3

/-- Helper: `-v = ~~~v + 1` (two's complement for EvmWord). -/
private theorem evmWord_neg_eq_not_add (v : EvmWord) : -v = ~~~v + 1 := by bv_omega

/-- With `sign = 0` the ripple-negation is the identity: it returns the source
    word assembled from the four limbs. -/
theorem rippleNegWord_of_sign_zero
    (limb0 limb1 limb2 limb3 sign : Word) (hSign : sign = 0) :
    rippleNegWord limb0 limb1 limb2 limb3 sign =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => limb3 := by
  subst hSign
  unfold rippleNegWord
  simp (config := { zeta := true }) only
    [show (0 : Word) - 0 = 0 from rfl, ult_zero_false, word_xor_zero, word_add_zero,
     word_if_false_eq_zero]

/-- With `sign = 1` the ripple-negation computes the two's-complement negation of
    the word assembled from the four limbs. This is the single proof shared by
    every SDIV/SMOD `…_eq_neg_word_of_sign_one` wrapper. -/
theorem rippleNegWord_of_sign_one
    (limb0 limb1 limb2 limb3 sign : Word) (hSign : sign = 1) :
    rippleNegWord limb0 limb1 limb2 limb3 sign =
      -(EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => limb3) := by
  set v := EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => limb3) with hv
  have hv0 : v.getLimb 0 = limb0 := by rw [hv]; exact EvmWord.getLimb_fromLimbs
  have hv1 : v.getLimb 1 = limb1 := by rw [hv]; exact EvmWord.getLimb_fromLimbs
  have hv2 : v.getLimb 2 = limb2 := by rw [hv]; exact EvmWord.getLimb_fromLimbs
  have hv3 : v.getLimb 3 = limb3 := by rw [hv]; exact EvmWord.getLimb_fromLimbs
  have h1_0 : (1 : EvmWord).getLimb 0 = 1 := by decide
  have h1_1 : (1 : EvmWord).getLimb 1 = 0 := by decide
  have h1_2 : (1 : EvmWord).getLimb 2 = 0 := by decide
  have h1_3 : (1 : EvmWord).getLimb 3 = 0 := by decide
  have hNot : ∀ i : Fin 4, (~~~v).getLimb i = ~~~(v.getLimb i) :=
    fun _ => EvmWord.getLimb_not
  have hadd := EvmWord.add_carry_chain_correct (~~~v) 1
  simp (config := { zeta := true }) only [hNot, h1_0, h1_1, h1_2, h1_3] at hadd
  simp (config := { zeta := true }) only [ult_zero_false, word_if_false_eq_zero] at hadd
  -- Rewrite the carry chain in terms of the raw limbs (not `v.getLimb _`).
  simp only [hv0, hv1, hv2, hv3] at hadd
  subst hSign
  unfold rippleNegWord
  simp (config := { zeta := true }) only [word_zero_sub_one, word_xor_allOnes]
  rw [evmWord_neg_eq_not_add, ← EvmWord.fromLimbs_getLimb (~~~v + 1)]
  apply EvmWord.eq_iff_limbs.mpr; intro ⟨i, hi⟩
  rw [EvmWord.getLimb_fromLimbs, EvmWord.getLimb_fromLimbs]
  rcases i with _ | _ | _ | _ | j <;> [skip; skip; skip; skip; omega]
  all_goals dsimp only []
  · exact hadd.1.symm
  · have h := hadd.2.1; simp [BitVec.add_zero] at h; exact h.symm
  · have h := hadd.2.2.1; simp [BitVec.add_zero] at h; exact h.symm
  · have h := hadd.2.2.2; simp [BitVec.add_zero] at h; exact h.symm

/-- Absolute-value word produced by the SDIV dividend sign/absolute-value
    prefix, packaged as a named expression so downstream callable-composition
    proofs do not duplicate the expanded `fromLimbs` term. -/
def sdivAbsDividendWord
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) : EvmWord :=
  rippleNegWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
    (dividendTop >>> (63 : BitVec 6).toNat)

/-- Absolute-value word produced by the SDIV divisor sign/absolute-value
    prefix, paired with `sdivAbsDividendWord` for downstream composition
    statements that consume `divModStackDispatchPre`. -/
def sdivAbsDivisorWord
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmWord :=
  rippleNegWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
    (divisorTop >>> (63 : BitVec 6).toNat)

/-- Word produced by conditionally negating the unsigned quotient limbs by the
    SDIV result sign. This names the memory-result word of the result-sign
    fixup block before connecting it to the semantic `EvmWord.sdiv` result. -/
def sdivResultSignFixedWord
    (dividendTop divisorTop limb0 limb1 limb2 limb3 : Word) : EvmWord :=
  rippleNegWord limb0 limb1 limb2 limb3
    ((dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat))

/-- The SDIV result sign is the XOR of two top-bit extractions, hence it is a
    Boolean word. This keeps later result-sign-fix zero-quotient rewrites from
    reasoning about arbitrary 64-bit masks. -/
theorem sdivResultSign_bool (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 0 ∨ resultSign = 1 := by
  rcases ushr63_bool dividendTop with h1 | h1 <;>
  rcases ushr63_bool divisorTop with h2 | h2 <;>
  · simp only [bv6_63_toNat, h1, h2]
    first | (left; decide) | (right; decide)


/-- The SDIV result sign is zero exactly when the operand sign bits match. -/
theorem sdivResultSign_eq_zero_iff
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 0 ↔
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat := by
  rcases ushr63_bool dividendTop with h1 | h1 <;>
  rcases ushr63_bool divisorTop with h2 | h2 <;>
  · simp only [bv6_63_toNat, h1, h2]
    simp (config := { decide := true })

/-- The SDIV result sign is one exactly when the operand sign bits differ. -/
theorem sdivResultSign_eq_one_iff
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 1 ↔
      dividendTop >>> (63 : BitVec 6).toNat ≠
        divisorTop >>> (63 : BitVec 6).toNat := by
  rcases ushr63_bool dividendTop with h1 | h1 <;>
  rcases ushr63_bool divisorTop with h2 | h2 <;>
  · simp only [bv6_63_toNat, h1, h2]
    simp (config := { decide := true })


/-- Conditional negation by the SDIV result sign leaves the zero quotient
    limbs equal to zero. The carries may be used internally by the sign-fix
    block, but the four memory-result limbs remain zero. -/
theorem sdivResultSign_fixZeroLimbs
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum0 = 0 ∧ sum1 = 0 ∧ sum2 = 0 ∧ sum3 = 0 := by
  rcases ushr63_bool dividendTop with h1 | h1 <;>
  rcases ushr63_bool divisorTop with h2 | h2 <;>
  · simp only [bv6_63_toNat, h1, h2]
    decide

/-- Top output limb of result-sign-fix is zero when the unsigned quotient is
    zero. -/
theorem sdivResultSign_fixZeroLimb3
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum3 = 0 := by
  have h := sdivResultSign_fixZeroLimbs dividendTop divisorTop
  simpa using h.2.2.2

/-- Word-shaped variant of `sdivResultSign_fixZeroLimb3`, matching callers that
    have already rewritten a quotient word to `0 : EvmWord` but not yet
    simplified its `getLimbN` projections. -/
theorem sdivResultSign_fixZeroWordLimb3
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    let mask := (0 : Word) - resultSign
    let sum0 := (((0 : EvmWord).getLimbN 0) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := (((0 : EvmWord).getLimbN 1) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := (((0 : EvmWord).getLimbN 2) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := (((0 : EvmWord).getLimbN 3) ^^^ mask) + carry2
    sum3 = 0 := by
  rw [EvmWord.getLimbN_zero 0, EvmWord.getLimbN_zero 1,
    EvmWord.getLimbN_zero 2, EvmWord.getLimbN_zero 3]
  exact sdivResultSign_fixZeroLimb3 dividendTop divisorTop

/-- If the dividend sign bit is zero, the dividend absolute-value word is just
    the original four-limb word. -/
theorem sdivAbsDividendWord_of_sign_zero
    (limb0 limb1 limb2 top : Word)
    (hSign : top >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDividendWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => top := by
  unfold sdivAbsDividendWord
  exact rippleNegWord_of_sign_zero _ _ _ _ _ hSign

/-- Four concrete `getLimbN` projections assemble back to their source word. -/
theorem sdivWord_from_getLimbN (v : EvmWord) :
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1 | 2 => v.getLimbN 2 | 3 => v.getLimbN 3) =
      v := by
  have heq : (fun i : Fin 4 => match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1
      | 2 => v.getLimbN 2 | 3 => v.getLimbN 3) = v.getLimb := by
    apply funext; intro ⟨i, hi⟩
    rcases i with _ | _ | _ | _ | i
    all_goals (first | (exact (EvmWord.getLimbN_lt v _ (by omega)).symm) | omega)
  rw [heq]; exact EvmWord.fromLimbs_getLimb v

/-- Word-shaped variant of `sdivAbsDividendWord_of_sign_zero`: if the dividend
    sign bit is zero, the SDIV absolute-value helper returns the dividend word. -/
theorem sdivAbsDividendWord_eq_word_of_sign_zero
    (dividend : EvmWord)
    (hSign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3) = dividend := by
  rw [sdivAbsDividendWord_of_sign_zero _ _ _ _ hSign]
  exact sdivWord_from_getLimbN dividend

/-- If the dividend sign bit is one, the SDIV absolute-value helper returns the
    two's-complement negation of the dividend word. -/
theorem sdivAbsDividendWord_eq_neg_word_of_sign_one
    (dividend : EvmWord)
    (hSign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3) = -dividend := by
  unfold sdivAbsDividendWord
  rw [rippleNegWord_of_sign_one _ _ _ _ _ hSign, sdivWord_from_getLimbN]

/-- If the divisor sign bit is zero, the divisor absolute-value word is just the
    original four-limb word. -/
theorem sdivAbsDivisorWord_of_sign_zero
    (limb0 limb1 limb2 top : Word)
    (hSign : top >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDivisorWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => top := by
  unfold sdivAbsDivisorWord
  exact rippleNegWord_of_sign_zero _ _ _ _ _ hSign

/-- Word-shaped variant of `sdivAbsDivisorWord_of_sign_zero`: if the divisor
    sign bit is zero, the SDIV absolute-value helper returns the divisor word. -/
theorem sdivAbsDivisorWord_eq_word_of_sign_zero
    (divisor : EvmWord)
    (hSign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3) = divisor := by
  rw [sdivAbsDivisorWord_of_sign_zero _ _ _ _ hSign]
  exact sdivWord_from_getLimbN divisor

/-- If the divisor sign bit is one, the SDIV absolute-value helper returns the
    two's-complement negation of the divisor word. -/
theorem sdivAbsDivisorWord_eq_neg_word_of_sign_one
    (divisor : EvmWord)
    (hSign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3) = -divisor := by
  unfold sdivAbsDivisorWord
  rw [rippleNegWord_of_sign_one _ _ _ _ _ hSign, sdivWord_from_getLimbN]

/-- If the SDIV result sign is zero, the result-sign-fix word is just the
    unsigned quotient word assembled from its four limbs. -/
theorem sdivResultSignFixedWord_of_result_sign_zero
    (dividendTop divisorTop limb0 limb1 limb2 limb3 : Word)
    (hSign :
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat) = (0 : Word)) :
    sdivResultSignFixedWord dividendTop divisorTop limb0 limb1 limb2 limb3 =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => limb0 | 1 => limb1 | 2 => limb2 | 3 => limb3 := by
  unfold sdivResultSignFixedWord
  exact rippleNegWord_of_sign_zero _ _ _ _ _ hSign

/-- Word-shaped variant of `sdivResultSignFixedWord_of_result_sign_zero`: if
    the result sign is zero, the result-sign-fix helper leaves the quotient word
    unchanged. -/
theorem sdivResultSignFixedWord_eq_word_of_result_sign_zero
    (dividendTop divisorTop : Word) (quotient : EvmWord)
    (hSign :
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat) = (0 : Word)) :
    sdivResultSignFixedWord dividendTop divisorTop
      (quotient.getLimbN 0) (quotient.getLimbN 1)
      (quotient.getLimbN 2) (quotient.getLimbN 3) = quotient := by
  rw [sdivResultSignFixedWord_of_result_sign_zero _ _ _ _ _ _ hSign]
  exact sdivWord_from_getLimbN quotient

/-- If the SDIV result sign is one, the result-sign-fix helper returns the
    two's-complement negation of the quotient word. -/
theorem sdivResultSignFixedWord_eq_neg_word_of_result_sign_one
    (dividendTop divisorTop : Word) (quotient : EvmWord)
    (hSign :
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat) = (1 : Word)) :
    sdivResultSignFixedWord dividendTop divisorTop
      (quotient.getLimbN 0) (quotient.getLimbN 1)
      (quotient.getLimbN 2) (quotient.getLimbN 3) = -quotient := by
  unfold sdivResultSignFixedWord
  rw [rippleNegWord_of_sign_one _ _ _ _ _ hSign, sdivWord_from_getLimbN]

/-- The SDIV divisor absolute-value word is zero when all divisor limbs are
    zero. This discharges the internal bzero-branch hypothesis for the
    caller-visible zero-divisor stack case. -/
theorem sdivAbsDivisorWord_zero :
    sdivAbsDivisorWord 0 0 0 0 = 0 := by
  decide

/-- The SDIV divisor absolute-value normalization either leaves the word
    unchanged or computes its two's-complement negation, depending on the
    caller-visible sign bit. -/
theorem sdivAbsDivisorWord_sign_split
    (divisor : EvmWord) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      if divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = 0 then
        divisor
      else
        ~~~divisor + 1 := by
  rcases ushr63_bool (divisor.getLimbN 3) with h | h
  · simp only [bv6_63_toNat, h]
    exact sdivAbsDivisorWord_eq_word_of_sign_zero divisor (by simp [h])
  · have hne : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat ≠ 0 := by
      simp only [bv6_63_toNat, h]; decide
    simp only [if_neg hne]
    rw [← evmWord_neg_eq_not_add]
    exact sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor (by simp [h])

/-- The SDIV divisor absolute-value word is zero exactly for the zero
    divisor. This lets stack-level branch proofs switch between the
    caller-visible divisor and the unsigned-DIV dispatch divisor. -/
theorem sdivAbsDivisorWord_eq_zero_iff
    (divisor : EvmWord) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) = 0 ↔
      divisor = 0 := by
  constructor
  · intro h
    rw [sdivAbsDivisorWord_sign_split] at h
    split_ifs at h with hsign
    · exact h
    · -- h : ~~~divisor + 1 = 0 → divisor = 0; bv_omega handles this
      have : -divisor = 0 := by rw [evmWord_neg_eq_not_add]; exact h
      bv_omega
  · intro h; subst h
    simp only [EvmWord.getLimbN_zero]
    exact sdivAbsDivisorWord_zero

/-- Nonzero caller-visible divisors stay nonzero after the SDIV absolute-value
    normalization used by the unsigned-DIV dispatch. -/
theorem sdivAbsDivisorWord_ne_zero_of_ne_zero
    {divisor : EvmWord} (h_ne : divisor ≠ 0) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) ≠ 0 := by
  intro h_abs_zero
  exact h_ne ((sdivAbsDivisorWord_eq_zero_iff divisor).mp h_abs_zero)

/-- Nonnegative SDIV divisors are unchanged by absolute-value normalization. -/
theorem sdivAbsDivisorWord_zero_sign
    {divisor : EvmWord}
    (h_sign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      divisor := by
  rw [sdivAbsDivisorWord_sign_split, if_pos h_sign]

/-- Negative SDIV divisors normalize to their two's-complement negation. -/
theorem sdivAbsDivisorWord_one_sign
    {divisor : EvmWord}
    (h_sign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      ~~~divisor + 1 := by
  have h_not_zero :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat ≠ 0 := by
    rw [h_sign]
    decide
  rw [sdivAbsDivisorWord_sign_split, if_neg h_not_zero]

/-- Nonnegative raw-limb SDIV divisors are unchanged by absolute-value
    normalization. -/
theorem sdivAbsDivisorWord_zero_limb_sign
    {divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (h_sign : divisorTop >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => divisorLimb0
        | 1 => divisorLimb1
        | 2 => divisorLimb2
        | 3 => divisorTop := by
  exact sdivAbsDivisorWord_of_sign_zero _ _ _ _ h_sign

/-- Negative raw-limb SDIV divisors normalize to their two's-complement
    negation. -/
theorem sdivAbsDivisorWord_one_limb_sign
    {divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (h_sign : divisorTop >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => divisorLimb0
        | 1 => divisorLimb1
        | 2 => divisorLimb2
        | 3 => divisorTop) + 1 := by
  -- Let v = fromLimbs ...; then v.getLimbN k = limb_k for k < 4
  set v := EvmWord.fromLimbs (fun i : Fin 4 => match i with
    | 0 => divisorLimb0 | 1 => divisorLimb1 | 2 => divisorLimb2 | 3 => divisorTop) with hv_def
  have hv0 : v.getLimbN 0 = divisorLimb0 := by
    simp [hv_def, EvmWord.getLimbN_lt _ 0 (by omega), EvmWord.getLimb_fromLimbs]
  have hv1 : v.getLimbN 1 = divisorLimb1 := by
    simp [hv_def, EvmWord.getLimbN_lt _ 1 (by omega), EvmWord.getLimb_fromLimbs]
  have hv2 : v.getLimbN 2 = divisorLimb2 := by
    simp [hv_def, EvmWord.getLimbN_lt _ 2 (by omega), EvmWord.getLimb_fromLimbs]
  have hv3 : v.getLimbN 3 = divisorTop := by
    simp [hv_def, EvmWord.getLimbN_lt _ 3 (by omega), EvmWord.getLimb_fromLimbs]
  rw [← hv0, ← hv1, ← hv2, ← hv3, ← evmWord_neg_eq_not_add]
  exact sdivAbsDivisorWord_eq_neg_word_of_sign_one v (by rw [hv3, h_sign])

/-- Raw-limb SDIV divisor absolute-value normalization split by the
    caller-visible sign bit. -/
theorem sdivAbsDivisorWord_limb_sign_split
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      if divisorTop >>> (63 : BitVec 6).toNat = 0 then
        EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => divisorLimb0
          | 1 => divisorLimb1
          | 2 => divisorLimb2
          | 3 => divisorTop
      else
        ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => divisorLimb0
          | 1 => divisorLimb1
          | 2 => divisorLimb2
          | 3 => divisorTop) + 1 := by
  rcases ushr63_bool divisorTop with h | h
  · simp only [bv6_63_toNat, h]
    exact sdivAbsDivisorWord_of_sign_zero _ _ _ _ (by simp [h])
  · have hne : divisorTop >>> (63 : BitVec 6).toNat ≠ 0 := by
      simp only [bv6_63_toNat, h]; decide
    simp only [if_neg hne]
    exact sdivAbsDivisorWord_one_limb_sign (by simp [h])

/-- The SDIV dividend absolute-value normalization either leaves the word
    unchanged or computes its two's-complement negation, depending on the
    caller-visible sign bit. -/
theorem sdivAbsDividendWord_sign_split
    (dividend : EvmWord) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) =
      if dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = 0 then
        dividend
      else
        ~~~dividend + 1 := by
  rcases ushr63_bool (dividend.getLimbN 3) with h | h
  · simp only [bv6_63_toNat, h]
    exact sdivAbsDividendWord_eq_word_of_sign_zero dividend (by simp [h])
  · have hne : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat ≠ 0 := by
      simp only [bv6_63_toNat, h]; decide
    simp only [if_neg hne]
    rw [← evmWord_neg_eq_not_add]
    exact sdivAbsDividendWord_eq_neg_word_of_sign_one dividend (by simp [h])

/-- The SDIV dividend absolute-value word is zero exactly for the zero
    dividend. This mirrors the divisor bridge for semantic stack views that
    reason about wrapper-normalized operands. -/
theorem sdivAbsDividendWord_eq_zero_iff
    (dividend : EvmWord) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) = 0 ↔
      dividend = 0 := by
  constructor
  · intro h
    rw [sdivAbsDividendWord_sign_split] at h
    split_ifs at h with hsign
    · exact h
    · have : -dividend = 0 := by rw [evmWord_neg_eq_not_add]; exact h
      bv_omega
  · intro h; subst h
    rw [EvmWord.getLimbN_zero 0, EvmWord.getLimbN_zero 1,
        EvmWord.getLimbN_zero 2, EvmWord.getLimbN_zero 3]
    decide

/-- Nonzero caller-visible dividends stay nonzero after the SDIV
    absolute-value normalization. -/
theorem sdivAbsDividendWord_ne_zero_of_ne_zero
    {dividend : EvmWord} (h_ne : dividend ≠ 0) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) ≠ 0 := by
  intro h_abs_zero
  exact h_ne ((sdivAbsDividendWord_eq_zero_iff dividend).mp h_abs_zero)

/-- Nonnegative SDIV dividends are unchanged by absolute-value normalization. -/
theorem sdivAbsDividendWord_zero_sign
    {dividend : EvmWord}
    (h_sign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) =
      dividend := by
  rw [sdivAbsDividendWord_sign_split, if_pos h_sign]

/-- Negative SDIV dividends normalize to their two's-complement negation. -/
theorem sdivAbsDividendWord_one_sign
    {dividend : EvmWord}
    (h_sign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) =
      ~~~dividend + 1 := by
  have h_not_zero :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat ≠ 0 := by
    rw [h_sign]
    decide
  rw [sdivAbsDividendWord_sign_split, if_neg h_not_zero]

/-- Nonnegative raw-limb SDIV dividends are unchanged by absolute-value
    normalization. -/
theorem sdivAbsDividendWord_zero_limb_sign
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word}
    (h_sign : dividendTop >>> (63 : BitVec 6).toNat = 0) :
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => dividendLimb0
        | 1 => dividendLimb1
        | 2 => dividendLimb2
        | 3 => dividendTop := by
  exact sdivAbsDividendWord_of_sign_zero _ _ _ _ h_sign

/-- Negative raw-limb SDIV dividends normalize to their two's-complement
    negation. -/
theorem sdivAbsDividendWord_one_limb_sign
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word}
    (h_sign : dividendTop >>> (63 : BitVec 6).toNat = 1) :
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop =
      ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => dividendLimb0
        | 1 => dividendLimb1
        | 2 => dividendLimb2
        | 3 => dividendTop) + 1 := by
  set v := EvmWord.fromLimbs (fun i : Fin 4 => match i with
    | 0 => dividendLimb0 | 1 => dividendLimb1 | 2 => dividendLimb2 | 3 => dividendTop) with hv_def
  have hv0 : v.getLimbN 0 = dividendLimb0 := by
    simp [hv_def, EvmWord.getLimbN_lt _ 0 (by omega), EvmWord.getLimb_fromLimbs]
  have hv1 : v.getLimbN 1 = dividendLimb1 := by
    simp [hv_def, EvmWord.getLimbN_lt _ 1 (by omega), EvmWord.getLimb_fromLimbs]
  have hv2 : v.getLimbN 2 = dividendLimb2 := by
    simp [hv_def, EvmWord.getLimbN_lt _ 2 (by omega), EvmWord.getLimb_fromLimbs]
  have hv3 : v.getLimbN 3 = dividendTop := by
    simp [hv_def, EvmWord.getLimbN_lt _ 3 (by omega), EvmWord.getLimb_fromLimbs]
  rw [← hv0, ← hv1, ← hv2, ← hv3, ← evmWord_neg_eq_not_add]
  exact sdivAbsDividendWord_eq_neg_word_of_sign_one v (by rw [hv3, h_sign])

/-- Raw-limb SDIV dividend absolute-value normalization split by the
    caller-visible sign bit. -/
theorem sdivAbsDividendWord_limb_sign_split
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) :
    sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop =
      if dividendTop >>> (63 : BitVec 6).toNat = 0 then
        EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => dividendLimb0
          | 1 => dividendLimb1
          | 2 => dividendLimb2
          | 3 => dividendTop
      else
        ~~~(EvmWord.fromLimbs fun i : Fin 4 =>
          match i with
          | 0 => dividendLimb0
          | 1 => dividendLimb1
          | 2 => dividendLimb2
          | 3 => dividendTop) + 1 := by
  rcases ushr63_bool dividendTop with h | h
  · simp only [bv6_63_toNat, h]
    exact sdivAbsDividendWord_of_sign_zero _ _ _ _ (by simp [h])
  · have hne : dividendTop >>> (63 : BitVec 6).toNat ≠ 0 := by
      simp only [bv6_63_toNat, h]; decide
    simp only [if_neg hne]
    exact sdivAbsDividendWord_one_limb_sign (by simp [h])

/-- Word produced by conditionally negating four quotient limbs with the SDIV
    result sign. This names the post-result-sign-fix `fromLimbs` term so
    stack-level views can fold the four memory atoms into one `evmWordIs`. -/
def sdivSignFixedWord
    (sign limb0 limb1 limb2 limb3 : Word) : EvmWord :=
  rippleNegWord limb0 limb1 limb2 limb3 sign

/-- If the SDIV result sign is zero, result-sign fixup leaves the quotient
    word unchanged. -/
theorem sdivSignFixedWord_zero_sign (word : EvmWord) :
    sdivSignFixedWord 0
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      word := by
  unfold sdivSignFixedWord
  rw [rippleNegWord_of_sign_zero _ _ _ _ _ rfl, sdivWord_from_getLimbN]

/-- Conditional result-sign fixup maps a zero quotient to the zero word. -/
theorem sdivSignFixedWord_zero_quotient
    (dividendTop divisorTop : Word) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign 0 0 0 0 = 0 := by
  show sdivSignFixedWord ((dividendTop >>> 63) ^^^
    (divisorTop >>> 63)) 0 0 0 0 = 0
  rcases ushr63_bool dividendTop with hd | hd <;>
  rcases ushr63_bool divisorTop with hv | hv <;>
  · rw [hd, hv]; decide

/-- If the SDIV result sign is one, result-sign fixup computes two's-complement
    negation of the quotient word. -/
theorem sdivSignFixedWord_one_sign (word : EvmWord) :
    sdivSignFixedWord 1
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      ~~~word + 1 := by
  unfold sdivSignFixedWord
  rw [rippleNegWord_of_sign_one _ _ _ _ _ rfl, sdivWord_from_getLimbN,
    evmWord_neg_eq_not_add]

/-- Boolean result signs reduce result-sign fixup to either the original
    quotient word or its explicit two's-complement negation. -/
theorem sdivSignFixedWord_bool_sign
    (sign : Word) (h_sign : sign = 0 ∨ sign = 1) (word : EvmWord) :
    sdivSignFixedWord sign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      if sign = 0 then word else ~~~word + 1 := by
  obtain h_zero | h_one := h_sign
  · rw [h_zero, sdivSignFixedWord_zero_sign]
    simp
  · rw [h_one, sdivSignFixedWord_one_sign]
    simp

/-- Specialized boolean-sign split for the SDIV result sign derived from the
    operand top limbs. -/
theorem sdivSignFixedWord_result_sign
    (dividendTop divisorTop : Word) (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      if resultSign = 0 then word else ~~~word + 1 := by
  dsimp
  exact sdivSignFixedWord_bool_sign
    ((dividendTop >>> 63) ^^^ (divisorTop >>> 63))
    (sdivResultSign_bool dividendTop divisorTop) word

/-- Same operand signs make SDIV result-sign fixup leave the unsigned
    quotient word unchanged. -/
theorem sdivSignFixedWord_same_sign
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat)
    (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      word := by
  simp only [bv6_63_toNat] at h_sign
  show sdivSignFixedWord ((dividendTop >>> 63) ^^^
    (divisorTop >>> 63)) (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2)
    (word.getLimbN 3) = word
  have h_result : (dividendTop >>> 63) ^^^ (divisorTop >>> 63) = 0 := by
    simp only [h_sign, BitVec.xor_self]; rfl
  rw [h_result]
  exact sdivSignFixedWord_zero_sign word

/-- Opposite operand signs make SDIV result-sign fixup compute the
    two's-complement negation of the unsigned quotient word. -/
theorem sdivSignFixedWord_opposite_sign
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat ≠
        divisorTop >>> (63 : BitVec 6).toNat)
    (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      ~~~word + 1 := by
  simp only [bv6_63_toNat] at h_sign
  show sdivSignFixedWord ((dividendTop >>> 63) ^^^
    (divisorTop >>> 63)) (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2)
    (word.getLimbN 3) = ~~~word + 1
  have h_result : (dividendTop >>> 63) ^^^ (divisorTop >>> 63) = 1 := by
    rcases ushr63_bool dividendTop with hd | hd <;>
    rcases ushr63_bool divisorTop with hv | hv <;>
    simp only [hd, hv] at h_sign ⊢ <;>
    first | decide | exact absurd rfl h_sign
  rw [h_result]
  exact sdivSignFixedWord_one_sign word

/-- SDIV result-sign fixup split directly by equality of the operand sign
    bits. This is the caller-facing branch condition used by the final stack
    spec. -/
theorem sdivSignFixedWord_sign_bits
    (dividendTop divisorTop : Word) (word : EvmWord) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    sdivSignFixedWord resultSign
      (word.getLimbN 0) (word.getLimbN 1) (word.getLimbN 2) (word.getLimbN 3) =
      if dividendTop >>> (63 : BitVec 6).toNat =
          divisorTop >>> (63 : BitVec 6).toNat then
        word
      else
        ~~~word + 1 := by
  by_cases h_sign :
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat
  · rw [if_pos h_sign]
    exact sdivSignFixedWord_same_sign h_sign word
  · rw [if_neg h_sign]
    exact sdivSignFixedWord_opposite_sign h_sign word

/-- Equal SDIV operand sign bits make the result sign zero. -/
theorem sdivResultSign_zero_of_eq
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat =
        divisorTop >>> (63 : BitVec 6).toNat) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 0 := by
  simp only [bv6_63_toNat] at h_sign
  show (dividendTop >>> 63) ^^^ (divisorTop >>> 63) = 0
  simp only [h_sign, BitVec.xor_self]
  rfl

/-- Distinct SDIV operand sign bits make the result sign one. -/
theorem sdivResultSign_one_of_ne
    {dividendTop divisorTop : Word}
    (h_sign :
      dividendTop >>> (63 : BitVec 6).toNat ≠
        divisorTop >>> (63 : BitVec 6).toNat) :
    let resultSign :=
      (dividendTop >>> (63 : BitVec 6).toNat) ^^^
        (divisorTop >>> (63 : BitVec 6).toNat)
    resultSign = 1 := by
  simp only [bv6_63_toNat] at h_sign
  show (dividendTop >>> 63) ^^^ (divisorTop >>> 63) = 1
  rcases ushr63_bool dividendTop with hd | hd <;>
  rcases ushr63_bool divisorTop with hv | hv <;>
  simp only [hd, hv] at h_sign ⊢ <;>
  first | decide | exact absurd rfl h_sign

end EvmAsm.Evm64.SDiv.Compose
