/-
  EvmAsm.Evm64.SDiv.SpecSemantic

  Pure semantic result bridge for the top-level SDIV stack spec.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallDispatchZeroDivisor
import EvmAsm.Evm64.SDiv.Compose.DivCallExactReturnHandoff
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Evm64.SDiv.Compose

-- ============================================================================
-- Private helpers: kernel-checkable sign-bit lemmas
-- ============================================================================

/-- Extracting limb 3 from a 256-bit value equals `extractLsb' 192 64`. -/
private lemma limbN3_eq_extractLsb (v : EvmWord) :
    v.getLimbN 3 = v.extractLsb' 192 64 := by
  simp [EvmWord.getLimbN, EvmWord.getLimb]

/-- Bit 255 of a 256-bit word equals bit 63 of its top limb. -/
private lemma getLsbD_255_eq_extractLsb_192_63 (v : EvmWord) :
    v.getLsbD 255 = (v.extractLsb' 192 64).getLsbD 63 := by
  rw [BitVec.getLsbD_extractLsb', show (192 + 63 : Nat) = 255 from by omega]
  simp

/-- Bit 63 of a 64-bit word is the low bit of that word shifted right by 63. -/
private lemma getLsbD_63_eq_ushiftRight_63_bit0 (x : Word) :
    x.getLsbD 63 = (x >>> 63).getLsbD 0 := by
  simp [show (0 + 63 : Nat) < 64 from by omega]

/-- If the top 64-bit limb right-shifted by 63 equals zero, `msb` is `false`. -/
private lemma msb_false_of_limbN3_shift63_zero (v : EvmWord)
    (hSign : v.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    BitVec.msb v = false := by
  simp only [show (63 : BitVec 6).toNat = 63 from rfl] at hSign
  rw [limbN3_eq_extractLsb] at hSign
  simp only [BitVec.msb, BitVec.getMsbD, show (256 : Nat) - 1 - 0 = 255 from rfl]
  rw [getLsbD_255_eq_extractLsb_192_63, getLsbD_63_eq_ushiftRight_63_bit0, hSign]
  rfl

/-- If the top 64-bit limb right-shifted by 63 equals one, `msb` is `true`. -/
private lemma msb_true_of_limbN3_shift63_one (v : EvmWord)
    (hSign : v.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    BitVec.msb v = true := by
  simp only [show (63 : BitVec 6).toNat = 63 from rfl] at hSign
  rw [limbN3_eq_extractLsb] at hSign
  simp only [BitVec.msb, BitVec.getMsbD, show (256 : Nat) - 1 - 0 = 255 from rfl]
  rw [getLsbD_255_eq_extractLsb_192_63, getLsbD_63_eq_ushiftRight_63_bit0, hSign]
  rfl

/-- The top-limb sign bit (>>> 63) is either 0 or 1. -/
private lemma limbN3_shift63_cases (v : EvmWord) :
    v.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word) ∨
      v.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word) := by
  simp only [show (63 : BitVec 6).toNat = 63 from rfl]
  -- (v.getLimbN 3 >>> 63).toNat < 2^64 / 2^63 = 2 since getLimbN 3 .toNat < 2^64.
  have hlt : (v.getLimbN 3 >>> 63).toNat < 2 := by
    have hx := (v.getLimbN 3).isLt
    simp only [BitVec.toNat_ushiftRight]
    omega
  rcases (show (v.getLimbN 3 >>> 63).toNat = 0 ∨ (v.getLimbN 3 >>> 63).toNat = 1 from by omega)
    with h0 | h1
  · left; exact BitVec.eq_of_toNat_eq (by simpa using h0)
  · right; exact BitVec.eq_of_toNat_eq (by simpa using h1)

/-- Nonnegative/nonnegative exact-path SDIV result bridge.

    When both input signs are zero, the assembly absolute-value helpers leave
    both operands unchanged and the result-sign-fix helper leaves the unsigned
    quotient unchanged. In that case `EvmWord.div` and `EvmWord.sdiv` agree. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_nonnegative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_word_of_sign_zero divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (0 : Word) := by
    rw [hDividendSign, hDivisorSign]; decide
  rw [sdivResultSignFixedWord_eq_word_of_result_sign_zero _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = false :=
    msb_false_of_limbN3_shift63_zero dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = false :=
    msb_false_of_limbN3_shift63_zero divisor hDivisorSign
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Negative/negative exact-path SDIV result bridge.

    When both input signs are one, the assembly absolute-value helpers produce
    `-dividend` and `-divisor`; the result sign is zero, so the result-sign-fix
    helper leaves the unsigned quotient unchanged. This is the `true,true`
    branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_neg_word_of_sign_one dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (0 : Word) := by
    rw [hDividendSign, hDivisorSign]; decide
  rw [sdivResultSignFixedWord_eq_word_of_result_sign_zero _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = true :=
    msb_true_of_limbN3_shift63_one dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = true :=
    msb_true_of_limbN3_shift63_one divisor hDivisorSign
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : -divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Nonnegative/negative exact-path SDIV result bridge.

    When only the divisor is negative, the assembly divisor absolute-value
    helper produces `-divisor` and result-sign-fix negates the unsigned
    quotient. This is the `false,true` branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_nonnegative_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (1 : Word) := by
    rw [hDividendSign, hDivisorSign]; decide
  rw [sdivResultSignFixedWord_eq_neg_word_of_result_sign_one _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = false :=
    msb_false_of_limbN3_shift63_zero dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = true :=
    msb_true_of_limbN3_shift63_one divisor hDivisorSign
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : -divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Negative/nonnegative exact-path SDIV result bridge.

    When only the dividend is negative, the assembly dividend absolute-value
    helper produces `-dividend` and result-sign-fix negates the unsigned
    quotient. This is the `true,false` branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_negative_nonnegative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_neg_word_of_sign_one dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_word_of_sign_zero divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (1 : Word) := by
    rw [hDividendSign, hDivisorSign]; decide
  rw [sdivResultSignFixedWord_eq_neg_word_of_result_sign_one _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = true :=
    msb_true_of_limbN3_shift63_one dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = false :=
    msb_false_of_limbN3_shift63_zero divisor hDivisorSign
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Exact-path SDIV result bridge for arbitrary operand signs.

    This dispatches over the two extracted sign bits and reuses the four
    sign-specific semantic bridges above. -/
theorem sdivResultSignFixedWord_eq_sdiv
    (dividend divisor : EvmWord) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  have hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word) ∨
        dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word) :=
    limbN3_shift63_cases dividend
  have hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word) ∨
        divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word) :=
    limbN3_shift63_cases divisor
  rcases hDividendSign with hDividendSign | hDividendSign
  · rcases hDivisorSign with hDivisorSign | hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_nonnegative
        dividend divisor hDividendSign hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_nonnegative_negative
        dividend divisor hDividendSign hDivisorSign
  · rcases hDivisorSign with hDivisorSign | hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_negative_nonnegative
        dividend divisor hDividendSign hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_negative
        dividend divisor hDividendSign hDivisorSign

end EvmAsm.Evm64
