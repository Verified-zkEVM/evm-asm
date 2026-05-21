/-
  EvmAsm.Evm64.SMod.Compose.Words

  Pure word-level helpers for SMOD composition files.
-/

import EvmAsm.Evm64.SDiv.Compose.Words

namespace EvmAsm.Evm64.SMod.Compose

/-- Absolute-value word produced by the SMOD dividend sign/absolute-value
    prefix. The computation matches SDIV; SMOD differs only in the final result
    sign, which follows the dividend sign. -/
def smodAbsDividendWord
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) : EvmWord :=
  EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord
    dividendLimb0 dividendLimb1 dividendLimb2 dividendTop

/-- Absolute-value word produced by the SMOD divisor sign/absolute-value
    prefix. -/
def smodAbsDivisorWord
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmWord :=
  EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord
    divisorLimb0 divisorLimb1 divisorLimb2 divisorTop

/-- Word produced by conditionally negating the unsigned modulo limbs by the
    SMOD result sign. For SMOD, the result sign is the dividend sign bit. -/
def smodResultSignFixedWord
    (dividendTop limb0 limb1 limb2 limb3 : Word) : EvmWord :=
  let resultSign := dividendTop >>> (63 : BitVec 6).toNat
  let mask := (0 : Word) - resultSign
  let sum0 := (limb0 ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => sum0 | 1 => sum1 | 2 => sum2 | 3 => sum3

/-- The SMOD result sign is the dividend top bit, hence it is a Boolean word. -/
theorem smodResultSign_bool (dividendTop : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    resultSign = 0 ∨ resultSign = 1 := by
  dsimp
  bv_decide

/-- Conditional negation by the SMOD result sign leaves zero modulo limbs
    equal to zero. -/
theorem smodResultSign_fixZeroLimbs
    (dividendTop : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum0 = 0 ∧ sum1 = 0 ∧ sum2 = 0 ∧ sum3 = 0 := by
  dsimp
  bv_decide

/-- Top output limb of SMOD result-sign-fix is zero when the unsigned modulo
    result is zero. -/
theorem smodResultSign_fixZeroLimb3
    (dividendTop : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum3 = 0 := by
  have h := smodResultSign_fixZeroLimbs dividendTop
  simpa using h.2.2.2

/-- Four concrete `getLimbN` projections assemble back to their source word. -/
theorem smodWord_from_getLimbN (v : EvmWord) :
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1 | 2 => v.getLimbN 2 | 3 => v.getLimbN 3) =
      v := by
  exact EvmAsm.Evm64.SDiv.Compose.sdivWord_from_getLimbN v

/-- If the dividend sign bit is zero, the SMOD absolute-value helper returns
    the dividend word. -/
theorem smodAbsDividendWord_eq_word_of_sign_zero
    (dividend : EvmWord)
    (hSign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3) = dividend := by
  simpa [smodAbsDividendWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord_eq_word_of_sign_zero dividend hSign

/-- If the dividend sign bit is one, the SMOD absolute-value helper returns
    the two's-complement negation of the dividend word. -/
theorem smodAbsDividendWord_eq_neg_word_of_sign_one
    (dividend : EvmWord)
    (hSign : dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3) = -dividend := by
  simpa [smodAbsDividendWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord_eq_neg_word_of_sign_one dividend hSign

/-- If the divisor sign bit is zero, the SMOD absolute-value helper returns the
    divisor word. -/
theorem smodAbsDivisorWord_eq_word_of_sign_zero
    (divisor : EvmWord)
    (hSign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3) = divisor := by
  simpa [smodAbsDivisorWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord_eq_word_of_sign_zero divisor hSign

/-- If the divisor sign bit is one, the SMOD absolute-value helper returns the
    two's-complement negation of the divisor word. -/
theorem smodAbsDivisorWord_eq_neg_word_of_sign_one
    (divisor : EvmWord)
    (hSign : divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3) = -divisor := by
  simpa [smodAbsDivisorWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor hSign

/-- The SMOD divisor absolute-value word is zero when all divisor limbs are
    zero. -/
theorem smodAbsDivisorWord_zero :
    smodAbsDivisorWord 0 0 0 0 = 0 := by
  simpa [smodAbsDivisorWord] using EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord_zero

/-- The SMOD divisor absolute-value word is zero exactly for the zero divisor. -/
theorem smodAbsDivisorWord_eq_zero_iff
    (divisor : EvmWord) :
    smodAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) = 0 ↔
      divisor = 0 := by
  simpa [smodAbsDivisorWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord_eq_zero_iff divisor

/-- Nonzero caller-visible divisors stay nonzero after SMOD absolute-value
    normalization used by the unsigned-MOD dispatch. -/
theorem smodAbsDivisorWord_ne_zero_of_ne_zero
    {divisor : EvmWord} (h_ne : divisor ≠ 0) :
    smodAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) ≠ 0 := by
  intro h_abs_zero
  exact h_ne ((smodAbsDivisorWord_eq_zero_iff divisor).mp h_abs_zero)

/-- If the SMOD result sign is zero, the result-sign-fix helper leaves the
    unsigned modulo word unchanged. -/
theorem smodResultSignFixedWord_eq_word_of_result_sign_zero
    (dividendTop : Word) (modulus : EvmWord)
    (hSign : dividendTop >>> (63 : BitVec 6).toNat = (0 : Word)) :
    smodResultSignFixedWord dividendTop
      (modulus.getLimbN 0) (modulus.getLimbN 1)
      (modulus.getLimbN 2) (modulus.getLimbN 3) = modulus := by
  unfold smodResultSignFixedWord EvmWord.fromLimbs
  rw [hSign]
  unfold EvmWord.getLimbN EvmWord.getLimb
  bv_decide

/-- If the SMOD result sign is one, the result-sign-fix helper returns the
    two's-complement negation of the unsigned modulo word. -/
theorem smodResultSignFixedWord_eq_neg_word_of_result_sign_one
    (dividendTop : Word) (modulus : EvmWord)
    (hSign : dividendTop >>> (63 : BitVec 6).toNat = (1 : Word)) :
    smodResultSignFixedWord dividendTop
      (modulus.getLimbN 0) (modulus.getLimbN 1)
      (modulus.getLimbN 2) (modulus.getLimbN 3) = -modulus := by
  unfold smodResultSignFixedWord EvmWord.fromLimbs
  rw [hSign]
  unfold EvmWord.getLimbN EvmWord.getLimb
  simp only [Neg.neg]
  bv_decide

/-- The SMOD dividend absolute-value word is zero exactly for the zero
    dividend. -/
theorem smodAbsDividendWord_eq_zero_iff
    (dividend : EvmWord) :
    smodAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) = 0 ↔
      dividend = 0 := by
  simpa [smodAbsDividendWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord_eq_zero_iff dividend

/-- Nonzero caller-visible dividends stay nonzero after SMOD absolute-value
    normalization. -/
theorem smodAbsDividendWord_ne_zero_of_ne_zero
    {dividend : EvmWord} (h_ne : dividend ≠ 0) :
    smodAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) ≠ 0 := by
  intro h_abs_zero
  exact h_ne ((smodAbsDividendWord_eq_zero_iff dividend).mp h_abs_zero)

/-- The SMOD dividend absolute-value normalization either leaves the word
    unchanged or computes its two's-complement negation. -/
theorem smodAbsDividendWord_sign_split
    (dividend : EvmWord) :
    smodAbsDividendWord
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3) =
      if dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = 0 then
        dividend
      else
        ~~~dividend + 1 := by
  simpa [smodAbsDividendWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord_sign_split dividend

/-- The SMOD divisor absolute-value normalization either leaves the word
    unchanged or computes its two's-complement negation. -/
theorem smodAbsDivisorWord_sign_split
    (divisor : EvmWord) :
    smodAbsDivisorWord
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) =
      if divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = 0 then
        divisor
      else
        ~~~divisor + 1 := by
  simpa [smodAbsDivisorWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord_sign_split divisor

/-- Raw-limb SMOD dividend absolute-value normalization split by the
    caller-visible sign bit. -/
theorem smodAbsDividendWord_limb_sign_split
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) :
    smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop =
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
  simpa [smodAbsDividendWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord_limb_sign_split
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop

/-- Raw-limb SMOD divisor absolute-value normalization split by the
    caller-visible sign bit. -/
theorem smodAbsDivisorWord_limb_sign_split
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) :
    smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
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
  simpa [smodAbsDivisorWord] using
    EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord_limb_sign_split
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop

end EvmAsm.Evm64.SMod.Compose
