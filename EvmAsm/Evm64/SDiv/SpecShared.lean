/-
  Shared declaration home for the SDIV semantic and stack specifications.
-/

import EvmAsm.Evm64.SDiv.Compose.SDivViewChainA
import EvmAsm.Evm64.SDiv.DivCallExactShared
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Evm64.SDiv.Compose

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

open EvmAsm.Evm64.SDiv.Compose

/-- Postcondition bundle for the exact (non-zero divisor) SDIV handler path.
    Bundles the result-sign/mask/carry chain, leaving the EVM stack as a parameter. -/
@[irreducible]
def sdivExactHandlerPost (sp vRa base : Word) (dividend divisor : EvmWord)
    (stackResult : List EvmWord) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
  let resultSign :=
    (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
      (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
  let mask := (0 : Word) - resultSign
  let divisorAbsWord :=
    sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
  let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
  let sum0 := ((quotientWord.getLimbN 0) ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := ((quotientWord.getLimbN 1) ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := ((quotientWord.getLimbN 2) ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := ((quotientWord.getLimbN 3) ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  let divisorSign := divisor.getLimbN 3 >>> (63 : BitVec 6).toNat
  fun h =>
    (((.x18 ↦ᵣ vRa) **
     (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       evmStackIs (sp + 32) stackResult) **
      saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) h) ∨
    (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
     (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       evmStackIs (sp + 32) stackResult) **
      saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) h)

theorem sdivExactHandlerPost_unfold {sp vRa base : Word} {dividend divisor : EvmWord}
    {stackResult : List EvmWord} :
    sdivExactHandlerPost sp vRa base dividend divisor stackResult =
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let mask := (0 : Word) - resultSign
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let sum0 := ((quotientWord.getLimbN 0) ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := ((quotientWord.getLimbN 1) ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := ((quotientWord.getLimbN 2) ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := ((quotientWord.getLimbN 3) ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       let divisorSign := divisor.getLimbN 3 >>> (63 : BitVec 6).toNat
       fun h =>
        (((.x18 ↦ᵣ vRa) **
         (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
           (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
           evmStackIs (sp + 32) stackResult) **
          saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) h) ∨
        (((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
         (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
           (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
           evmStackIs (sp + 32) stackResult) **
          saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) h)) := by
  delta sdivExactHandlerPost; rfl

/-- Postcondition bundle for zero-divisor SDIV handler path.
    Bundles the result-sign/mask/carry computation and the saved-RA frame,
    leaving the EVM stack result as a parameter. -/
@[irreducible]
def sdivZeroDivisorPost (sp vRa base : Word) (dividend : EvmWord)
    (stackResult : List EvmWord) : EvmAsm.Rv64.Assertion :=
  let dividendAbsWord :=
    sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
  let divisorSign := (0 : Word) >>> (63 : BitVec 6).toNat
  let resultSign :=
    (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^ divisorSign
  let mask := (0 : Word) - resultSign
  let sum0 := ((0 : Word) ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := ((0 : Word) ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := ((0 : Word) ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := ((0 : Word) ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x18 ↦ᵣ vRa) **
  (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
    (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ carry3) **
    evmStackIs (sp + 32) stackResult) **
   saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)

theorem sdivZeroDivisorPost_unfold {sp vRa base : Word} {dividend : EvmWord}
    {stackResult : List EvmWord} :
    sdivZeroDivisorPost sp vRa base dividend stackResult =
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorSign := (0 : Word) >>> (63 : BitVec 6).toNat
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^ divisorSign
       let mask := (0 : Word) - resultSign
       let sum0 := ((0 : Word) ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := ((0 : Word) ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := ((0 : Word) ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := ((0 : Word) ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ vRa) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) stackResult) **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord)) := by
  delta sdivZeroDivisorPost; rfl

/-- v4 top-level zero-divisor SDIV stack bridge with the concrete semantic
    zero-result stack shape. -/
theorem evm_sdiv_zero_divisor_result_stack_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: (0 : EvmWord) :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (sdivZeroDivisorPost sp vRa base dividend ((0 : EvmWord) :: rest)) := by
  rw [sdivZeroDivisorPost_unfold]
  exact saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_divisor_spec_in_sdivCodeV4
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 dividend rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase

/-- v4 top-level zero-divisor SDIV handler-stack bridge.

    This is the caller-visible zero-divisor path through the full
    `sdivCodeV4`, exposing the post stack using the executable `sdivHandler`
    view. -/
theorem evm_sdiv_zero_divisor_handler_stack_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: (0 : EvmWord) :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (sdivZeroDivisorPost sp vRa base dividend
        (ArithmeticHandlers.sdivHandler
          { state with stack := dividend :: (0 : EvmWord) :: rest }).stack) := by
  rw [sdivZeroDivisorPost_unfold]
  exact saveRa_signs_abs_signXor_then_divCall_bzero_stack_entry_zero_divisor_handler_stack_spec_in_sdivCodeV4
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 state dividend rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase

/-- v4 zero-divisor SDIV handler-stack bridge with the zero divisor supplied
    as a variable plus an equality proof. -/
theorem evm_sdiv_zero_divisor_handler_stack_of_eq_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hDivisorZero : divisor = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (sdivZeroDivisorPost sp vRa base dividend
        (ArithmeticHandlers.sdivHandler
          { state with stack := dividend :: divisor :: rest }).stack) := by
  subst divisor
  exact evm_sdiv_zero_divisor_handler_stack_v4_spec_within
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 state dividend rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase

/-- v4 zero-divisor SDIV handler-stack bridge viewed through the exact-path
    quotient/sign-fix postcondition. -/
theorem evm_sdiv_zero_divisor_handler_stack_exact_post_of_eq_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hDivisorZero : divisor = 0) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (sdivExactHandlerPost sp vRa base dividend divisor
        (ArithmeticHandlers.sdivHandler
          { state with stack := dividend :: divisor :: rest }).stack) := by
  subst divisor
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [sdivExactHandlerPost_unfold]
      rw [sdivZeroDivisorPost_unfold] at hp
      simp only [EvmWord.getLimbN_zero] at hp ⊢
      have hDivisorAbs :
          sdivAbsDivisorWord (0 : Word) (0 : Word) (0 : Word) (0 : Word) = 0 := by
        exact sdivAbsDivisorWord_zero
      rw [hDivisorAbs, EvmWord.div_zero_right]
      simp only [EvmWord.getLimbN_zero] at hp ⊢
      have hSum3 := sdivResultSign_fixZeroWordLimb3 (dividend.getLimbN 3) (0 : Word)
      simp only [EvmWord.getLimbN_zero] at hSum3
      rw [hSum3] at hp ⊢
      exact Or.inl (by simpa using hp))
    (evm_sdiv_zero_divisor_handler_stack_v4_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 state dividend rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase)

/-- v4 top-level exact-callable SDIV stack-tail bridge.

    This is the caller-visible exact path through `sdivCodeV4`, parameterized
    by the unsigned DIV no-NOP v4 proof that discharges the branch-specific
    callable obligation. -/
theorem evm_sdiv_exact_return_stack_tail_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnPostNoX9 vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
       evmStackIs (sp + 64) rest) :=
  saveRa_signs_abs_signXor_then_divCall_exact_then_return_stack_tail_from_handoff_spec_in_sdivCodeV4
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 dividend divisor rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack

/-- v4 top-level exact-callable SDIV stack bridge with the produced result slot
    exposed as the named sign-fixed quotient word. -/
theorem evm_sdiv_exact_callable_return_sign_fixed_word_stack_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaDivCallCallableReturnSignFixedWordPostNoX9 vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3) **
       evmStackIs (sp + 64) rest) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [saveRaDivCallCallableReturnPostNoX9_evmWordIs] at hp
      exact hp)
    (evm_sdiv_exact_return_stack_tail_v4_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- v4 top-level exact-callable SDIV result-stack bridge.

    This folds the exact v4 return path's result-sign-fix memory output into
    `evmStackIs (sp + 32)`. -/
theorem evm_sdiv_exact_return_result_stack_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (let dividendAbsWord :=
         sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
           (dividend.getLimbN 2) (dividend.getLimbN 3)
       let divisorAbsWord :=
         sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
           (divisor.getLimbN 2) (divisor.getLimbN 3)
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultWord :=
         sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
           (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
           (quotientWord.getLimbN 2) (quotientWord.getLimbN 3)
       let resultSign :=
         (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
           (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat)
       let mask := (0 : Word) - resultSign
       let sum0 := ((quotientWord.getLimbN 0) ^^^ mask) + resultSign
       let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
       let sum1 := ((quotientWord.getLimbN 1) ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := ((quotientWord.getLimbN 2) ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := ((quotientWord.getLimbN 3) ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (sp + 32)) ** (.x8 ↦ᵣ resultSign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         evmStackIs (sp + 32) (resultWord :: rest)) **
        saveRaDivCallSavedRaRetFrameNoX9 sp base dividendAbsWord)) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun h hp => by
      rw [saveRaDivCallCallableReturnPostNoX9_unfold] at hp
      dsimp only at hp ⊢
      rw [resultSignFixPost_sdivResultSign_word
        (sp + 32) (dividend.getLimbN 3) (divisor.getLimbN 3)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 0)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 1)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 2)
        ((EvmWord.div
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))).getLimbN 3)] at hp
      rw [evmStackIs_cons]
      rw [show (sp + 32 + 32 : Word) = sp + 64 by bv_omega]
      xperm_hyp hp)
    (evm_sdiv_exact_return_stack_tail_v4_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- v4 exact-callable SDIV handler-stack bridge, parameterized by the remaining
    pure result-word equality. -/
theorem evm_sdiv_exact_return_handler_stack_of_result_eq_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4))))
    (hResult :
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
        EvmWord.sdiv dividend divisor) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (sdivExactHandlerPost sp vRa base dividend divisor
        (ArithmeticHandlers.sdivHandler
          { state with stack := dividend :: divisor :: rest }).stack) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [hResult] at hp
      rw [sdivExactHandlerPost_unfold]
      exact Or.inr (by simpa using hp))
    (evm_sdiv_exact_return_result_stack_v4_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack)

/-- v4 exact-callable SDIV handler-stack bridge with the pure result-word
    equality discharged for all operand signs. -/
theorem evm_sdiv_exact_return_handler_stack_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (sdivExactHandlerPost sp vRa base dividend divisor
        (ArithmeticHandlers.sdivHandler
          { state with stack := dividend :: divisor :: rest }).stack) :=
  evm_sdiv_exact_return_handler_stack_of_result_eq_v4_spec_within
    vRa vSavedOld sp sDividendOld sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld
    v2 v5 v6 state dividend divisor rest
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack
    (sdivResultSignFixedWord_eq_sdiv dividend divisor)

/-- v4 all-case SDIV handler-stack bridge.

    The proof splits on `divisor = 0`: the zero-divisor branch uses the v4
    bzero path viewed through the exact-path postcondition, while the nonzero
    branch uses the v4 exact-return handler-stack bridge. -/
theorem evm_sdiv_handler_stack_v4_spec_within
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 : Word)
    (state : EvmState) (dividend divisor : EvmWord) (rest : List EvmWord)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (hbase : base &&& 1 = 0)
    (hStack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff)
        ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsSign (divisor.getLimbN 3)) ((base + divCallOff) + 4) v2 v5 v6
          (sdivAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (sdivAbsMask (divisor.getLimbN 3))
          (sdivAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.divStackDispatchPostCallable sp
          (sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + divCallOff) + 4)))) :
    EvmAsm.Rv64.cpsTripleWithin (((49 + (EvmAsm.Evm64.unifiedDivBound + 1)) + 21) + 1)
      base (vRa &&& ~~~(1 : Word)) (sdivCodeV4 base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld) ** (.x12 ↦ᵣ sp) **
         (.x8 ↦ᵣ sDividendOld) ** (.x9 ↦ᵣ sDivisorOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
         (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
        evmStackIs sp (dividend :: divisor :: rest)) **
       ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
        EvmAsm.Evm64.divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (sdivExactHandlerPost sp vRa base dividend divisor
        (ArithmeticHandlers.sdivHandler
          { state with stack := dividend :: divisor :: rest }).stack) := by
  by_cases hDivisorZero : divisor = 0
  · exact evm_sdiv_zero_divisor_handler_stack_exact_post_of_eq_v4_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 state dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hDivisorZero
  · exact evm_sdiv_exact_return_handler_stack_v4_spec_within
      vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      v2 v5 v6 state dividend divisor rest
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base hbase hStack

/-- Public v4 all-case SDIV stack spec, conditional on the unsigned DIV v4
    no-NOP stack proof used by the internal callable handoff. -/
abbrev evm_sdiv_stack_v4_spec_within :=
  evm_sdiv_handler_stack_v4_spec_within

end EvmAsm.Evm64
