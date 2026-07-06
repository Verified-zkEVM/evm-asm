/-
  EvmAsm.Evm64.SMod.SpecSemantic

  Pure semantic result bridge for the top-level SMOD stack spec.
-/

import EvmAsm.Evm64.SMod.Compose.Words
import EvmAsm.Evm64.EvmWordArith.Div
import EvmAsm.Evm64.EvmWordArith.SMod

namespace EvmAsm.Evm64

open EvmAsm.Evm64.SMod.Compose

private lemma limbN3_eq_extractLsb (v : EvmWord) :
    v.getLimbN 3 = v.extractLsb' 192 64 := by
  simp [EvmWord.getLimbN, EvmWord.getLimb]

private lemma getLsbD_255_eq_extractLsb_192_63 (v : EvmWord) :
    v.getLsbD 255 = (v.extractLsb' 192 64).getLsbD 63 := by
  rw [BitVec.getLsbD_extractLsb', show (192 + 63 : Nat) = 255 from by omega]
  simp

private lemma getLsbD_63_eq_ushiftRight_63_bit0 (x : Word) :
    x.getLsbD 63 = (x >>> 63).getLsbD 0 := by
  simp [show (0 + 63 : Nat) < 64 from by omega]

private lemma msb_false_of_limbN3_shift63_zero (v : EvmWord)
    (hSign : v.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    BitVec.msb v = false := by
  simp only [show (63 : BitVec 6).toNat = 63 from rfl] at hSign
  rw [limbN3_eq_extractLsb] at hSign
  simp only [BitVec.msb, BitVec.getMsbD, show (256 : Nat) - 1 - 0 = 255 from rfl]
  rw [getLsbD_255_eq_extractLsb_192_63, getLsbD_63_eq_ushiftRight_63_bit0, hSign]
  rfl

private lemma msb_true_of_limbN3_shift63_one (v : EvmWord)
    (hSign : v.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    BitVec.msb v = true := by
  simp only [show (63 : BitVec 6).toNat = 63 from rfl] at hSign
  rw [limbN3_eq_extractLsb] at hSign
  simp only [BitVec.msb, BitVec.getMsbD, show (256 : Nat) - 1 - 0 = 255 from rfl]
  rw [getLsbD_255_eq_extractLsb_192_63, getLsbD_63_eq_ushiftRight_63_bit0, hSign]
  rfl

private lemma limbN3_shift63_cases (v : EvmWord) :
    v.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word) ∨
      v.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word) := by
  simp only [show (63 : BitVec 6).toNat = 63 from rfl]
  have h_lt : (v.getLimbN 3 >>> 63).toNat < 2 := by
    have hx := (v.getLimbN 3).isLt
    simp only [BitVec.toNat_ushiftRight]
    omega
  rcases (show (v.getLimbN 3 >>> 63).toNat = 0 ∨
      (v.getLimbN 3 >>> 63).toNat = 1 from by omega) with h0 | h1
  · left
    exact BitVec.eq_of_toNat_eq (by simpa using h0)
  · right
    exact BitVec.eq_of_toNat_eq (by simpa using h1)

theorem smodResultSignFixedWord_eq_smod_of_nonnegative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    let dividendAbsWord :=
      smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let modulusWord := EvmWord.mod dividendAbsWord divisorAbsWord
    smodResultSignFixedWord (dividend.getLimbN 3)
      (modulusWord.getLimbN 0) (modulusWord.getLimbN 1)
      (modulusWord.getLimbN 2) (modulusWord.getLimbN 3) =
      EvmWord.smod dividend divisor := by
  dsimp
  rw [smodAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [smodAbsDivisorWord_eq_word_of_sign_zero divisor hDivisorSign]
  rw [smodResultSignFixedWord_eq_word_of_result_sign_zero _ _ hDividendSign]
  have hDividendMsb : BitVec.msb dividend = false :=
    msb_false_of_limbN3_shift63_zero dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = false :=
    msb_false_of_limbN3_shift63_zero divisor hDivisorSign
  unfold EvmWord.mod EvmWord.smod
  simp [BitVec.srem_eq, hDividendMsb, hDivisorMsb]

theorem smodResultSignFixedWord_eq_smod_of_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let modulusWord := EvmWord.mod dividendAbsWord divisorAbsWord
    smodResultSignFixedWord (dividend.getLimbN 3)
      (modulusWord.getLimbN 0) (modulusWord.getLimbN 1)
      (modulusWord.getLimbN 2) (modulusWord.getLimbN 3) =
      EvmWord.smod dividend divisor := by
  dsimp
  rw [smodAbsDividendWord_eq_neg_word_of_sign_one dividend hDividendSign]
  rw [smodAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  rw [smodResultSignFixedWord_eq_neg_word_of_result_sign_one _ _ hDividendSign]
  have hDividendMsb : BitVec.msb dividend = true :=
    msb_true_of_limbN3_shift63_one dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = true :=
    msb_true_of_limbN3_shift63_one divisor hDivisorSign
  unfold EvmWord.mod EvmWord.smod
  by_cases h_zero : divisor = 0
  · simp [h_zero]
  · have h_neg_ne : -divisor ≠ 0 := by
      intro h_neg_zero
      apply h_zero
      bv_omega
    simp [BitVec.srem_eq, hDividendMsb, hDivisorMsb]

theorem smodResultSignFixedWord_eq_smod_of_nonnegative_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let modulusWord := EvmWord.mod dividendAbsWord divisorAbsWord
    smodResultSignFixedWord (dividend.getLimbN 3)
      (modulusWord.getLimbN 0) (modulusWord.getLimbN 1)
      (modulusWord.getLimbN 2) (modulusWord.getLimbN 3) =
      EvmWord.smod dividend divisor := by
  dsimp
  rw [smodAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [smodAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  rw [smodResultSignFixedWord_eq_word_of_result_sign_zero _ _ hDividendSign]
  have hDividendMsb : BitVec.msb dividend = false :=
    msb_false_of_limbN3_shift63_zero dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = true :=
    msb_true_of_limbN3_shift63_one divisor hDivisorSign
  unfold EvmWord.mod EvmWord.smod
  by_cases h_zero : divisor = 0
  · simp [h_zero]
  · have h_neg_ne : -divisor ≠ 0 := by
      intro h_neg_zero
      apply h_zero
      bv_omega
    simp [BitVec.srem_eq, hDividendMsb, hDivisorMsb]

theorem smodResultSignFixedWord_eq_smod_of_negative_nonnegative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    let dividendAbsWord :=
      smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let modulusWord := EvmWord.mod dividendAbsWord divisorAbsWord
    smodResultSignFixedWord (dividend.getLimbN 3)
      (modulusWord.getLimbN 0) (modulusWord.getLimbN 1)
      (modulusWord.getLimbN 2) (modulusWord.getLimbN 3) =
      EvmWord.smod dividend divisor := by
  dsimp
  rw [smodAbsDividendWord_eq_neg_word_of_sign_one dividend hDividendSign]
  rw [smodAbsDivisorWord_eq_word_of_sign_zero divisor hDivisorSign]
  rw [smodResultSignFixedWord_eq_neg_word_of_result_sign_one _ _ hDividendSign]
  have hDividendMsb : BitVec.msb dividend = true :=
    msb_true_of_limbN3_shift63_one dividend hDividendSign
  have hDivisorMsb : BitVec.msb divisor = false :=
    msb_false_of_limbN3_shift63_zero divisor hDivisorSign
  unfold EvmWord.mod EvmWord.smod
  by_cases h_zero : divisor = 0
  · simp [h_zero]
  · rw [if_neg h_zero, if_neg h_zero]
    simp [BitVec.srem_eq, hDividendMsb, hDivisorMsb]

theorem smodResultSignFixedWord_eq_smod
    (dividend divisor : EvmWord) :
    let dividendAbsWord :=
      smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let modulusWord := EvmWord.mod dividendAbsWord divisorAbsWord
    smodResultSignFixedWord (dividend.getLimbN 3)
      (modulusWord.getLimbN 0) (modulusWord.getLimbN 1)
      (modulusWord.getLimbN 2) (modulusWord.getLimbN 3) =
      EvmWord.smod dividend divisor := by
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
    · exact smodResultSignFixedWord_eq_smod_of_nonnegative
        dividend divisor hDividendSign hDivisorSign
    · exact smodResultSignFixedWord_eq_smod_of_nonnegative_negative
        dividend divisor hDividendSign hDivisorSign
  · rcases hDivisorSign with hDivisorSign | hDivisorSign
    · exact smodResultSignFixedWord_eq_smod_of_negative_nonnegative
        dividend divisor hDividendSign hDivisorSign
    · exact smodResultSignFixedWord_eq_smod_of_negative
        dividend divisor hDividendSign hDivisorSign

end EvmAsm.Evm64
