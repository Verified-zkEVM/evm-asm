/-
  EvmAsm.Evm64.DivMod.Spec.N3V5QuotientShape

  **v5 n=3 quotient correctness from shape (shift≠0):**
  `fullDivN3QuotientWordV5 = EvmWord.div a b`.

  Combines the accumulated-quotient telescope `fullDivN3_acc_quot_eq_div_of_shape`
  (N3V5AccQuot) with the `EvmWord` lift `div_of_val256_eq_div`: the assembled
  quotient word's `val256` equals `val256 a / val256 b`, hence the word equals
  `EvmWord.div a b`.  Then `fullDivN3V5_hdivs_of_word_eq` (N3V5QuotientWord)
  projects out the four per-limb `(div a b).getLimbN` digit equalities the n=3
  lane wrapper feeds to `divStackDispatchPost`.

  n=3 analog of `fullDivN2QuotientWordV5_eq_div_of_shape` (N2V5QuotientShape).
  Bead `evm-asm-wbc4i.9.3.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.N3V5RemainderShared
import EvmAsm.Evm64.DivMod.Spec.N3V5QuotientWord

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=3 quotient correctness (shift≠0), from shape + `bltu` path matches.**
    The assembled v5 n=3 quotient word equals `EvmWord.div a b`. -/
theorem fullDivN3QuotientWordV5_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    fullDivN3QuotientWordV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  have hacc := fullDivN3_acc_quot_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_1 bltu_0 hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  have hqval : val256 (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 0 0
      = val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
    rw [← hacc]; simp only [EvmWord.val256, h0]; ring
  have hdiv := div_of_val256_eq_div hbnz hqval
  unfold fullDivN3QuotientWordV5
  exact hdiv

/-- **Lane-ready form: the four `(div a b).getLimbN` digit equalities from shape**
    (shift≠0) + the `bltu` path matches.  Composes
    `fullDivN3QuotientWordV5_eq_div_of_shape` with the `getLimbN` projector
    `fullDivN3V5_hdivs_of_word_eq`. -/
theorem div_getLimbN_eq_digit_n3_v5_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 1
      = (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 2
      = (0 : Word) ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 3
      = (0 : Word) := by
  have hword := fullDivN3QuotientWordV5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_1 bltu_0 hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  exact fullDivN3V5_hdivs_of_word_eq bltu_1 bltu_0 _ _ a0 a1 a2 a3 b0 b1 b2 b3 hword

end EvmAsm.Evm64
