/-
  EvmAsm.Evm64.DivMod.Spec.N3V5Shift0Quotient

  **v5 n=3 accumulated quotient correctness for the shift=0 path.**
  When the divisor's top limb `b2` is already normalized (`b2 ≥ 2^63`, i.e.
  `clz b2 = 0`), the algorithm skips normalization and runs the schoolbook
  directly on the RAW divisor `(b0,b1,b2,0)` and the raw dividend limbs.  The two
  v5 n=3 digits (r1, r0) then combine to exactly `val256 a / val256 b`.

  Shift=0 counterpart of `fullDivN3_acc_quot_eq_div_of_shape` (N3V5AccQuot,
  shift≠0).  Cleaner: with `s = 0` there is no normalization scaling, so the
  per-digit steps (`iterN3V5_step`, over the raw 3-limb divisor) telescope
  directly into the unnormalized Euclidean equation, and `Nat.div_mod_unique`
  recovers the quotient.  n=3 / 2-digit analog of `n2_shift0_acc_quot`
  (N2V5Shift0Quotient).  Bead `evm-asm-wbc4i.9.3.3.8`.
-/

import EvmAsm.Evm64.DivMod.Spec.N3V5RemainderShared

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=3 accumulated quotient correctness (shift=0).** The two v5 n=3 digits
    over the raw 3-limb divisor combine to `val256 a / val256 b`. -/
theorem n3_shift0_acc_quot
    (a0 a1 a2 a3 b0 b1 b2 : Word) (hb2 : b2.toNat ≥ 2^63) (bltu_1 bltu_0 : Bool)
    (hc1 : bltu_1 = true → BitVec.ult (0:Word) b2 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (0:Word) b2)
    (hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).1.toNat * 2^64
      + (iterN3V5 bltu_0 b0 b1 b2 0 a0
          (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
          (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
          (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).1.toNat
      = val256 a0 a1 a2 a3 / val256 b0 b1 b2 0 := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hvpos : 2^191 ≤ val256 b0 b1 b2 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a1 a2 a3 0 < 2^64 * val256 b0 b1 b2 0 := by
    have ha : val256 a1 a2 a3 0 < 2^192 := by
      have := a1.isLt; have := a2.isLt; have := a3.isLt
      simp only [EvmWord.val256, h0]; omega
    calc val256 a1 a2 a3 0 < 2^192 := ha
      _ ≤ 2^64 * 2^191 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 b2 0 := Nat.mul_le_mul_left _ hvpos
  have hR1 := iterN3V5_step bltu_1 b0 b1 b2 a1 a2 a3 0 hb2 hfwv hc1 hm1
  have hR0valid := n3_next_window_lt a0
    (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
    (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
    (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 _ hR1.2
  have hR0 := iterN3V5_step bltu_0 b0 b1 b2 a0
    (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
    (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
    (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 hb2 hR0valid hc0 hm0
  have hfirst : val256 a0 a1 a2 a3 = a0.toNat + 2^64 * val256 a1 a2 a3 0 := by
    simp only [EvmWord.val256, h0]; ring
  have hWin0 : val256 a0
      (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
      (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
      (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1
      = a0.toNat + 2^64 * ((iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1.toNat
          + 2^64 * (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1.toNat
          + 2^128 * (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1.toNat) := by
    simp only [EvmWord.val256]; ring
  rw [hWin0] at hR0
  have htele := fullDivN3V5_two_step_nat hfirst hR1.1 hR0.1
  have hbpos : 0 < val256 b0 b1 b2 0 := by omega
  symm
  exact ((Nat.div_mod_unique hbpos).mpr ⟨by rw [htele]; ring, hR0.2⟩).1

/-- **v5 n=3 quotient word = div a b (shift=0).** The shift=0 quotient digits,
    packed into a word `fromLimbs(R0.1, R1.1, 0, 0)`, equal `EvmWord.div a b`. -/
theorem n3_shift0_quotient_word_eq_div
    (a0 a1 a2 a3 b0 b1 b2 : Word) (hb2 : b2.toNat ≥ 2^63) (bltu_1 bltu_0 : Bool)
    (hc1 : bltu_1 = true → BitVec.ult (0:Word) b2 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (0:Word) b2)
    (hc0 : bltu_0 = true →
      BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 b2) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).1
        | 1 => (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).1
        | 2 => 0
        | 3 => 0)
      = EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => 0) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| (0:Word) ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have hz : b2 = 0 := (BitVec.or_eq_zero_iff.mp h2).2
    rw [hz] at hb2; simp at hb2
  have hacc := n3_shift0_acc_quot a0 a1 a2 a3 b0 b1 b2 hb2 bltu_1 bltu_0 hc1 hm1 hc0 hm0
  have hqval : val256
      (iterN3V5 bltu_0 b0 b1 b2 0 a0
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).1
      (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).1 0 0
      = val256 a0 a1 a2 a3 / val256 b0 b1 b2 0 := by
    rw [← hacc]; simp only [EvmWord.val256, h0]; ring
  exact div_of_val256_eq_div hbnz hqval

end EvmAsm.Evm64
