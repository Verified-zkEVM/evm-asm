/-
  EvmAsm.Evm64.DivMod.Spec.N3V5Shift0ModRemainder

  **v5 n=3 MOD remainder correctness for the shift=0 path.**
  When the divisor's top limb `b2` is already normalized (`b2 ≥ 2^63`), the
  schoolbook runs on the RAW 3-limb divisor `(b0,b1,b2,0)` with no denormalization,
  so the final R0 remainder window (3 limbs, top limb collapsed to 0) equals
  `EvmWord.mod a b` directly.

  MOD counterpart of `n3_shift0_quotient_word_eq_div` (N3V5Shift0Quotient): same
  `iterN3V5_step` telescope (reused via the two-step accumulation), but extracts
  the remainder (`Nat.mul_add_mod` + the window bound) instead of the quotient, and
  closes with `mod_of_val256_eq_mod`.  n=3 analog of `n2_shift0_remainder_eq_mod`.
-/

import EvmAsm.Evm64.DivMod.Spec.N3V5Shift0Quotient

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=3 remainder word = mod a b (shift=0).** The shift=0 final R0 remainder
    window, packed into `fromLimbs(R0.2.1, R0.2.2.1, R0.2.2.2.1, R0.2.2.2.2.1)`,
    equals `EvmWord.mod a b`. -/
theorem n3_shift0_remainder_word_eq_mod
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
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.1
        | 1 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.1
        | 2 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.2.1
        | 3 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.2.2.1)
      = EvmWord.mod
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => 0) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| (0:Word) ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have hz : b2 = 0 := (BitVec.or_eq_zero_iff.mp h2).2
    rw [hz] at hb2; simp at hb2
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
  have hR0c := iterN3V5_collapse bltu_0 b0 b1 b2 a0
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
  have hmodeq : val256 a0 a1 a2 a3 % val256 b0 b1 b2 0
      = (iterN3V5 bltu_0 b0 b1 b2 0 a0
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.1.toNat
        + 2^64 * (iterN3V5 bltu_0 b0 b1 b2 0 a0
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.1.toNat
        + 2^128 * (iterN3V5 bltu_0 b0 b1 b2 0 a0
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
            (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.2.1.toNat := by
    rw [htele, Nat.mul_comm _ (val256 b0 b1 b2 0), Nat.mul_add_mod, Nat.mod_eq_of_lt hR0.2]
  have hr : val256
      (iterN3V5 bltu_0 b0 b1 b2 0 a0
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.1
      (iterN3V5 bltu_0 b0 b1 b2 0 a0
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.1
      (iterN3V5 bltu_0 b0 b1 b2 0 a0
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.2.1
      (iterN3V5 bltu_0 b0 b1 b2 0 a0
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
        (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.2.2.1
      = val256 a0 a1 a2 a3 % val256 b0 b1 b2 0 := by
    rw [hR0c.1, hmodeq]; simp only [EvmWord.val256, h0]; ring_nf
  exact mod_of_val256_eq_mod hbnz hr

/-- Lane (`a b : EvmWord`) form of the shift=0 n=3 MOD remainder-word correctness. -/
theorem n3_shift0_remainder_word_eq_mod_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 : Word) (bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3z : b.getLimbN 3 = 0)
    (hb2ge : b2.toNat ≥ 2^63)
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
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.1
        | 1 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.1
        | 2 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.2.1
        | 3 => (iterN3V5 bltu_0 b0 b1 b2 0 a0
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.1
                  (iterN3V5 bltu_1 b0 b1 b2 0 a1 a2 a3 0 0).2.2.2.1 0).2.2.2.2.1)
      = EvmWord.mod a b := by
  have hbase := n3_shift0_remainder_word_eq_mod a0 a1 a2 a3 b0 b1 b2 hb2ge bltu_1 bltu_0
    hc1 hm1 hc0 hm0
  refine hbase.trans ?_
  congr 1
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id a]
    congr 1
    funext i
    fin_cases i <;> simp only [ha0, ha1, ha2, ha3]
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id b]
    congr 1
    funext i
    fin_cases i <;> simp only [hb0, hb1, hb2, hb3z]

end EvmAsm.Evm64
