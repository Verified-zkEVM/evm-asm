/- Shared declaration home for the n=2 shift=0 quotient and remainder limbs. -/

import EvmAsm.Evm64.DivMod.Spec.N2V5NormScaled
import EvmAsm.Evm64.DivMod.Spec.N2QuotientWord
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientWord
import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=2 accumulated quotient correctness (shift=0).** The three v5 n=2
    digits over the raw 2-limb divisor combine to `val256 a / val256 b`. -/
theorem n2_shift0_acc_quot
    (a0 a1 a2 a3 b0 b1 : Word) (hb1 : b1.toNat ≥ 2^63) (bltu_2 bltu_1 bltu_0 : Bool)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).1.toNat * 2^128
      + (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).1.toNat * 2^64
      + (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).1.toNat
      = val256 a0 a1 a2 a3 / val256 b0 b1 0 0 := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| 0 ||| 0 ≠ 0 := by
    intro h; have h2 := (BitVec.or_eq_zero_iff.mp h).1; have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2; rw [hz] at hb1; simp at hb1
  have hvpos : 2^127 ≤ val256 b0 b1 0 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a2 a3 0 0 < 2^64 * val256 b0 b1 0 0 := by
    have ha : val256 a2 a3 0 0 < 2^128 := by
      have := a2.isLt; have := a3.isLt; simp only [EvmWord.val256, h0]; omega
    calc val256 a2 a3 0 0 < 2^128 := ha
      _ ≤ 2^64 * 2^127 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 0 0 := Nat.mul_le_mul_left _ hvpos
  have hR2 := iterN2V5_step bltu_2 b0 b1 a2 a3 0 hbnz hb1 hfwv hc2 hm2
  have hR1valid := n2_next_window_lt a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 _ hR2.2
  have hR1 := iterN2V5_step bltu_1 b0 b1 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 hbnz hb1 hR1valid hc1 hm1
  have hR0valid := n2_next_window_lt a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 _ hR1.2
  have hR0 := iterN2V5_step bltu_0 b0 b1 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 hbnz hb1 hR0valid hc0 hm0
  have hfirst : val256 a0 a1 a2 a3 = a0.toNat + 2^64*a1.toNat + 2^128*(a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat)) := by
    simp only [EvmWord.val256]; ring
  have hW2 : val256 a2 a3 0 0 = a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin1 : val256 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0
      = a1.toNat + 2^64*((iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin0 : val256 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0
      = a0.toNat + 2^64*((iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  rw [hW2] at hR2; rw [hWin1] at hR1; rw [hWin0] at hR0
  have htele := fullDivN2V5_three_step_nat hfirst hR2.1 hR1.1 hR0.1
  have hbpos : 0 < val256 b0 b1 0 0 := by omega
  symm
  exact ((Nat.div_mod_unique hbpos).mpr ⟨by rw [htele]; ring, hR0.2⟩).1

/-- **v5 n=2 MOD remainder correctness (shift=0).** At shift=0 the remainder is
    used directly (no denormalization), so the final R0 remainder limbs equal
    `EvmWord.mod a b`.  Cleaner than the shift≠0 case (#7367): `s = 0`, so the
    denorm is the identity and `mod_of_val256_eq_mod` applies after collapsing the
    remainder to its low two limbs. -/
theorem n2_shift0_remainder_eq_mod
    (a0 a1 a2 a3 b0 b1 : Word) (hb1 : b1.toNat ≥ 2^63) (bltu_2 bltu_1 bltu_0 : Bool)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1
        | 1 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1
        | 2 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.1
        | 3 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.2.1)
      = EvmWord.mod
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => 0 | 3 => 0) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| (0:Word) ||| 0 ≠ 0 := by
    intro h; have h2 := (BitVec.or_eq_zero_iff.mp h).1; have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2; rw [hz] at hb1; simp at hb1
  have hvpos : 2^127 ≤ val256 b0 b1 0 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a2 a3 0 0 < 2^64 * val256 b0 b1 0 0 := by
    have ha : val256 a2 a3 0 0 < 2^128 := by
      have := a2.isLt; have := a3.isLt; simp only [EvmWord.val256, h0]; omega
    calc val256 a2 a3 0 0 < 2^128 := ha
      _ ≤ 2^64 * 2^127 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 0 0 := Nat.mul_le_mul_left _ hvpos
  have hR2 := iterN2V5_step bltu_2 b0 b1 a2 a3 0 hbnz hb1 hfwv hc2 hm2
  have hR1valid := n2_next_window_lt a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 _ hR2.2
  have hR1 := iterN2V5_step bltu_1 b0 b1 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 hbnz hb1 hR1valid hc1 hm1
  have hR0valid := n2_next_window_lt a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 _ hR1.2
  have hR0 := iterN2V5_step bltu_0 b0 b1 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 hbnz hb1 hR0valid hc0 hm0
  have hR0c := iterN2V5_collapse bltu_0 b0 b1 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 hbnz hb1 hR0valid hc0 hm0
  have hfirst : val256 a0 a1 a2 a3 = a0.toNat + 2^64*a1.toNat + 2^128*(a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat)) := by
    simp only [EvmWord.val256]; ring
  have hW2 : val256 a2 a3 0 0 = a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin1 : val256 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0
      = a1.toNat + 2^64*((iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin0 : val256 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0
      = a0.toNat + 2^64*((iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  rw [hW2] at hR2; rw [hWin1] at hR1; rw [hWin0] at hR0
  have htele := fullDivN2V5_three_step_nat hfirst hR2.1 hR1.1 hR0.1
  have hbpos : 0 < val256 b0 b1 0 0 := by omega
  have hmodeq : val256 a0 a1 a2 a3 % val256 b0 b1 0 0
      = (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1.toNat
        + 2^64*(iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1.toNat := by
    rw [htele, Nat.mul_comm _ (val256 b0 b1 0 0), Nat.mul_add_mod, Nat.mod_eq_of_lt hR0.2]
  have hr : val256
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.1
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.2.1
      = val256 a0 a1 a2 a3 % val256 b0 b1 0 0 := by
    rw [hR0c.1, hR0c.2.1, hmodeq]; simp only [EvmWord.val256, h0]; ring_nf
  exact mod_of_val256_eq_mod hbnz hr

/-- **v5 n=2 quotient word = div a b (shift=0).** The shift=0 quotient digits,
    packed into a word `fromLimbs(R0.1, R1.1, R2.1, 0)`, equal `EvmWord.div a b`.
    From the accumulated-quotient correctness + the EvmWord lift. -/
theorem n2_shift0_quotient_word_eq_div
    (a0 a1 a2 a3 b0 b1 : Word) (hb1 : b1.toNat ≥ 2^63) (bltu_2 bltu_1 bltu_0 : Bool)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).1
        | 1 => (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).1
        | 2 => (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).1
        | 3 => 0)
      = EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => 0 | 3 => 0) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| (0:Word) ||| 0 ≠ 0 := by
    intro h; have h2 := (BitVec.or_eq_zero_iff.mp h).1; have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2; rw [hz] at hb1; simp at hb1
  have hacc := n2_shift0_acc_quot a0 a1 a2 a3 b0 b1 hb1 bltu_2 bltu_1 bltu_0 hc2 hm2 hc1 hm1 hc0 hm0
  have hqval : val256
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).1
      (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).1
      (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).1 0
      = val256 a0 a1 a2 a3 / val256 b0 b1 0 0 := by
    rw [← hacc]; simp only [EvmWord.val256, h0]; ring
  exact div_of_val256_eq_div hbnz hqval


open EvmWord EvmAsm.Rv64

/-- Lane form of the shift=0 n=2 remainder word: equals `EvmWord.mod a b`. -/
theorem n2_shift0_remainder_word_eq_mod_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2z : b.getLimbN 2 = 0) (hb3z : b.getLimbN 3 = 0)
    (hb1ge : b1.toNat ≥ 2^63)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1
        | 1 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1
        | 2 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.1
        | 3 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.2.1)
      = EvmWord.mod a b := by
  have hbase := n2_shift0_remainder_eq_mod a0 a1 a2 a3 b0 b1 hb1ge bltu_2 bltu_1 bltu_0
    hc2 hm2 hc1 hm1 hc0 hm0
  refine hbase.trans ?_
  congr 1
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id a]
    congr 1
    funext i
    fin_cases i <;> simp only [ha0, ha1, ha2, ha3]
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id b]
    congr 1
    funext i
    fin_cases i <;> simp only [hb0, hb1, hb2z, hb3z]


open EvmAsm.Rv64

/-- The four `(EvmWord.mod a b).getLimbN i` shift=0 digit equalities. -/
theorem n2_shift0_mod_getLimbN_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2z : b.getLimbN 2 = 0) (hb3z : b.getLimbN 3 = 0)
    (hb1ge : b1.toNat ≥ 2^63)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    (EvmWord.mod a b).getLimbN 0 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1 ∧
    (EvmWord.mod a b).getLimbN 1 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.2.1 := by
  have hword := n2_shift0_remainder_word_eq_mod_lane a b a0 a1 a2 a3 b0 b1 bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2z hb3z hb1ge hc2 hm2 hc1 hm1 hc0 hm0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hword]
  · exact EvmWord.getLimbN_fromLimbs_0
  · exact EvmWord.getLimbN_fromLimbs_1
  · exact EvmWord.getLimbN_fromLimbs_2
  · exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
