/-
  EvmAsm.Evm64.EvmWordArith.Normalization

  Normalization properties for Knuth's Algorithm D: shifting both dividend
  and divisor by the same amount preserves the quotient. Used to bridge
  the algorithm's normalized computation back to the original division.
-/

import EvmAsm.Evm64.EvmWordArith.MulSubChain
import EvmAsm.Evm64.EvmWordArith.Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Nat-level normalization: shifting preserves quotient
-- ============================================================================

/-- Normalization preserves the quotient: `(a * 2^s) / (b * 2^s) = a / b`. -/
theorem norm_div_eq {a b s : Nat} :
    (a * 2^s) / (b * 2^s) = a / b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · rw [Nat.mul_comm a, Nat.mul_comm b, Nat.mul_div_mul_left _ _ (by positivity)]

/-- Normalization scales the remainder: `(a * 2^s) % (b * 2^s) = (a % b) * 2^s`. -/
theorem norm_mod_eq {a b s : Nat} :
    (a * 2^s) % (b * 2^s) = (a % b) * 2^s :=
  Nat.mul_mod_mul_right (2^s) a b

/-- Denormalization: dividing the scaled remainder by 2^s gives the true remainder. -/
theorem denorm_mod_eq {a b s : Nat} :
    (a * 2^s) % (b * 2^s) / 2^s = a % b := by
  rw [norm_mod_eq, Nat.mul_comm, Nat.mul_div_cancel_left _ (by positivity : 0 < 2^s)]

-- ============================================================================
-- Bridge from normalized Euclidean property to original division
-- ============================================================================

/-- If we prove the Euclidean property for normalized values `a' = a * 2^s`,
    `b' = b * 2^s`, the quotient is the same as for the original values,
    and the remainder can be recovered by dividing by 2^s. -/
theorem norm_euclidean_bridge {a b q r s : Nat}
    (h_eq : a * 2^s = b * 2^s * q + r)
    (h_rem : r < b * 2^s) :
    q = a / b ∧ r / 2^s = a % b := by
  have hs : 0 < 2^s := by positivity
  -- r is divisible by 2^s
  have h_dvd : 2^s ∣ r := by
    have : r = a * 2^s - b * 2^s * q := by omega
    rw [this]; exact Nat.dvd_sub ⟨a, by ring⟩ ⟨b * q, by ring⟩
  obtain ⟨r', hr'⟩ := h_dvd; subst hr'
  have ha : a = b * q + r' := by nlinarith [Nat.mul_comm (2^s) r']
  have hr'_lt : r' < b := by nlinarith [Nat.mul_comm (2^s) r']
  constructor
  · have h4 : q * b ≤ a := by nlinarith
    have h5 : a < (q + 1) * b := by nlinarith
    exact (Nat.div_eq_of_lt_le h4 h5).symm
  · rw [Nat.mul_div_cancel_left _ hs]
    have hq : q = a / b := by
      have h4 : q * b ≤ a := by nlinarith
      have h5 : a < (q + 1) * b := by nlinarith
      exact (Nat.div_eq_of_lt_le h4 h5).symm
    have := Nat.div_add_mod a b
    nlinarith [Nat.mul_comm b (a / b)]

-- ============================================================================
-- No-overflow for EvmWord.div/mod
-- ============================================================================

/-- The no-overflow condition holds for the true quotient and remainder. -/
theorem div_mod_no_overflow (a b : EvmWord) (hb : b ≠ 0) :
    b.toNat * (EvmWord.div a b).toNat + (EvmWord.mod a b).toNat < 2^256 := by
  unfold EvmWord.div EvmWord.mod; simp only [if_neg hb]
  have h1 : (BitVec.udiv a b).toNat = a.toNat / b.toNat := BitVec.toNat_udiv
  have h2 : (BitVec.umod a b).toNat = a.toNat % b.toNat := BitVec.toNat_umod
  rw [h1, h2]
  nlinarith [a.isLt, Nat.div_add_mod a.toNat b.toNat, Nat.mul_comm b.toNat (a.toNat / b.toNat)]

end EvmWord

end EvmAsm.Evm64
