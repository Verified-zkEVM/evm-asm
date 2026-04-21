/-
  EvmAsm.Evm64.EvmWordArith.DivN4Lemmas

  Specialized lemmas for the n=4 division case (divisor uses all 4 limbs).
  When n=4 and shift=0, the quotient has at most 1 limb and the algorithm
  runs a single loop iteration. These lemmas establish:
  - quotient bound (≤ 1) from MSB condition
  - division correctness for the q=0 and q=1 subcases
  - val128 simplification when uHi = 0
-/

import EvmAsm.Evm64.EvmWordArith.DivBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- val128 simplification
-- ============================================================================

/-- When uHi = 0, val128 reduces to the low word's toNat. -/
theorem val128_zero_hi (uLo : Word) : val128 0 uLo = uLo.toNat := by
  unfold val128; simp

-- ============================================================================
-- Quotient bound for n=4 shift=0
-- ============================================================================

/-- When the divisor's MSB is set (d ≥ 2^63) and uHi = 0,
    the 128-bit quotient is at most 1.
    This is the key bound for n=4 shift=0: the single loop iteration
    produces a trial quotient q̂ ∈ {0, 1}. -/
theorem div_nat_le_one_of_msb (uLo d : Word) (hd : d.toNat ≥ 2^63) :
    uLo.toNat / d.toNat ≤ 1 := by
  have hulo := uLo.isLt
  have : uLo.toNat / d.toNat < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d.toNat)]
    nlinarith
  omega

-- ============================================================================
-- n=4 shift=0 correctness: q=0 case (a < b)
-- ============================================================================

private theorem bnz_of_lt {a b : EvmWord} (h : a.toNat < b.toNat) : b ≠ 0 := by
  intro heq; subst heq; simp at h

/-- When a < b, the quotient is 0. -/
theorem div_zero_of_lt (a b : EvmWord) (h_lt : a.toNat < b.toNat) :
    EvmWord.div a b = 0 :=
  (div_of_nat_euclidean a b 0 a (bnz_of_lt h_lt) (by simp) h_lt).symm

/-- When a < b, the remainder is a itself. -/
theorem mod_self_of_lt (a b : EvmWord) (h_lt : a.toNat < b.toNat) :
    EvmWord.mod a b = a :=
  (mod_of_nat_euclidean a b 0 a (bnz_of_lt h_lt) (by simp) h_lt).symm

-- ============================================================================
-- n=4 shift=0 correctness: q=1 case (b ≤ a < 2*b)
-- ============================================================================

private theorem bnz_of_lt2 {a b : EvmWord} (h : a.toNat < 2 * b.toNat) : b ≠ 0 := by
  intro heq; subst heq; simp at h

/-- When b ≤ a < 2b, the quotient is 1. -/
theorem div_one_of_ge_lt (a b : EvmWord)
    (h_ge : b.toNat ≤ a.toNat) (h_lt2 : a.toNat < 2 * b.toNat) :
    EvmWord.div a b = 1 := by
  have h1 : (1 : EvmWord).toNat = 1 := by decide
  exact (div_of_nat_euclidean a b 1 (a - b) (bnz_of_lt2 h_lt2)
    (by rw [h1, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega)
    (by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega)).symm

/-- When b ≤ a < 2b, the remainder is a - b. -/
theorem mod_sub_of_ge_lt (a b : EvmWord)
    (h_ge : b.toNat ≤ a.toNat) (h_lt2 : a.toNat < 2 * b.toNat) :
    EvmWord.mod a b = a - b := by
  have h1 : (1 : EvmWord).toNat = 1 := by decide
  exact (mod_of_nat_euclidean a b 1 (a - b) (bnz_of_lt2 h_lt2)
    (by rw [h1, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega)
    (by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h_ge)]; omega)).symm

-- ============================================================================
-- MSB condition implies divisor bound for trial quotient
-- ============================================================================

/-- If the top limb b3 has MSB set (b3 ≥ 2^63), then its upper half-word
    satisfies the normalization condition dHi ≥ 2^31 for trial quotient bounds. -/
theorem msb_imp_hi32_ge (b3 : Word) (hmsb : b3.toNat ≥ 2^63) :
    (hi32 b3).toNat ≥ 2^31 := by
  unfold hi32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb3 := b3.isLt
  exact Nat.le_div_iff_mul_le (by positivity) |>.mpr (by omega)

/-- If b3 ≥ 2^63, the full 256-bit divisor b satisfies b ≥ 2^63 * 2^192. -/
theorem val256_pos_of_b3_msb (b0 b1 b2 b3 : Word) (hmsb : b3.toNat ≥ 2^63) :
    val256 b0 b1 b2 b3 ≥ 2^63 * 2^192 := by
  unfold val256
  nlinarith

end EvmWord

end EvmAsm.Evm64
