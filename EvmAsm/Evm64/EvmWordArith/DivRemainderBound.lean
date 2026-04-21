/-
  EvmAsm.Evm64.EvmWordArith.DivRemainderBound

  Remainder bound lemmas for Knuth's Algorithm D division correctness.
  These connect the trial quotient overestimate property to the Euclidean
  division correctness, establishing that the remainder is in range.

  Key results:
  - quotient_le_of_euclidean: a = q*b + r → q ≤ a/b
  - remainder_lt_of_ge_floor: a = q*b + r, a/b ≤ q → q = a/b ∧ r < b
  - mulsub_no_underflow_correct: no-underflow mulsub + overestimate → correct quotient
  - mulsub_addback_correct: underflow + addback + overestimate → correct quotient
  - val256_euclidean_to_div_mod: val256 Euclidean property → EvmWord.div/mod
-/

import EvmAsm.Evm64.EvmWordArith.DivAddbackLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Core number theory: quotient bounds from Euclidean equations
-- ============================================================================

/-- If `a = q * b + r` (Nat) with `b > 0`, then `q ≤ a / b`.
    The quotient in a Euclidean equation can never exceed the floor division. -/
theorem quotient_le_of_euclidean {a b q r : Nat} (hb : 0 < b)
    (heq : a = q * b + r) : q ≤ a / b := by
  have : q * b ≤ a := by omega
  exact Nat.le_div_iff_mul_le hb |>.mpr this

/-- If `a = q * b + r` (Nat) with `b > 0` and `a / b ≤ q`,
    then `q = a / b` and `r < b`.

    This is the fundamental reason the Algorithm D mulsub step works:
    the trial quotient overestimates (`q ≥ a/b` from Knuth's Theorem B),
    so if no underflow occurs (`r ≥ 0`, automatic for Nat), the quotient
    must be exact and the remainder in range.

    Proof: `q ≤ a/b` from the Euclidean equation, combined with `a/b ≤ q`,
    gives `q = a/b`. Then `r = a - (a/b)*b = a mod b < b`. -/
theorem remainder_lt_of_ge_floor {a b q r : Nat} (hb : 0 < b)
    (heq : a = q * b + r) (hge : a / b ≤ q) : q = a / b ∧ r < b := by
  have hle := quotient_le_of_euclidean hb heq
  have hqeq : q = a / b := by omega
  subst hqeq
  constructor
  · rfl
  · have h1 := Nat.div_add_mod a b
    have h2 := Nat.mod_lt a hb
    nlinarith [Nat.mul_comm b (a / b)]

-- ============================================================================
-- Mulsub no-underflow case: val256 Euclidean + overestimate → correct
-- ============================================================================

/-- No-underflow mulsub correctness: if the multiply-subtract chain produces
    `val256(u) = val256(r) + q * val256(v)` (cb3 = 0) and the trial quotient
    overestimates (`q ≥ ⌊val256(u)/val256(v)⌋`), then q is the exact
    quotient and the remainder is in range.

    This is the happy path of Algorithm D: mulsub doesn't underflow,
    so no addback is needed, and the result is directly correct. -/
theorem mulsub_no_underflow_correct {uVal vVal qNat r_val : Nat}
    (hv : 0 < vVal)
    (hmulsub : uVal = r_val + qNat * vVal)
    (hge : uVal / vVal ≤ qNat) :
    qNat = uVal / vVal ∧ r_val < vVal := by
  have heq : uVal = qNat * vVal + r_val := by omega
  exact remainder_lt_of_ge_floor hv heq hge

-- ============================================================================
-- Mulsub underflow + addback case
-- ============================================================================

/-- Underflow implies strict overestimate: if `u < q * v` (mulsub underflowed),
    then `u / v + 1 ≤ q`. Equivalently, the quotient digit strictly exceeds the
    floor division value. -/
theorem underflow_imp_strict_overestimate {uVal vVal qNat : Nat}
    (hoverflow : uVal < qNat * vVal) :
    uVal / vVal + 1 ≤ qNat := by
  -- q * v > u means q > u / v
  have : uVal / vVal < qNat := by
    by_contra h; push Not at h
    have := Nat.div_mul_le_self uVal vVal
    nlinarith [Nat.mul_le_mul_right vVal h]
  omega

/-- Addback correctness: after mulsub underflow and addback, the corrected
    quotient (q-1) satisfies the Euclidean property with remainder in range.

    Given:
    - mulsub with underflow: `u + 2^256 = r_ms + q * v` (cb3 = 1)
    - addback: `r_ms + v = r_ab + 2^256` (carry = 1)
    - trial quotient overestimates: `q ≥ u / v`
    - underflow occurred: `q * v > u` (otherwise cb3 would be 0)

    Then: `q - 1 = u / v` and `r_ab < v`. -/
theorem mulsub_addback_correct {uVal vVal qNat rAbVal : Nat}
    (hv : 0 < vVal)
    (h_combined : uVal = rAbVal + (qNat - 1) * vVal)
    (hge : uVal / vVal + 1 ≤ qNat) :
    qNat - 1 = uVal / vVal ∧ rAbVal < vVal := by
  have hge0 := Nat.zero_le (uVal / vVal)
  have hq1 : qNat ≥ 1 := by omega
  have heq : uVal = (qNat - 1) * vVal + rAbVal := by omega
  have hge' : uVal / vVal ≤ qNat - 1 := by omega
  exact remainder_lt_of_ge_floor hv heq hge'

-- ============================================================================
-- Combined: either path gives correct Euclidean division
-- ============================================================================

/-- Combined single-iteration correctness: given the mulsub chain output and
    the trial quotient overestimate, either:
    - No underflow (cb3 = 0): q is correct, remainder in range
    - Underflow (cb3 = 1) + addback: q-1 is correct, corrected remainder in range

    This produces the final quotient digit and remainder for one iteration. -/
theorem single_iteration_correct {uVal vVal q_digit r_val : Nat}
    (hv : 0 < vVal)
    (heuclidean : uVal = q_digit * vVal + r_val)
    (hge : uVal / vVal ≤ q_digit) :
    q_digit = uVal / vVal ∧ r_val = uVal % vVal ∧ r_val < vVal := by
  have ⟨hq, hr_lt⟩ := remainder_lt_of_ge_floor hv heuclidean hge
  subst hq
  have h_mod := Nat.div_add_mod uVal vVal
  refine ⟨rfl, ?_, hr_lt⟩
  nlinarith [Nat.mul_comm vVal (uVal / vVal)]

-- ============================================================================
-- val256-level Euclidean → EvmWord.div/mod via fromLimbs
-- ============================================================================

/-- Convert a val256-level Euclidean property to EvmWord.div/mod correctness.

    Given limb-level values satisfying the Euclidean property at the Nat level,
    this bridges to the EvmWord operations via fromLimbs. -/
theorem val256_euclidean_to_div_mod
    {a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 r0 r1 r2 r3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (heq : val256 a0 a1 a2 a3 =
           val256 q0 q1 q2 q3 * val256 b0 b1 b2 b3 + val256 r0 r1 r2 r3)
    (hlt : val256 r0 r1 r2 r3 < val256 b0 b1 b2 b3) :
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => r0 | 1 => r1 | 2 => r2 | 3 => r3
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro a b q r
  have ha : a.toNat = val256 a0 a1 a2 a3 := (val256_eq_fromLimbs_toNat a0 a1 a2 a3).symm
  have hb : b.toNat = val256 b0 b1 b2 b3 := (val256_eq_fromLimbs_toNat b0 b1 b2 b3).symm
  have hq : q.toNat = val256 q0 q1 q2 q3 := (val256_eq_fromLimbs_toNat q0 q1 q2 q3).symm
  have hr : r.toNat = val256 r0 r1 r2 r3 := (val256_eq_fromLimbs_toNat r0 r1 r2 r3).symm
  have hbnz' : b ≠ 0 := fromLimbs_ne_zero_of_or hbnz
  have h_nat_eq : a.toNat = b.toNat * q.toNat + r.toNat := by
    rw [ha, hb, hq, hr]; nlinarith [Nat.mul_comm (val256 q0 q1 q2 q3) (val256 b0 b1 b2 b3)]
  have h_nat_lt : r.toNat < b.toNat := by rw [hr, hb]; exact hlt
  exact div_from_mulsub hbnz' h_nat_eq h_nat_lt

-- ============================================================================
-- Normalization round-trip: normalized Euclidean → original div/mod
-- ============================================================================

/-- Normalization round-trip for division: if we establish the Euclidean property
    for normalized values (a*2^s, b*2^s), we can recover the original quotient
    and remainder.

    Given:
    - Normalized Euclidean: `a*2^s = q * (b*2^s) + r'` with `r' < b*2^s`
    - Then: `q = a/b` and `r'/2^s = a%b`

    This is used when shift ≠ 0: the algorithm normalizes, computes, then
    denormalizes the remainder by right-shifting by s. -/
theorem norm_euclidean_correct {aVal bVal qNat r_norm : Nat} (s : Nat)
    (heq : aVal * 2^s = qNat * (bVal * 2^s) + r_norm)
    (hlt : r_norm < bVal * 2^s) :
    qNat = aVal / bVal ∧ r_norm / 2^s = aVal % bVal := by
  -- Convert to the form expected by norm_euclidean_bridge
  have heq' : aVal * 2^s = bVal * 2^s * qNat + r_norm := by linarith
  exact norm_euclidean_bridge heq' hlt

end EvmWord

end EvmAsm.Evm64
