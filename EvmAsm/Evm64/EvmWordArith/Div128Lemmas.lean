/-
  EvmAsm.Evm64.EvmWordArith.Div128Lemmas

  Mathematical foundations for div128 correctness and multi-limb division:
  - Half-word OR-combine (non-overlapping shift+OR = add)
  - 128-bit Euclidean uniqueness
  - Trial quotient bounds (Knuth TAOCP 4.3.1): generalized and 256→128 level
  - Product check correction: reduces overestimate from ≤ 2 to ≤ 1
  - Full half-round theorem (overflow + product check)
  - Mulsub borrow bound for n ≤ 3 (v3 = 0): c3 ≤ 1 unconditionally
-/

import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Half-word OR-combine: non-overlapping shift+OR = add
-- ============================================================================

/-- Combining two half-words via shift-left + OR gives addition at the Nat level,
    since the bit ranges [63:32] and [31:0] are disjoint. -/
theorem halfword_combine (a b : Word) (ha : a.toNat < 2^32) (hb : b.toNat < 2^32) :
    (a <<< 32 ||| b).toNat = a.toNat * 2^32 + b.toNat := by
  have h_disjoint : a <<< 32 &&& b = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases hi : (i : Nat) < 32
    · simp [hi]
    · simp only [hi, decide_false, Bool.not_false, Bool.true_and]
      have hbi : b[i] = false := by
        simp only [BitVec.getElem_eq_testBit_toNat]
        apply Nat.testBit_lt_two_pow
        calc b.toNat < 2 ^ 32 := hb
          _ ≤ 2 ^ (i : Nat) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hbi]
  rw [(BitVec.add_eq_or_of_and_eq_zero (a <<< 32) b h_disjoint).symm,
      BitVec.toNat_add_of_and_eq_zero h_disjoint,
      BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show a.toNat * 2 ^ 32 < 2 ^ 64 by nlinarith)]

/-- Corollary: combining hi32 and lo32 of a word reconstructs it at the Nat level. -/
theorem halfword_combine_hi_lo (x : Word) :
    (hi32 x <<< 32 ||| lo32 x).toNat = x.toNat := by
  rw [halfword_combine _ _ (hi32_toNat_lt x) (lo32_toNat_lt x)]
  exact (halfword_decompose x).symm

-- ============================================================================
-- 128-bit Euclidean uniqueness (Nat level)
-- ============================================================================

/-- If `val128 u_hi u_lo = d * q + r` with `r < d`, then `q = val128 u_hi u_lo / d`.
    Used to verify div128 output by checking the division equation and remainder bound. -/
theorem val128_div_unique (u_hi u_lo : Word) (d q r : Nat)
    (hr : r < d)
    (heq : val128 u_hi u_lo = d * q + r) :
    q = val128 u_hi u_lo / d := by
  have h1 : q * d ≤ val128 u_hi u_lo := by rw [heq]; nlinarith [Nat.mul_comm d q]
  have h2 : val128 u_hi u_lo < (q + 1) * d := by rw [heq]; nlinarith [Nat.mul_comm d q]
  exact (Nat.div_eq_of_lt_le h1 h2).symm

/-- Remainder uniqueness: if the Euclidean equation holds, the remainder equals mod. -/
theorem val128_mod_unique (u_hi u_lo : Word) (d q r : Nat)
    (hr : r < d)
    (heq : val128 u_hi u_lo = d * q + r) :
    r = val128 u_hi u_lo % d := by
  have hq := val128_div_unique u_hi u_lo d q r hr heq
  have hdm := Nat.div_add_mod (val128 u_hi u_lo) d
  subst hq; nlinarith [Nat.mul_comm d (val128 u_hi u_lo / d)]

-- ============================================================================
-- Trial quotient bounds (Knuth TAOCP Vol 2, Section 4.3.1)
-- ============================================================================

-- The trial quotient q̂ = ⌊u_hi / d_hi⌋ overestimates the true quotient digit
-- qTrue = ⌊(u_hi * B + un1) / d⌋ where d = d_hi * B + d_lo, B = 2^32.
--
-- Bound 1 (no normalization needed): q̂ ≥ qTrue
-- Bound 2 (normalization: d_hi ≥ B/2): q̂ ≤ qTrue + 2

/-- Trial quotient upper bound: `⌊u_hi / d_hi⌋ ≥ ⌊(u_hi * B + un1) / d⌋`.
    The trial quotient never underestimates. No normalization needed.

    Proof idea: `(q̂ + 1) * d_hi > u_hi`, so `(q̂ + 1) * d > u_hi * B + un1`. -/
theorem trial_quotient_ge (u_hi un1 d_hi d_lo : Nat)
    (hd_hi : 0 < d_hi) (hun1 : un1 < 2^32) :
    (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) ≤ u_hi / d_hi := by
  have hd_pos : 0 < d_hi * 2^32 + d_lo := by positivity
  have : (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) < u_hi / d_hi + 1 :=
    (Nat.div_lt_iff_lt_mul hd_pos).mpr (by
      have hq : u_hi < d_hi * (u_hi / d_hi + 1) := Nat.lt_mul_div_succ u_hi hd_hi
      calc u_hi * 2^32 + un1
          < (u_hi + 1) * 2^32 := by nlinarith
        _ ≤ d_hi * (u_hi / d_hi + 1) * 2^32 := by nlinarith
        _ = (u_hi / d_hi + 1) * (d_hi * 2^32) := by ring
        _ ≤ (u_hi / d_hi + 1) * (d_hi * 2^32 + d_lo) := by nlinarith)
  omega

/-- Trial quotient lower bound: `⌊u_hi / d_hi⌋ ≤ ⌊(u_hi * B + un1) / d⌋ + 2`.
    The trial quotient overestimates by at most 2 when d_hi ≥ B/2 (normalized).

    This is the key bound from Knuth's analysis. The normalization condition ensures
    `q̂ ≤ B + 1`, so `q̂ * d_lo < B² ≤ 2d`, giving `q̂ * d ≤ u_hi * B + 2d`. -/
theorem trial_quotient_le (u_hi un1 d_hi d_lo : Nat)
    (hd_hi_bound : d_hi < 2^32) (hd_lo : d_lo < 2^32)
    (hun1 : un1 < 2^32) (hu : u_hi < d_hi * 2^32 + d_lo) (hnorm : d_hi ≥ 2^31) :
    u_hi / d_hi ≤ (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) + 2 := by
  have hd_hi : 0 < d_hi := by omega
  set d := d_hi * 2^32 + d_lo
  set qHat := u_hi / d_hi
  have hd_pos : 0 < d := by positivity
  have hq_mul : qHat * d_hi ≤ u_hi := Nat.div_mul_le_self u_hi d_hi
  -- q̂ ≤ B + 1: if q̂ ≥ B+2 then q̂*d_hi ≥ (B+2)*d_hi, giving 2*d_hi ≤ d_lo,
  -- contradicting d_hi ≥ B/2 and d_lo < B.
  have hq_bound : qHat ≤ 2^32 + 1 := by
    by_contra h_contra; push Not at h_contra
    have h1 : (2^32 + 2) * d_hi ≤ qHat * d_hi := Nat.mul_le_mul_right d_hi (by omega)
    have h2 : 2 * d_hi ≤ d_lo := by omega
    omega
  -- q̂ * d_lo < B² ≤ 2d
  have hq_dlo_bound : qHat * d_lo < 2^64 := by
    have : d_lo ≤ 2^32 - 1 := by omega
    have : qHat * d_lo ≤ (2^32 + 1) * (2^32 - 1) := Nat.mul_le_mul hq_bound this
    norm_num at this ⊢; omega
  have h2d_ge : 2 * d ≥ 2^64 := by
    show 2 * (d_hi * 2^32 + d_lo) ≥ _; omega
  have hq_d_eq : qHat * d = qHat * d_hi * 2^32 + qHat * d_lo := by
    show qHat * (d_hi * 2^32 + d_lo) = _; ring
  -- Key: q̂ * d ≤ u_hi * B + 2d ≤ X + 2d where X = u_hi * B + un1
  set X := u_hi * 2^32 + un1
  have key : qHat * d ≤ X + 2 * d := by
    calc qHat * d = qHat * d_hi * 2^32 + qHat * d_lo := hq_d_eq
      _ ≤ u_hi * 2^32 + qHat * d_lo := by nlinarith
      _ ≤ u_hi * 2^32 + 2^64 := by omega
      _ ≤ u_hi * 2^32 + 2 * d := by omega
      _ ≤ X + 2 * d := by omega
  -- Convert: q̂ * d ≤ X + 2d < (X/d + 3) * d → q̂ < X/d + 3 → q̂ ≤ X/d + 2
  have hXmod : X < (X / d + 1) * d := by
    have := Nat.div_add_mod X d; have := Nat.mod_lt X hd_pos; nlinarith
  have hlt : qHat * d < (X / d + 3) * d := by nlinarith
  have : qHat < X / d + 3 := by
    by_contra hc; push Not at hc
    exact Nat.not_lt.mpr (Nat.mul_le_mul_right d hc) hlt
  omega

/-- Combined: the trial quotient is within 2 of the true value.
    `qTrue ≤ q̂ ≤ qTrue + 2` when `d_hi ≥ B/2` (normalization condition). -/
theorem trial_quotient_range (u_hi un1 d_hi d_lo : Nat)
    (hd_hi_bound : d_hi < 2^32) (hd_lo : d_lo < 2^32)
    (hun1 : un1 < 2^32) (hu : u_hi < d_hi * 2^32 + d_lo) (hnorm : d_hi ≥ 2^31) :
    let qHat := u_hi / d_hi
    let qTrue := (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo)
    qTrue ≤ qHat ∧ qHat ≤ qTrue + 2 :=
  ⟨trial_quotient_ge u_hi un1 d_hi d_lo (by omega) hun1,
   trial_quotient_le u_hi un1 d_hi d_lo hd_hi_bound hd_lo hun1 hu hnorm⟩

-- ============================================================================
-- Product check correction: reduces overestimate from ≤ 2 to ≤ 1
-- ============================================================================

-- After computing q̂ = ⌊u_hi / d_hi⌋ and r̂ = u_hi mod d_hi, the div128
-- algorithm checks: is q̂ * d_lo > r̂ * B + un1?
-- If yes, q̂ overestimates by ≥ 1, so decrement.
-- After at most one correction, the overestimate is ≤ 1.

/-- Product check soundness: if `q̂ * d_lo > r̂ * B + un1`,
    then `q̂ > qTrue` (the trial quotient strictly overestimates).

    Proof: q̂ * d = q̂ * d_hi * B + q̂ * d_lo > r̂ * d_hi * B + r̂ * B + un1
    and from r̂ = u_hi - q̂ * d_hi: q̂ * d_hi = u_hi - r̂,
    so q̂ * d > (u_hi - r̂) * B + r̂ * B + un1 = u_hi * B + un1. -/
theorem product_check_gt_imp_overestimate (u_hi un1 d_hi d_lo qHat r_hat : Nat)
    (B : Nat := 2^32)
    (hd_pos : 0 < d_hi * B + d_lo)
    (hr_hat : r_hat = u_hi - qHat * d_hi)
    (hq_mul : qHat * d_hi ≤ u_hi)
    (hcheck : qHat * d_lo > r_hat * B + un1) :
    qHat > (u_hi * B + un1) / (d_hi * B + d_lo) := by
  set d := d_hi * B + d_lo
  set X := u_hi * B + un1
  -- q̂ * d = q̂ * d_hi * B + q̂ * d_lo > (u_hi - r̂) * B + r̂ * B + un1 = X
  have hqd_gt : qHat * d > X := by
    calc qHat * d = qHat * (d_hi * B + d_lo) := rfl
      _ = qHat * d_hi * B + qHat * d_lo := by ring
      _ > qHat * d_hi * B + r_hat * B + un1 := by omega
      _ = (qHat * d_hi + r_hat) * B + un1 := by ring
      _ = u_hi * B + un1 := by
            rw [hr_hat, Nat.add_sub_cancel' hq_mul]
  exact (Nat.div_lt_iff_lt_mul hd_pos).mpr hqd_gt

/-- If the product check passes (`q̂ * d_lo ≤ r̂ * B + un1`), then `q̂ ≤ qTrue`.
    The trial quotient does NOT overestimate the true quotient in this branch. -/
theorem product_check_pass_imp_le (u_hi un1 d_hi d_lo qHat r_hat : Nat)
    (B : Nat := 2^32)
    (hd_pos : 0 < d_hi * B + d_lo)
    (hr_hat : r_hat = u_hi - qHat * d_hi)
    (hq_mul : qHat * d_hi ≤ u_hi)
    (hcheck_pass : qHat * d_lo ≤ r_hat * B + un1) :
    qHat ≤ (u_hi * B + un1) / (d_hi * B + d_lo) := by
  set d := d_hi * B + d_lo
  set X := u_hi * B + un1
  have hqd_le : qHat * d ≤ X := by
    calc qHat * d = qHat * (d_hi * B + d_lo) := rfl
      _ = qHat * d_hi * B + qHat * d_lo := by ring
      _ ≤ qHat * d_hi * B + r_hat * B + un1 := by omega
      _ = (qHat * d_hi + r_hat) * B + un1 := by ring
      _ = u_hi * B + un1 := by
            rw [hr_hat, Nat.add_sub_cancel' hq_mul]
  exact Nat.le_div_iff_mul_le hd_pos |>.mpr hqd_le

/-- Full correction step: after at most one correction (decrement when product check
    fails), the trial quotient overestimates by at most 1.
    - If check passes: `q̂ ≤ qTrue` (from `product_check_pass_imp_le`)
    - If check fails: `q̂ - 1 ≤ qTrue + 1` since `q̂ > qTrue` and `q̂ ≤ qTrue + 2` -/
theorem correction_step_overestimate_le_one (u_hi un1 d_hi d_lo qHat r_hat : Nat)
    (B : Nat := 2^32)
    (hd_pos : 0 < d_hi * B + d_lo)
    (hr_hat : r_hat = u_hi - qHat * d_hi)
    (hq_mul : qHat * d_hi ≤ u_hi)
    (hq_upper : qHat ≤ (u_hi * B + un1) / (d_hi * B + d_lo) + 2) :
    (if qHat * d_lo > r_hat * B + un1 then qHat - 1 else qHat) ≤
      (u_hi * B + un1) / (d_hi * B + d_lo) + 1 := by
  set qTrue := (u_hi * B + un1) / (d_hi * B + d_lo)
  split
  · -- Product check fails: decrement. q̂ > qTrue and q̂ ≤ qTrue + 2.
    rename_i hfail
    have hgt : qHat > qTrue := product_check_gt_imp_overestimate u_hi un1 d_hi d_lo qHat r_hat B
      hd_pos hr_hat hq_mul hfail
    exact Nat.sub_le_of_le_add (by omega : qHat ≤ qTrue + 1 + 1)
  · -- Product check passes: q̂ ≤ qTrue, so q̂ ≤ qTrue + 1 trivially.
    rename_i hpass
    simp only [not_lt] at hpass
    have := product_check_pass_imp_le u_hi un1 d_hi d_lo qHat r_hat B
      hd_pos hr_hat hq_mul hpass
    omega

-- ============================================================================
-- Full half-round: overflow clamp + product check = overestimate ≤ 1
-- ============================================================================

/-- Full half-round: any quotient q satisfying qTrue ≤ q ≤ qTrue + 2
    (the trial quotient range) can be corrected to qTrue ≤ q' ≤ qTrue + 1
    via the product check, provided q * d_hi ≤ u_hi (the trial division invariant).

    This captures both the overflow correction case (which reduces the bound
    from ≤ qTrue + 2 to ≤ qTrue + 1) and the no-overflow case (where
    correction_step_overestimate_le_one applies directly). -/
theorem half_round_overestimate_le_one (u_hi un1 d_hi d_lo q r : Nat)
    (hd_pos : 0 < d_hi * 2^32 + d_lo)
    (hr : r = u_hi - q * d_hi)
    (hq_mul : q * d_hi ≤ u_hi)
    (hq_ge : (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) ≤ q)
    (hq_le : q ≤ (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) + 2) :
    let qTrue := (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo)
    let q' := if q * d_lo > r * 2^32 + un1 then q - 1 else q
    qTrue ≤ q' ∧ q' ≤ qTrue + 1 := by
  constructor
  · -- Lower bound: q' ≥ qTrue
    split
    · rename_i hfail
      have hgt : q > (u_hi * 2^32 + un1) / (d_hi * 2^32 + d_lo) :=
        product_check_gt_imp_overestimate u_hi un1 d_hi d_lo q r (2^32)
          hd_pos hr hq_mul hfail
      omega
    · exact hq_ge
  · -- Upper bound: q' ≤ qTrue + 1
    exact correction_step_overestimate_le_one u_hi un1 d_hi d_lo q r (2^32)
      hd_pos hr hq_mul hq_le

-- ============================================================================
-- Generalized trial quotient bound (any base)
-- ============================================================================

/-- Generalized trial quotient bound: ⌊(u_hi * Bk + u_rest) / (d_hi * Bk + d_rest)⌋ ≤ ⌊u_hi / d_hi⌋.
    Works for any "base" Bk (e.g., 2^32, 2^64, 2^128). The trial quotient using only the
    top portions never underestimates the true quotient. -/
theorem trial_quotient_ge_general (u_hi u_rest d_hi d_rest Bk : Nat)
    (hd_hi : 0 < d_hi) (hu_rest : u_rest < Bk) :
    (u_hi * Bk + u_rest) / (d_hi * Bk + d_rest) ≤ u_hi / d_hi := by
  have hBk : 0 < Bk := by omega
  have hd_pos : 0 < d_hi * Bk + d_rest := by positivity
  have : (u_hi * Bk + u_rest) / (d_hi * Bk + d_rest) < u_hi / d_hi + 1 :=
    (Nat.div_lt_iff_lt_mul hd_pos).mpr (by
      have hq : u_hi < d_hi * (u_hi / d_hi + 1) := Nat.lt_mul_div_succ u_hi hd_hi
      calc u_hi * Bk + u_rest
          < (u_hi + 1) * Bk := by nlinarith
        _ ≤ d_hi * (u_hi / d_hi + 1) * Bk := by nlinarith
        _ = (u_hi / d_hi + 1) * (d_hi * Bk) := by ring
        _ ≤ (u_hi / d_hi + 1) * (d_hi * Bk + d_rest) := by nlinarith)
  omega

-- ============================================================================
-- val256 ↔ val128 decomposition
-- ============================================================================

/-- val256 decomposes into two val128 halves: val256 l0 l1 l2 l3 = val128 l3 l2 * 2^128 + val128 l1 l0. -/
theorem val256_eq_val128_pair (l0 l1 l2 l3 : Word) :
    val256 l0 l1 l2 l3 = val128 l3 l2 * 2 ^ 128 + val128 l1 l0 := by
  unfold val256 val128; ring

/-- val256 with top limb zero: val256 l0 l1 l2 0 = l2 * 2^128 + val128 l1 l0. -/
theorem val256_top_zero (l0 l1 l2 : Word) :
    val256 l0 l1 l2 0 = l2.toNat * 2 ^ 128 + val128 l1 l0 := by
  unfold val256 val128; simp; ring

-- ============================================================================
-- Trial quotient bound: 256-bit ÷ 192-bit level
-- ============================================================================

/-- Trial quotient bound at the 64-bit level: the trial quotient val128(u3,u2)/v2
    never underestimates the true quotient val256(u0,u1,u2,u3)/val256(v0,v1,v2,0).
    This is the 256→128 analogue of `trial_quotient_ge`. -/
theorem trial_quotient_ge_256 (u0 u1 u2 u3 v0 v1 v2 : Word) (hv2 : v2 ≠ 0) :
    val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 ≤ val128 u3 u2 / v2.toNat := by
  rw [val256_eq_val128_pair u0 u1 u2 u3, val256_top_zero v0 v1 v2]
  exact trial_quotient_ge_general (val128 u3 u2) (val128 u1 u0)
    v2.toNat (val128 v1 v0) (2 ^ 128)
    (Nat.pos_of_ne_zero (by intro h; apply hv2; exact BitVec.eq_of_toNat_eq h))
    (val128_bound u1 u0)

-- ============================================================================
-- val256 bound with zero top limb
-- ============================================================================

/-- When the top limb is zero, val256 < 2^192. -/
theorem val256_lt_pow192 (l0 l1 l2 : Word) :
    val256 l0 l1 l2 0 < 2 ^ 192 := by
  unfold val256; simp
  have h0 := l0.isLt; have h1 := l1.isLt; have h2 := l2.isLt
  nlinarith

end EvmWord

end EvmAsm.Evm64
