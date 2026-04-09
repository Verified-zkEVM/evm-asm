/-
  EvmAsm.Evm64.EvmWordArith.DivAccumulate

  Multi-iteration quotient accumulation for Knuth's Algorithm D.
  Each loop iteration produces one quotient digit q_j. These lemmas show
  that the per-iteration Euclidean equations telescope into a single
  Euclidean equation for the full multi-digit quotient.

  For n-limb divisor, there are (4-n+1) = (5-n) iterations producing
  (5-n) quotient digits. The accumulated quotient is:
    val256(q0, q1, ..., q_{4-n}, 0, ..., 0) = q0 + q1*2^64 + ...

  Key results:
  - iter_accumulate_{1,2,3,4}: telescoping for 1..4 iterations
  - val256_zero_upper_{1,2,3}: val256 with trailing zero limbs
  - accumulated_quotient_correct: full chain from iterations to EvmWord.div
-/

import EvmAsm.Evm64.EvmWordArith.DivRemainderBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- val256 with trailing zeros (simplification lemmas)
-- ============================================================================

/-- val256 with upper 3 limbs zero: reduces to single limb. -/
theorem val256_zero_upper_3 (q0 : Word) :
    val256 q0 0 0 0 = q0.toNat := by
  unfold val256; simp

/-- val256 with upper 2 limbs zero: reduces to 2-limb value. -/
theorem val256_zero_upper_2 (q0 q1 : Word) :
    val256 q0 q1 0 0 = q0.toNat + q1.toNat * 2^64 := by
  unfold val256; simp

/-- val256 with upper 1 limb zero: reduces to 3-limb value. -/
theorem val256_zero_upper_1 (q0 q1 q2 : Word) :
    val256 q0 q1 q2 0 = q0.toNat + q1.toNat * 2^64 + q2.toNat * 2^128 := by
  unfold val256; simp

-- ============================================================================
-- Per-iteration Euclidean equations: telescoping
-- ============================================================================

-- In Knuth's Algorithm D, each iteration j processes the dividend window
-- u[j..j+n] and produces quotient digit q_j. The per-iteration equation is:
--
--   u_before = q_j * v + u_after   (at the appropriate limb scale)
--
-- where u_before includes a "high limb" that gets absorbed. For a sliding
-- window: u_before_j = u_after_{j+1} * 2^64 + u_low_j.
--
-- The key observation is that these equations telescope:
--   u_total = (q_{m}*B^m + ... + q_0) * v + remainder

/-- 1 iteration (n=4 case): the single mulsub directly gives the Euclidean equation.
    No accumulation needed — this is the base case. -/
theorem iter_accumulate_1 {u_val v_val q0_nat r_val : Nat}
    (h0 : u_val = q0_nat * v_val + r_val) :
    u_val = q0_nat * v_val + r_val := h0

/-- 2 iterations (n=3 case): digits q1 (high) and q0 (low).

    Iteration 1 (j=1): operates on u[1..4], produces q1.
      u_hi * 2^64 + u_lo_part = q1 * v + u'
    This means the "upper portion" of the dividend satisfies the equation.

    Iteration 0 (j=0): operates on u'[0..3], produces q0.
      u' = q0 * v + r

    Combined: u_hi * 2^64 + u_lo_part = (q1 * 2^64 + q0) * v + r
    But we work at the full val level where the iteration equations are:

    iter 1: u_total = q1 * (v * 2^64) + u'_total  (q1 accounts for position)
    iter 0: u'_total = q0 * v + r

    Actually, in Algorithm D, the iterations work on shifted windows. Let me
    use a more direct formulation: the accumulated quotient digits form the
    full quotient. -/
theorem iter_accumulate_2 {u_val v_val q1_nat q0_nat mid_val r_val : Nat}
    (h1 : u_val = q1_nat * v_val * 2^64 + mid_val)
    (h0 : mid_val = q0_nat * v_val + r_val) :
    u_val = (q1_nat * 2^64 + q0_nat) * v_val + r_val := by
  nlinarith

/-- 3 iterations (n=2 case): digits q2, q1, q0. -/
theorem iter_accumulate_3 {u_val v_val q2_nat q1_nat q0_nat mid2_val mid1_val r_val : Nat}
    (h2 : u_val = q2_nat * v_val * 2^128 + mid2_val)
    (h1 : mid2_val = q1_nat * v_val * 2^64 + mid1_val)
    (h0 : mid1_val = q0_nat * v_val + r_val) :
    u_val = (q2_nat * 2^128 + q1_nat * 2^64 + q0_nat) * v_val + r_val := by
  nlinarith

/-- 4 iterations (n=1 case): digits q3, q2, q1, q0. -/
theorem iter_accumulate_4
    {u_val v_val q3_nat q2_nat q1_nat q0_nat mid3_val mid2_val mid1_val r_val : Nat}
    (h3 : u_val = q3_nat * v_val * 2^192 + mid3_val)
    (h2 : mid3_val = q2_nat * v_val * 2^128 + mid2_val)
    (h1 : mid2_val = q1_nat * v_val * 2^64 + mid1_val)
    (h0 : mid1_val = q0_nat * v_val + r_val) :
    u_val = (q3_nat * 2^192 + q2_nat * 2^128 + q1_nat * 2^64 + q0_nat) * v_val + r_val := by
  nlinarith

-- ============================================================================
-- Connecting accumulated quotient digits to val256
-- ============================================================================

/-- For n=4 (1 digit): the quotient is just q0, matching val256(q0, 0, 0, 0). -/
theorem accumulated_eq_val256_n4 (q0 : Word) :
    q0.toNat = val256 q0 0 0 0 := by
  rw [val256_zero_upper_3]

/-- For n=3 (2 digits): the accumulated quotient matches val256(q0, q1, 0, 0). -/
theorem accumulated_eq_val256_n3 (q0 q1 : Word) :
    q1.toNat * 2^64 + q0.toNat = val256 q0 q1 0 0 := by
  rw [val256_zero_upper_2]; ring

/-- For n=2 (3 digits): the accumulated quotient matches val256(q0, q1, q2, 0). -/
theorem accumulated_eq_val256_n2 (q0 q1 q2 : Word) :
    q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat = val256 q0 q1 q2 0 := by
  rw [val256_zero_upper_1]; ring

/-- For n=1 (4 digits): the accumulated quotient matches val256(q0, q1, q2, q3). -/
theorem accumulated_eq_val256_n1 (q0 q1 q2 q3 : Word) :
    q3.toNat * 2^192 + q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat =
    val256 q0 q1 q2 q3 := by
  unfold val256; ring

-- ============================================================================
-- End-to-end: iterations + remainder bound → EvmWord.div/mod
-- ============================================================================

/-- End-to-end for n=4 (1 iteration, no shift):
    mulsub equation + overestimate → EvmWord.div/mod correctness via val256. -/
theorem div_correct_n4_no_shift
    {a0 a1 a2 a3 b0 b1 b2 b3 q0 r0 r1 r2 r3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : val256 a0 a1 a2 a3 = q0.toNat * val256 b0 b1 b2 b3 +
               val256 r0 r1 r2 r3)
    (hge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ q0.toNat) :
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => q0 | 1 => (0 : Word) | 2 => (0 : Word) | 3 => (0 : Word)
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => r0 | 1 => r1 | 2 => r2 | 3 => r3
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro a b q r
  have hv := val256_pos_of_or_ne_zero b0 b1 b2 b3 hbnz
  have ⟨_, hr_lt⟩ := remainder_lt_of_ge_floor hv hmulsub hge
  -- val256(q0, 0, 0, 0) = q0.toNat
  have hq_val : val256 q0 0 0 0 = q0.toNat := val256_zero_upper_3 q0
  have hmulsub' : val256 a0 a1 a2 a3 =
      val256 q0 0 0 0 * val256 b0 b1 b2 b3 + val256 r0 r1 r2 r3 := by
    rw [hq_val]; exact hmulsub
  exact val256_euclidean_to_div_mod hbnz hmulsub' hr_lt

/-- End-to-end for n=3 (2 iterations, no shift):
    Two mulsub iterations produce q1, q0. The accumulated quotient
    val256(q0, q1, 0, 0) gives EvmWord.div/mod. -/
theorem div_correct_n3_no_shift
    {a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 r0 r1 r2 r3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : val256 a0 a1 a2 a3 =
               (q1.toNat * 2^64 + q0.toNat) * val256 b0 b1 b2 b3 +
               val256 r0 r1 r2 r3)
    (hge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
           q1.toNat * 2^64 + q0.toNat) :
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => q0 | 1 => q1 | 2 => (0 : Word) | 3 => (0 : Word)
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => r0 | 1 => r1 | 2 => r2 | 3 => r3
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro a b q r
  have hv := val256_pos_of_or_ne_zero b0 b1 b2 b3 hbnz
  have ⟨_, hr_lt⟩ := remainder_lt_of_ge_floor hv hmulsub hge
  have hq_val : val256 q0 q1 0 0 = q1.toNat * 2^64 + q0.toNat :=
    (accumulated_eq_val256_n3 q0 q1).symm
  have hmulsub' : val256 a0 a1 a2 a3 =
      val256 q0 q1 0 0 * val256 b0 b1 b2 b3 + val256 r0 r1 r2 r3 := by
    rw [hq_val]; exact hmulsub
  exact val256_euclidean_to_div_mod hbnz hmulsub' hr_lt

/-- End-to-end for n=2 (3 iterations, no shift). -/
theorem div_correct_n2_no_shift
    {a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 r0 r1 r2 r3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : val256 a0 a1 a2 a3 =
               (q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat) *
               val256 b0 b1 b2 b3 + val256 r0 r1 r2 r3)
    (hge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
           q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat) :
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => q0 | 1 => q1 | 2 => q2 | 3 => (0 : Word)
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => r0 | 1 => r1 | 2 => r2 | 3 => r3
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro a b q r
  have hv := val256_pos_of_or_ne_zero b0 b1 b2 b3 hbnz
  have ⟨_, hr_lt⟩ := remainder_lt_of_ge_floor hv hmulsub hge
  have hq_val : val256 q0 q1 q2 0 = q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat :=
    (accumulated_eq_val256_n2 q0 q1 q2).symm
  have hmulsub' : val256 a0 a1 a2 a3 =
      val256 q0 q1 q2 0 * val256 b0 b1 b2 b3 + val256 r0 r1 r2 r3 := by
    rw [hq_val]; exact hmulsub
  exact val256_euclidean_to_div_mod hbnz hmulsub' hr_lt

/-- End-to-end for n=1 (4 iterations, no shift). -/
theorem div_correct_n1_no_shift
    {a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 r0 r1 r2 r3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : val256 a0 a1 a2 a3 =
               (q3.toNat * 2^192 + q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat) *
               val256 b0 b1 b2 b3 + val256 r0 r1 r2 r3)
    (hge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
           q3.toNat * 2^192 + q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat) :
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
  have hv := val256_pos_of_or_ne_zero b0 b1 b2 b3 hbnz
  have ⟨_, hr_lt⟩ := remainder_lt_of_ge_floor hv hmulsub hge
  have hq_val : val256 q0 q1 q2 q3 =
      q3.toNat * 2^192 + q2.toNat * 2^128 + q1.toNat * 2^64 + q0.toNat :=
    (accumulated_eq_val256_n1 q0 q1 q2 q3).symm
  have hmulsub' : val256 a0 a1 a2 a3 =
      val256 q0 q1 q2 q3 * val256 b0 b1 b2 b3 + val256 r0 r1 r2 r3 := by
    rw [hq_val]; exact hmulsub
  exact val256_euclidean_to_div_mod hbnz hmulsub' hr_lt

-- ============================================================================
-- With normalization: shifted dividend/divisor → original div/mod
-- ============================================================================

/-- General normalization bridge at the val256 level: accumulated quotient digits
    at normalized level → quotient equals original a/b.

    Given the Euclidean equation at the normalized level:
      val256(a) * 2^s = q_val * (val256(b) * 2^s) + r_norm
    with r_norm < val256(b) * 2^s, we get q_val = val256(a) / val256(b).

    This handles all n-cases and both shift=0 and shift≠0. For shift=0,
    use s=0 (2^0 = 1, so the equation simplifies to val256(a) = q_val * val256(b) + r). -/
theorem div_quotient_of_normalized {a_val b_val q_val r_norm : Nat} (s : Nat)
    (hmulsub : a_val * 2^s = q_val * (b_val * 2^s) + r_norm)
    (hlt : r_norm < b_val * 2^s) :
    q_val = a_val / b_val :=
  (norm_euclidean_correct s hmulsub hlt).1

/-- Normalization also recovers the remainder: r_norm / 2^s = a % b. -/
theorem mod_remainder_of_normalized {a_val b_val q_val r_norm : Nat} (s : Nat)
    (hmulsub : a_val * 2^s = q_val * (b_val * 2^s) + r_norm)
    (hlt : r_norm < b_val * 2^s) :
    r_norm / 2^s = a_val % b_val :=
  (norm_euclidean_correct s hmulsub hlt).2

/-- Bridge from val256-level quotient correctness to EvmWord.div.
    If val256(q_limbs) = val256(a_limbs) / val256(b_limbs), then
    fromLimbs(q_limbs) = EvmWord.div(fromLimbs(a_limbs), fromLimbs(b_limbs)). -/
theorem div_of_val256_eq_div
    {a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hq : val256 q0 q1 q2 q3 = val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) :
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3
    q = EvmWord.div a b := by
  intro a b q
  have ha : a.toNat = val256 a0 a1 a2 a3 := (val256_eq_fromLimbs_toNat a0 a1 a2 a3).symm
  have hb : b.toNat = val256 b0 b1 b2 b3 := (val256_eq_fromLimbs_toNat b0 b1 b2 b3).symm
  have hq_val : q.toNat = val256 q0 q1 q2 q3 := (val256_eq_fromLimbs_toNat q0 q1 q2 q3).symm
  have hbnz' : b ≠ 0 := fromLimbs_ne_zero_of_or b0 b1 b2 b3 hbnz
  -- q.toNat = a.toNat / b.toNat
  have hq_nat : q.toNat = a.toNat / b.toNat := by rw [hq_val, ha, hb]; exact hq
  -- (EvmWord.div a b).toNat = a.toNat / b.toNat
  have hdiv : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div; rw [if_neg hbnz']; exact BitVec.toNat_udiv
  exact BitVec.eq_of_toNat_eq (by omega)

end EvmWord

end EvmAsm.Evm64
