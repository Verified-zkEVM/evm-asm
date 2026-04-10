/-
  EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

  Trial quotient overestimate proofs for the n=4 case (b3 ≠ 0, single iteration).

  The max-trial quotient (signExtend12 4095 = 2^64-1) overestimates ⌊val256(a)/val256(b)⌋
  when b3 ≠ 0, because val256(b) ≥ 2^192 forces val256(a)/val256(b) < 2^64.

  These are the key hypotheses needed by `div_correct_n4_no_shift` to bridge
  from the algorithm's mulsub/addback computations to EvmWord.div correctness.
-/

import EvmAsm.Evm64.EvmWordArith.DivAccumulate
import EvmAsm.Evm64.DivMod.LoopSemantic

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

-- ============================================================================
-- Max trial overestimate: q_hat = 2^64 - 1 ≥ ⌊val256(a)/val256(b)⌋
-- ============================================================================

/-- When b3 ≠ 0, val256(a)/val256(b) ≤ 2^64 - 1.
    This is because val256(b) ≥ 2^192 (from b3 ≠ 0) and val256(a) < 2^256. -/
theorem val256_div_lt_pow64 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (hb3nz : b3 ≠ 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ 2^64 - 1 := by
  have hb_ge := val256_ge_pow192_of_limb3 b0 b1 b2 b3 hb3nz
  have ha_lt := val256_bound a0 a1 a2 a3
  -- val256(a) < 2^256 = 2^64 * 2^192 ≤ 2^64 * val256(b)
  -- So val256(a) / val256(b) < 2^64
  have hb_pos : 0 < val256 b0 b1 b2 b3 := by omega
  calc val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3
      ≤ (2^256 - 1) / val256 b0 b1 b2 b3 := Nat.div_le_div_right (by omega)
    _ ≤ (2^256 - 1) / 2^192 := Nat.div_le_div_left hb_ge (by omega)
    _ = 2^64 - 1 := by norm_num

/-- signExtend12 4095 as Word has toNat = 2^64 - 1. -/
theorem signExtend12_4095_toNat : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by
  decide

/-- Max trial quotient overestimate for n=4: when b3 ≠ 0,
    ⌊val256(a)/val256(b)⌋ ≤ (signExtend12 4095).toNat.
    This is the `hge` hypothesis needed by `div_correct_n4_no_shift`. -/
theorem max_trial_overestimate_n4 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (hb3nz : b3 ≠ 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ (signExtend12 (4095 : BitVec 12) : Word).toNat := by
  rw [signExtend12_4095_toNat]
  exact val256_div_lt_pow64 a0 a1 a2 a3 b0 b1 b2 b3 hb3nz

-- ============================================================================
-- Skip path: mulsub c3=0 → Euclidean equation → EvmWord.div correctness
-- ============================================================================

/-- Skip path (c3 = 0, max trial) at n=4: when mulsubN4 produces no borrow,
    the max trial quotient (2^64-1) equals ⌊val256(a)/val256(b)⌋
    and fromLimbs [q_hat, 0, 0, 0] = EvmWord.div a b. -/
theorem n4_max_skip_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hc3_zero : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 0) :
    let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => (signExtend12 4095 : Word) | 1 => 0 | 2 => 0 | 3 => 0
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => ms.1 | 1 => ms.2.1 | 2 => ms.2.2.1 | 3 => ms.2.2.2.1
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro ms a b q r
  -- Derive hbnz from hb3nz
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  -- From mulsubN4_val256_eq: val256(u) + c3 * 2^256 = val256(un) + q * val256(v)
  have hmulsub_raw := mulsubN4_val256_eq (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
  simp only [] at hmulsub_raw
  -- c3 = 0, so val256(u) = val256(un) + q * val256(v)
  rw [show ms.2.2.2.2 = (0 : Word) from hc3_zero] at hmulsub_raw
  have : (0 : Word).toNat = 0 := by decide
  rw [this, Nat.zero_mul, Nat.add_zero] at hmulsub_raw
  -- Rearrange: val256 a = q.toNat * val256 b + val256 r
  have hmulsub : val256 a0 a1 a2 a3 =
      (signExtend12 (4095 : BitVec 12) : Word).toNat * val256 b0 b1 b2 b3 +
      val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 := by linarith
  -- Overestimate: val256(a)/val256(b) ≤ q_hat.toNat
  have hge := max_trial_overestimate_n4 a0 a1 a2 a3 b0 b1 b2 b3 hb3nz
  exact div_correct_n4_no_shift hbnz hmulsub hge

-- ============================================================================
-- Addback combined equation: mulsub(c3=1) + addback(carry=1) → Euclidean
-- ============================================================================

/-- When mulsub borrow c3 = 1 and addback carry = 1, the 2^256 terms cancel,
    giving a clean Euclidean equation: val256(u) = (q-1) * val256(v) + val256(aun).
    This is the combined equation needed by mulsub_addback_correct. -/
theorem mulsub_addback_val256_combined (q v0 v1 v2 v3 u0 u1 u2 u3 u4_new : Word)
    (hc3_one : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hcarry_one : addbackN4_carry
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3 = 1)
    (hq_pos : q.toNat ≥ 1) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new v0 v1 v2 v3
    val256 u0 u1 u2 u3 = (q.toNat - 1) * val256 v0 v1 v2 v3 +
      val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by
  intro ms ab
  -- From mulsubN4_val256_eq: val256(u) + c3 * 2^256 = val256(un) + q * val256(v)
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  -- From addbackN4_val256_eq: val256(un) + val256(v) = val256(aun) + carry * 2^256
  have haddback := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new v0 v1 v2 v3
  simp only [] at haddback
  -- Substitute c3 = 1 and carry = 1
  rw [show ms.2.2.2.2 = (1 : Word) from hc3_one] at hmulsub
  rw [hcarry_one] at haddback
  have h1 : (1 : Word).toNat = 1 := by decide
  rw [h1] at hmulsub haddback
  -- hmulsub: val256 u + 1 * 2^256 = val256 un + q * val256 v
  -- haddback: val256 un + val256 v = val256 aun + 1 * 2^256
  -- Add both: cancel val256 un and 2^256
  -- hmulsub: val256(u) + 2^256 = val256(un) + q * val256(v)
  -- haddback: val256(un) + val256(v) = val256(aun) + 2^256
  -- So: val256(u) + val256(v) = q * val256(v) + val256(aun)
  have hsum : val256 u0 u1 u2 u3 + val256 v0 v1 v2 v3 =
      q.toNat * val256 v0 v1 v2 v3 + val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 := by linarith
  -- From A + V = Q*V + R with Q ≥ 1: A = (Q-1)*V + R
  -- Rewrite as: A = Q*V + R - V = Q*V - V + R = (Q-1)*V + R
  -- Use: (Q-1)*V + V = Q*V (from hq_pos)
  -- So: A + V = (Q-1)*V + V + R, hence A = (Q-1)*V + R
  suffices h : (q.toNat - 1) * val256 v0 v1 v2 v3 + val256 v0 v1 v2 v3 =
      q.toNat * val256 v0 v1 v2 v3 by linarith
  have hq1 : q.toNat = q.toNat - 1 + 1 := by omega
  nlinarith

-- ============================================================================
-- Addback path correctness for max trial at n=4
-- ============================================================================

/-- Addback path (c3 = 1, max trial) at n=4: when mulsubN4 underflows with
    borrow 1 and addback produces carry 1, the corrected quotient (q_hat - 1)
    equals ⌊val256(a)/val256(b)⌋. -/
theorem n4_max_addback_correct (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hc3_one : (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.2 = 1)
    (hcarry_one : addbackN4_carry
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.1
      (mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3).2.2.2.1
      b0 b1 b2 b3 = 1) :
    let ms := mulsubN4 (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - ms.2.2.2.2) b0 b1 b2 b3
    let q_hat' := signExtend12 (4095 : BitVec 12) + signExtend12 (4095 : BitVec 12)
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => q_hat' | 1 => (0 : Word) | 2 => (0 : Word) | 3 => (0 : Word)
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => ab.1 | 1 => ab.2.1 | 2 => ab.2.2.1 | 3 => ab.2.2.2.1
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro ms ab q_hat' a b q r
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h; exact hb3nz (BitVec.or_eq_zero_iff.mp h).2
  have hq_hat_toNat : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
  have hq_hat'_toNat : q_hat'.toNat = 2^64 - 2 := by decide
  -- Combined Euclidean equation from mulsub(c3=1) + addback(carry=1)
  -- Pass u4_new = 0 - ms.2.2.2.2 so addbackN4 matches ab's definition
  have hcombined := mulsub_addback_val256_combined
    (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3 ((0 : Word) - ms.2.2.2.2)
    hc3_one hcarry_one (by rw [hq_hat_toNat]; omega)
  simp only [] at hcombined
  -- hcombined now mentions addbackN4 ... (0 - ms.2.2.2.2) ... which matches ab
  -- Rewrite (signExtend12 4095).toNat - 1 to q_hat'.toNat
  rw [show (signExtend12 (4095 : BitVec 12) : Word).toNat - 1 = q_hat'.toNat from by
    rw [hq_hat_toNat, hq_hat'_toNat]; omega] at hcombined
  -- Normalize hcombined to use let-bound ab
  change val256 a0 a1 a2 a3 = q_hat'.toNat * val256 b0 b1 b2 b3 +
    val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 at hcombined
  -- Strict overestimate: c3 ≥ 1 implies q_hat * v > u, so u/v < q_hat, hence u/v ≤ q_hat'
  have hge : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ q_hat'.toNat := by
    rw [hq_hat'_toNat]
    -- From mulsubN4_val256_eq with c3 = 1: q_hat * val(v) ≥ val(u) + 1
    have hmulsub_raw := mulsubN4_val256_eq (signExtend12 4095) b0 b1 b2 b3 a0 a1 a2 a3
    simp only [] at hmulsub_raw
    rw [show ms.2.2.2.2 = (1 : Word) from hc3_one] at hmulsub_raw
    have h1 : (1 : Word).toNat = 1 := by decide
    rw [h1] at hmulsub_raw
    -- hmulsub_raw: val256 u + 1 * 2^256 = val256 un + q_hat * val256 v
    -- So q_hat * val256 v ≥ val256 u + 1 (since 2^256 > val256 un)
    have hv_bound := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    have hv_pos := val256_pos_of_or_ne_zero b0 b1 b2 b3 hbnz
    have hq_mul_gt : (signExtend12 (4095 : BitVec 12) : Word).toNat * val256 b0 b1 b2 b3 >
        val256 a0 a1 a2 a3 := by nlinarith
    rw [hq_hat_toNat] at hq_mul_gt
    -- From q * v > u and v > 0: u / v < q, hence u / v ≤ q - 1
    -- val256(a) < (2^64-1) * val256(b) implies val256(a) / val256(b) < 2^64-1
    have hdiv_lt : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 < 2^64 - 1 :=
      Nat.div_lt_iff_lt_mul hv_pos |>.mpr hq_mul_gt
    omega
  exact div_correct_n4_no_shift hbnz hcombined hge

-- Note: The remaining missing pieces for full semantic bridge:
-- 1. Mulsub borrow bound (c3 ≤ 1): needed to derive hc3_one from hc3_nonzero
-- 2. Call path trial quotient overestimate (Knuth's Theorem B for div128)

end EvmAsm.Evm64
