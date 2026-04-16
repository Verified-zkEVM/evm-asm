/-
  EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

  Trial quotient overestimate proofs for the n=4 case (b3 ≠ 0, single iteration).

  The max-trial quotient (signExtend12 4095 = 2^64-1) overestimates ⌊val256(a)/val256(b)⌋
  when b3 ≠ 0, because val256(b) ≥ 2^192 forces val256(a)/val256(b) < 2^64.

  These are the key hypotheses needed by `div_correct_n4_no_shift` to bridge
  from the algorithm's mulsub/addback computations to EvmWord.div correctness.
-/

import EvmAsm.Evm64.EvmWordArith.DivAccumulate
import EvmAsm.Evm64.EvmWordArith.Div128Lemmas
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

-- ============================================================================
-- Mulsub borrow bound: c3 ≤ 1 when trial quotient overestimates by at most 1
-- ============================================================================

/-- When the trial quotient overestimates by at most 1 (q ≤ ⌊u/v⌋ + 1),
    the mulsub borrow c3 is at most 1.

    Proof: from mulsubN4_val256_eq, c3 * 2^256 = val256(un) + q*val256(v) - val256(u).
    Since q*val256(v) ≤ val256(u) + val256(v), we get
    c3 * 2^256 ≤ val256(un) + val256(v) < 2 * 2^256, hence c3 ≤ 1. -/
theorem mulsubN4_c3_le_one (q v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1) :
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ 1 := by
  let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  -- From mulsubN4_val256_eq: val256(u) + c3 * 2^256 = val256(un) + q * val256(v)
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  -- Bounds
  have hu_bound := val256_bound u0 u1 u2 u3
  have hun_bound := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have hv_bound := val256_bound v0 v1 v2 v3
  have hv_pos := val256_pos_of_or_ne_zero v0 v1 v2 v3 hbnz
  -- From hq_over: q * val256(v) ≤ (⌊u/v⌋ + 1) * val256(v)
  --            = ⌊u/v⌋ * val256(v) + val256(v) ≤ val256(u) + val256(v)
  have hdiv_mul_le : val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 *
      val256 v0 v1 v2 v3 ≤ val256 u0 u1 u2 u3 :=
    Nat.div_mul_le_self _ _
  have hqv_le : q.toNat * val256 v0 v1 v2 v3 ≤
      val256 u0 u1 u2 u3 + val256 v0 v1 v2 v3 := by
    calc q.toNat * val256 v0 v1 v2 v3
        ≤ (val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1) * val256 v0 v1 v2 v3 :=
          Nat.mul_le_mul_right _ hq_over
      _ = val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 * val256 v0 v1 v2 v3 +
          val256 v0 v1 v2 v3 := by ring
      _ ≤ val256 u0 u1 u2 u3 + val256 v0 v1 v2 v3 :=
          Nat.add_le_add_right hdiv_mul_le _
  -- From hmulsub: c3 * 2^256 = val256(un) + q * val256(v) - val256(u)
  -- So: c3 * 2^256 ≤ val256(un) + val256(v) < 2^256 + 2^256 = 2 * 2^256
  have hc3_bound : c3.toNat * 2^256 < 2 * 2^256 := by
    -- hmulsub: val256(u) + c3 * 2^256 = val256(un) + q * val256(v)
    -- hence c3 * 2^256 = val256(un) + q * val256(v) - val256(u)
    --                   ≤ val256(un) + val256(u) + val256(v) - val256(u)
    --                   = val256(un) + val256(v)
    --                   < 2^256 + 2^256
    nlinarith
  -- Therefore c3 < 2, i.e., c3.toNat ≤ 1
  show c3.toNat ≤ 1
  have h256_pos : (0 : Nat) < 2^256 := by positivity
  have : c3.toNat < 2 := (Nat.mul_lt_mul_right h256_pos).mp hc3_bound
  omega

/-- When c3 ≤ 1, it's either 0 or 1 (as a Word). -/
theorem mulsubN4_c3_eq_zero_or_one (q v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1) :
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0 ∨
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1 := by
  have hle := mulsubN4_c3_le_one q v0 v1 v2 v3 u0 u1 u2 u3 hbnz hq_over
  rcases Nat.eq_zero_or_pos (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat with h | h
  · left; bv_omega
  · right; bv_omega

/-- When c3 ≤ 1 and c3 ≠ 0, then c3 = 1. This is the key link between
    the algorithm's borrow check (c3 ≠ 0) and the addback hypothesis (c3 = 1). -/
theorem mulsubN4_c3_ne_zero_imp_one (q v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1)
    (hc3_nz : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 ≠ 0) :
    (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1 :=
  (mulsubN4_c3_eq_zero_or_one q v0 v1 v2 v3 u0 u1 u2 u3 hbnz hq_over |>.resolve_left hc3_nz)

-- ============================================================================
-- Mulsub borrow bound for n ≤ 3 (v3 = 0): c3 ≤ 1 unconditionally
-- ============================================================================

-- When v3 = 0, val256(v) < 2^192, so q * val256(v) < 2^64 * 2^192 = 2^256
-- for any 64-bit q. This gives c3 ≤ 1 without any overestimate hypothesis.

/-- When the top divisor limb v3 = 0, the mulsub borrow c3 ≤ 1 for ANY
    64-bit trial quotient q, without needing any overestimate bound.

    Proof: from `mulsubN4_val256_eq`, c3 * 2^256 = val256(un) + q * val256(v) - val256(u).
    Since val256(un) < 2^256 and val256(v) < 2^192 (because v3 = 0):
    q * val256(v) ≤ (2^64-1) * (2^192-1) < 2^256.
    So c3 * 2^256 < 2^256 + 2^256 = 2 * 2^256, hence c3 ≤ 1. -/
theorem mulsubN4_c3_le_one_v3_zero (q v0 v1 v2 u0 u1 u2 u3 : Word) :
    (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2.toNat ≤ 1 := by
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 0 u0 u1 u2 u3
  simp only [] at hmulsub
  let ms := mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  have hun_bound := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have hv_bound := val256_lt_pow192 v0 v1 v2
  have hq_bound := q.isLt
  have hqv_bound : q.toNat * val256 v0 v1 v2 0 < 2 ^ 256 := by nlinarith
  have hc3_bound : c3.toNat * 2 ^ 256 < 2 * 2 ^ 256 := by
    show ms.2.2.2.2.toNat * 2 ^ 256 < 2 * 2 ^ 256; nlinarith
  show c3.toNat ≤ 1
  have h256_pos : (0 : Nat) < 2 ^ 256 := by positivity
  have : c3.toNat < 2 := (Nat.mul_lt_mul_right h256_pos).mp hc3_bound
  omega

/-- When c3 ≠ 0 and v3 = 0, the borrow is exactly 1.
    Immediate from `mulsubN4_c3_le_one_v3_zero`. -/
theorem mulsubN4_c3_eq_one_v3_zero (q v0 v1 v2 u0 u1 u2 u3 : Word)
    (hc3_nz : (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 ≠ 0) :
    (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
  have h := mulsubN4_c3_le_one_v3_zero q v0 v1 v2 u0 u1 u2 u3
  have hc3_pos : 0 < (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2.toNat := by
    exact Nat.pos_of_ne_zero (by intro h0; exact hc3_nz (BitVec.eq_of_toNat_eq h0))
  have h1 : (1 : Word).toNat = 1 := by decide
  exact BitVec.eq_of_toNat_eq (by omega)

-- ============================================================================
-- Double addback: second carry is 1 when first carry was 0
-- ============================================================================

-- When the trial quotient overestimates by exactly 2 (detected by c3=1 and
-- first addback carry=0), a second addback produces carry=1, giving a clean
-- Euclidean equation: val256(u) = (q-2) * val256(v) + val256(ab').

/-- Second addback carry is 1 when the first was 0.

    From c3=1: val256(u) + 2^256 = val256(un) + q*val256(v)
    From carry1=0: val256(un) + val256(v) = val256(ab1)  (no overflow)
    Second addback: val256(ab1) + val256(v) = val256(ab') + carry2*2^256
    Combining: val256(u) + 2^256 = val256(ab') + carry2*2^256 + (q-2)*val256(v)
    Since q ≤ ⌊u/v⌋ + 2: (q-2)*val256(v) ≤ val256(u), hence carry2 = 1. -/
theorem addbackN4_second_carry_one (q v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hc3_one : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hcarry_zero : (addbackN4_carry
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3) = 0) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
    (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3).toNat = 1 := by
  intro ms ab
  -- From mulsubN4_val256_eq with c3 = 1
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  rw [show ms.2.2.2.2 = (1 : Word) from hc3_one] at hmulsub
  have h1w : (1 : Word).toNat = 1 := by decide
  rw [h1w] at hmulsub
  -- First addback: val256(un) + val256(v) = val256(ab1) + carry1 * 2^256
  have hab1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab1
  have hc1_val : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3).toNat = 0 := by
    rw [hcarry_zero]; decide
  rw [hc1_val] at hab1
  -- Second addback: val256(ab1) + val256(v) = val256(ab') + carry2 * 2^256
  have hab' := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab'
  -- Bounds
  have hv_pos := val256_pos_of_or_ne_zero v0 v1 v2 v3 hbnz
  have hun_bound := val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have hab1_bound := val256_bound ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
  have hab'_result_bound := val256_bound
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.1
    (addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3).2.2.2.1
  have hdiv_mul_le : val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 *
      val256 v0 v1 v2 v3 ≤ val256 u0 u1 u2 u3 := Nat.div_mul_le_self _ _
  -- q ≥ 2: from c3=1 and carry1=0, q*v > u+v, so q ≥ 2
  have hqv_gt_u : q.toNat * val256 v0 v1 v2 v3 > val256 u0 u1 u2 u3 := by nlinarith
  have hun_v_lt : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 +
      val256 v0 v1 v2 v3 < 2 ^ 256 := by nlinarith
  have hu_v_lt_qv : val256 u0 u1 u2 u3 + val256 v0 v1 v2 v3 <
      q.toNat * val256 v0 v1 v2 v3 := by nlinarith
  have hq_ge_2 : q.toNat ≥ 2 := by
    by_contra h; push Not at h
    have : q.toNat * val256 v0 v1 v2 v3 ≤ 1 * val256 v0 v1 v2 v3 :=
      Nat.mul_le_mul_right _ (by omega)
    linarith
  have hqm2_le : (q.toNat - 2) * val256 v0 v1 v2 v3 ≤ val256 u0 u1 u2 u3 := by
    calc (q.toNat - 2) * val256 v0 v1 v2 v3
        ≤ (val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3) * val256 v0 v1 v2 v3 := by
          apply Nat.mul_le_mul_right; omega
      _ ≤ val256 u0 u1 u2 u3 := hdiv_mul_le
  -- val256(un) + 2*val256(v) ≥ 2^256
  have h_ge : val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 + 2 * val256 v0 v1 v2 v3 ≥ 2 ^ 256 := by
    have hq_split : q.toNat * val256 v0 v1 v2 v3 =
        (q.toNat - 2) * val256 v0 v1 v2 v3 + 2 * val256 v0 v1 v2 v3 := by
      have hq2 : q.toNat = (q.toNat - 2) + 2 := by omega
      nlinarith
    nlinarith
  -- val256(ab1) + val256(v) ≥ 2^256
  have h_ab1_v_ge : val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 +
      val256 v0 v1 v2 v3 ≥ 2 ^ 256 := by nlinarith
  -- carry2 = 1: from hab' and h_ab1_v_ge
  -- val256(ab'_result) + carry2 * 2^256 = val256(ab) + val256(v) ≥ 2^256
  -- So carry2 * 2^256 ≥ 2^256 - val256(ab'_result) ≥ 1, hence carry2 ≥ 1
  -- Also val256(ab) + val256(v) < 2 * 2^256, so carry2 < 2
  set carry2 := (addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3).toNat
  -- Upper bound: carry2 * 2^256 < 2 * 2^256
  have hc2_lt : carry2 * 2 ^ 256 < 2 * 2 ^ 256 := by
    have : val256 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 + val256 v0 v1 v2 v3 < 2 * 2 ^ 256 := by
      linarith
    linarith
  -- Lower bound: carry2 ≥ 1
  -- If carry2 = 0 then hab' gives val256(ab)+val256(v) = val256(ab'_result) < 2^256,
  -- contradicting h_ab1_v_ge.
  have hc2_ge : carry2 ≥ 1 := by
    by_contra h; push Not at h
    have hc2_zero : carry2 = 0 := by omega
    rw [hc2_zero] at hab'
    -- hab': val256(ab) + val256(v) = val256(ab'_result) + 0 * 2^256
    -- = val256(ab'_result) < 2^256, contradicting ≥ 2^256
    linarith
  have h256_pos : (0 : Nat) < 2 ^ 256 := by positivity
  have : carry2 < 2 := (Nat.mul_lt_mul_right h256_pos).mp hc2_lt
  omega

/-- Combined Euclidean equation for the double-addback case:
    val256(u) = (q.toNat - 2) * val256(v) + val256(ab'_result). -/
theorem mulsub_double_addback_val256_combined (q v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hc3_one : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1)
    (hcarry_zero : (addbackN4_carry
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
      v0 v1 v2 v3) = 0)
    (hq_ge_2 : q.toNat ≥ 2) :
    let ms := mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3
    val256 u0 u1 u2 u3 = (q.toNat - 2) * val256 v0 v1 v2 v3 +
      val256 ab'.1 ab'.2.1 ab'.2.2.1 ab'.2.2.2.1 := by
  intro ms ab ab'
  -- Mulsub equation with c3 = 1
  have hmulsub := mulsubN4_val256_eq q v0 v1 v2 v3 u0 u1 u2 u3
  simp only [] at hmulsub
  rw [show ms.2.2.2.2 = (1 : Word) from hc3_one] at hmulsub
  have h1w : (1 : Word).toNat = 1 := by decide
  rw [h1w] at hmulsub
  -- First addback with carry = 0
  have hab1 := addbackN4_val256_eq ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab1
  have hc1_val : (addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3).toNat = 0 := by
    rw [hcarry_zero]; decide
  rw [hc1_val] at hab1
  -- Second addback with carry = 1
  have hcarry2 := addbackN4_second_carry_one q v0 v1 v2 v3 u0 u1 u2 u3
    hbnz hq_over hc3_one hcarry_zero
  simp only [] at hcarry2
  have hab'_eq := addbackN4_val256_eq ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 0 v0 v1 v2 v3
  simp only [] at hab'_eq
  rw [hcarry2] at hab'_eq
  -- Combine: val256(u) + 2^256 = val256(un) + q*v (mulsub, c3=1)
  -- val256(un) + val256(v) = val256(ab1) (addback, carry=0)
  -- val256(ab1) + val256(v) = val256(ab') + 2^256 (addback2, carry=1)
  -- So: val256(u) = (q-2)*val256(v) + val256(ab')
  suffices h : (q.toNat - 2) * val256 v0 v1 v2 v3 + 2 * val256 v0 v1 v2 v3 =
      q.toNat * val256 v0 v1 v2 v3 by linarith
  have : q.toNat = (q.toNat - 2) + 2 := by omega
  nlinarith

end EvmAsm.Evm64
