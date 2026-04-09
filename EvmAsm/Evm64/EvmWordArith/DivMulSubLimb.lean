/-
  EvmAsm.Evm64.EvmWordArith.DivMulSubLimb

  Per-limb multiply-subtract correctness at the Nat level.
  These lemmas connect the register-level operations (MUL, MULHU, ADD, SLTU, SUB)
  in each mulsub_limb iteration to the Nat-level carry equations required by
  `mulsub_chain_nat` and `mulsub_chain_no_underflow`.

  Key results:
  - mulhu_toNat_le: MULHU product bounded by 2^64 - 2
  - mulsub_limb_nat_eq: per-limb carry equation at the Nat level
  - mulsub_limb_carry_le: carry bounded (≤ 2^64)
  - mulsub_limb_carry_lt_of_sum_le_one: carry < 2^64 when borrows don't both fire
  - mulsub_carry_word_eq: Word-level carry equals Nat-level carry when < 2^64
  - mulsub_4limb_euclidean_div: end-to-end from 4-limb chain to EvmWord.div/mod
-/

import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- MULHU upper bound
-- ============================================================================

/-- The high 64 bits of a 64×64 product is at most 2^64 - 2.
    Max product: (2^64-1)² = 2^128 - 2·2^64 + 1, high half = 2^64 - 2. -/
theorem mulhu_toNat_le (a b : Word) : (rv64_mulhu a b).toNat ≤ 2^64 - 2 := by
  rw [rv64_mulhu_toNat]
  have ha := a.isLt; have hb := b.isLt
  have h1 : a.toNat ≤ 2^64 - 1 := by omega
  have h2 : b.toNat ≤ 2^64 - 1 := by omega
  have h3 : a.toNat * b.toNat ≤ (2^64 - 1) * (2^64 - 1) := Nat.mul_le_mul h1 h2
  suffices (2^64 - 1) * (2^64 - 1) / 2^64 = 2^64 - 2 by
    exact Nat.le_trans (Nat.div_le_div_right h3) (Nat.le_of_eq this)
  norm_num

-- ============================================================================
-- Per-limb multiply-subtract: Nat-level carry equation
-- ============================================================================

/-- Per-limb multiply-subtract Nat-level equation.

    The mulsub_limb operation computes:
    - prod_lo = MUL(q, v_i), prod_hi = MULHU(q, v_i)
    - full_sub = ADD(prod_lo, carry_in), borrow_add = SLTU(full_sub, carry_in)
    - u_new = SUB(u_i, full_sub), borrow_sub = SLTU(u_i, full_sub)

    At the Nat level, this produces:
      u_i + C * 2^64 = u_new + q * v_i + carry_in
    where C = borrow_add + prod_hi + borrow_sub (Nat sum).

    This is exactly the per-limb equation needed by `mulsub_chain_nat`. -/
theorem mulsub_limb_nat_eq (q v_i u_i carry_in : Word) :
    let prod_lo := q * v_i
    let prod_hi := rv64_mulhu q v_i
    let full_sub := prod_lo + carry_in
    let borrow_add := if BitVec.ult full_sub carry_in then (1 : Word) else 0
    let u_new := u_i - full_sub
    let borrow_sub := if BitVec.ult u_i full_sub then (1 : Word) else 0
    u_i.toNat + (borrow_add.toNat + prod_hi.toNat + borrow_sub.toNat) * 2^64 =
      u_new.toNat + q.toNat * v_i.toNat + carry_in.toNat := by
  intro prod_lo prod_hi full_sub borrow_add u_new borrow_sub
  -- Full product: q * v_i = prod_hi * 2^64 + prod_lo
  have h_prod := partial_product_decompose q v_i
  -- full_sub = (prod_lo + carry_in) mod 2^64
  have h_fs : full_sub.toNat = (prod_lo.toNat + carry_in.toNat) % 2^64 :=
    BitVec.toNat_add prod_lo carry_in
  -- borrow_add = (prod_lo + carry_in) / 2^64 (is 0 or 1)
  have h_ba : borrow_add.toNat = (prod_lo.toNat + carry_in.toNat) / 2^64 := by
    have hpl := prod_lo.isLt; have hci := carry_in.isLt
    by_cases hov : prod_lo.toNat + carry_in.toNat < 2^64
    · -- no overflow
      have hge : full_sub.toNat ≥ carry_in.toNat := by rw [h_fs, Nat.mod_eq_of_lt hov]; omega
      show (if BitVec.ult full_sub carry_in then (1 : Word) else 0).toNat = _
      have : ¬(full_sub.toNat < carry_in.toNat) := by omega
      simp [BitVec.ult, this]
      show 0 = _; omega
    · -- overflow
      push Not at hov
      have hlt : full_sub.toNat < carry_in.toNat := by rw [h_fs]; omega
      show (if BitVec.ult full_sub carry_in then (1 : Word) else 0).toNat = _
      simp [BitVec.ult, hlt]
      show 1 = _
      have : prod_lo.toNat + carry_in.toNat < 2 * 2^64 := by omega
      omega
  -- borrow_sub = if u_i < full_sub then 1 else 0
  have h_bs : borrow_sub.toNat = if u_i.toNat < full_sub.toNat then 1 else 0 := by
    show (if BitVec.ult u_i full_sub then (1 : Word) else 0).toNat = _
    by_cases h : u_i.toNat < full_sub.toNat
    · simp [BitVec.ult, h]
    · simp [BitVec.ult, show ¬(u_i.toNat < full_sub.toNat) from h]
  -- u_new via sub
  have hu := u_i.isLt; have hfs := full_sub.isLt
  have h_un : u_new.toNat = if full_sub.toNat ≤ u_i.toNat
    then u_i.toNat - full_sub.toNat
    else u_i.toNat + 2^64 - full_sub.toNat := by
    show (u_i - full_sub).toNat = _; rw [BitVec.toNat_sub]
    by_cases h : full_sub.toNat ≤ u_i.toNat
    · simp [h]; omega
    · push Not at h; simp [show ¬(full_sub.toNat ≤ u_i.toNat) from by omega]; omega
  -- div_add_mod for the add carry
  have hdm := Nat.div_add_mod (prod_lo.toNat + carry_in.toNat) (2^64)
  -- Combine: normalize 2^64 to the literal everywhere
  have hB : (2:Nat)^64 = 18446744073709551616 := by norm_num
  -- Use B as shorthand for 2^64 literal
  set B := (18446744073709551616 : Nat) with hBdef
  rw [show (2:Nat)^64 = B from by omega] at h_ba h_fs h_prod hdm hu hfs h_un ⊢
  -- Key: from hdm, (prod_lo + carry_in) / B * B + full_sub = prod_lo + carry_in
  have hkey : (prod_lo.toNat + carry_in.toNat) / B * B =
      prod_lo.toNat + carry_in.toNat - full_sub.toNat := by
    rw [h_fs]; omega
  -- Key: prod_hi * B + prod_lo = q * v_i
  -- (prod_hi and prod_lo are let-defs for rv64_mulhu and MUL, so this is h_prod rewritten)
  have h_prod' : prod_hi.toNat * B + prod_lo.toNat = q.toNat * v_i.toNat := by
    show (rv64_mulhu q v_i).toNat * B + (q * v_i).toNat = _; linarith
  -- Expand the compound carry multiplication
  have hfs_le : full_sub.toNat ≤ prod_lo.toNat + carry_in.toNat := by
    rw [h_fs]; exact Nat.mod_le _ _
  have hpl_le : prod_lo.toNat ≤ prod_hi.toNat * B + prod_lo.toNat := Nat.le_add_left _ _
  rw [h_ba, h_bs, h_un]
  -- Eliminate the nonlinear q*v_i term by replacing with prod_hi*B + prod_lo (linear!)
  rw [show q.toNat * v_i.toNat = prod_hi.toNat * B + prod_lo.toNat from h_prod'.symm]
  -- Now everything is linear in div, prod_hi, B, prod_lo, carry_in, full_sub, u_i
  by_cases hcmp : full_sub.toNat ≤ u_i.toNat
  · simp only [hcmp, show ¬(u_i.toNat < full_sub.toNat) from by omega, ite_true, ite_false]
    have h1 := Nat.add_mul ((prod_lo.toNat + carry_in.toNat) / B) prod_hi.toNat B
    omega
  · push Not at hcmp
    simp only [show ¬(full_sub.toNat ≤ u_i.toNat) from by omega,
      show u_i.toNat < full_sub.toNat from by omega, ite_false, ite_true]
    have h1 := Nat.add_mul ((prod_lo.toNat + carry_in.toNat) / B) prod_hi.toNat B
    have h2 := Nat.add_mul ((prod_lo.toNat + carry_in.toNat) / B + prod_hi.toNat) 1 B
    omega

-- ============================================================================
-- Carry bound
-- ============================================================================

/-- The Nat-level carry from one mulsub_limb step is at most 2^64.
    borrow_add ≤ 1, prod_hi ≤ 2^64 - 2, borrow_sub ≤ 1. -/
theorem mulsub_limb_carry_le (q v_i : Word)
    (borrow_add_nat borrow_sub_nat : Nat)
    (h_ba : borrow_add_nat ≤ 1) (h_bs : borrow_sub_nat ≤ 1) :
    borrow_add_nat + (rv64_mulhu q v_i).toNat + borrow_sub_nat ≤ 2^64 := by
  have := mulhu_toNat_le q v_i; omega

/-- When carry_in + prod_lo doesn't overflow, the add-borrow is 0. -/
theorem borrow_add_eq_zero_of_no_overflow (q v_i carry_in : Word)
    (h : (q * v_i).toNat + carry_in.toNat < 2^64) :
    (if BitVec.ult (q * v_i + carry_in) carry_in then (1 : Word) else 0) = 0 := by
  have hge : (q * v_i + carry_in).toNat ≥ carry_in.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [BitVec.ult, show ¬((q * v_i + carry_in).toNat < carry_in.toNat) from by omega,
    decide_false]
  decide

-- ============================================================================
-- Carry strictly less than 2^64 (for Word-level tracking)
-- ============================================================================

/-- The per-limb carry is strictly < 2^64 whenever
    borrow_add + borrow_sub ≤ 1 (not both overflow and underflow).
    This ensures the carry fits in a Word. -/
theorem mulsub_limb_carry_lt_of_sum_le_one (q v_i : Word)
    (borrow_add_nat borrow_sub_nat : Nat)
    (h_sum : borrow_add_nat + borrow_sub_nat ≤ 1) :
    borrow_add_nat + (rv64_mulhu q v_i).toNat + borrow_sub_nat < 2^64 := by
  have := mulhu_toNat_le q v_i; omega

/-- When the carry is < 2^64, the Word-level carry equals the Nat-level carry.
    This ensures the register-level carry_out correctly tracks the Nat-level
    carry for use as the next limb's carry_in. -/
theorem mulsub_carry_word_eq (borrow_add prod_hi borrow_sub : Word)
    (h : borrow_add.toNat + prod_hi.toNat + borrow_sub.toNat < 2^64) :
    ((borrow_add + prod_hi) + borrow_sub).toNat =
    borrow_add.toNat + prod_hi.toNat + borrow_sub.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add]
  have h1 : borrow_add.toNat + prod_hi.toNat < 2^64 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

-- ============================================================================
-- Composed: 4-limb multiply-subtract from per-limb equations
-- ============================================================================

/-- Composing 4 per-limb Nat-level equations gives the full val256 equation
    via `mulsub_chain_nat`. The carries cb0..cb3 telescope, leaving only cb3:
      val256 u + cb3 * 2^256 = val256 r + q * val256 v -/
theorem mulsub_4limb_val256 (q_nat : Nat)
    (u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 : Word)
    (cb0 cb1 cb2 cb3 : Nat)
    (h0 : u0.toNat + cb0 * 2^64 = r0.toNat + q_nat * v0.toNat)
    (h1 : u1.toNat + cb1 * 2^64 = r1.toNat + q_nat * v1.toNat + cb0)
    (h2 : u2.toNat + cb2 * 2^64 = r2.toNat + q_nat * v2.toNat + cb1)
    (h3 : u3.toNat + cb3 * 2^64 = r3.toNat + q_nat * v3.toNat + cb2) :
    val256 u0 u1 u2 u3 + cb3 * 2^256 =
    val256 r0 r1 r2 r3 + q_nat * val256 v0 v1 v2 v3 :=
  mulsub_chain_nat q_nat u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 cb0 cb1 cb2 cb3
    h0 h1 h2 h3

/-- When the final carry cb3 = 0 (no underflow) and remainder < divisor,
    the multiply-subtract proves the Euclidean property, giving
    q = EvmWord.div and r = EvmWord.mod.

    This handles the single-digit quotient case (n=4 in Knuth's Algorithm D). -/
theorem mulsub_4limb_euclidean_div (q_nat : Nat)
    (u0 u1 u2 u3 v0 v1 v2 v3 r0 r1 r2 r3 : Word)
    (cb0 cb1 cb2 : Nat)
    (hq_bound : q_nat < 2^64)
    (h0 : u0.toNat + cb0 * 2^64 = r0.toNat + q_nat * v0.toNat)
    (h1 : u1.toNat + cb1 * 2^64 = r1.toNat + q_nat * v1.toNat + cb0)
    (h2 : u2.toNat + cb2 * 2^64 = r2.toNat + q_nat * v2.toNat + cb1)
    (h3 : u3.toNat = r3.toNat + q_nat * v3.toNat + cb2)
    (h_rem : val256 r0 r1 r2 r3 < val256 v0 v1 v2 v3)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0) :
    let a := fromLimbs fun i : Fin 4 =>
      match i with | 0 => u0 | 1 => u1 | 2 => u2 | 3 => u3
    let b := fromLimbs fun i : Fin 4 =>
      match i with | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3
    let q := fromLimbs fun i : Fin 4 =>
      match i with | 0 => BitVec.ofNat 64 q_nat | _ => 0
    let r := fromLimbs fun i : Fin 4 =>
      match i with | 0 => r0 | 1 => r1 | 2 => r2 | 3 => r3
    q = EvmWord.div a b ∧ r = EvmWord.mod a b := by
  intro a b q r
  have h_chain := mulsub_chain_no_underflow q_nat u0 u1 u2 u3 v0 v1 v2 v3
    r0 r1 r2 r3 cb0 cb1 cb2 h0 h1 h2 h3
  -- Connect fromLimbs.toNat to val256
  have ha : a.toNat = val256 u0 u1 u2 u3 := by
    show (fromLimbs _).toNat = _; rw [fromLimbs_toNat]; dsimp only []; unfold val256; norm_num
  have hb : b.toNat = val256 v0 v1 v2 v3 := by
    show (fromLimbs _).toNat = _; rw [fromLimbs_toNat]; dsimp only []; unfold val256; norm_num
  have hq : q.toNat = q_nat := by
    show (fromLimbs _).toNat = q_nat; rw [fromLimbs_toNat, show (0 : Word).toNat = 0 from rfl]
    simp only [BitVec.toNat_ofNat]; omega
  have hr : r.toNat = val256 r0 r1 r2 r3 := by
    show (fromLimbs _).toNat = _; rw [fromLimbs_toNat]; dsimp only []; unfold val256; norm_num
  have h_eq : a.toNat = b.toNat * q.toNat + r.toNat := by
    rw [ha, hb, hq, hr]; linarith
  have h_lt : r.toNat < b.toNat := by rw [hr, hb]; exact h_rem
  have h_bnz : b ≠ 0 := fromLimbs_ne_zero_of_or v0 v1 v2 v3 hbnz
  exact div_from_mulsub a b q r h_bnz h_eq h_lt

end EvmWord

end EvmAsm.Evm64
