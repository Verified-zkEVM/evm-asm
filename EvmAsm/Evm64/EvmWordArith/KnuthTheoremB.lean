/-
  EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

  Toward Knuth's TAOCP Vol 2 §4.3.1 Theorem B for the n=4 max-trial
  call path: `div128Quot u_top u3 b3'` overestimates the true quotient
  `⌊val256(a) / val256(b)⌋` by at most 2.

  This is the major remaining math gap for call-trial DIV/MOD stack
  specs (the real shift > 0 runtime path, after max-trial under
  `hshift_nz` was shown vacuous in `MaxTrialVacuity.lean`).

  See `memory/project_knuth_theorem_b_plan.md` for the 6-PR breakdown.

  Currently contains:
  - `val256_div_scale_invariant` (Step 0).
  - `rv64_divu_toNat` (Step 1a — RV64 divu → Nat div bridge).
  - `val256_ge_pow255_of_normalized` — normalized divisor ≥ 2^255.
  - `val256_split_hi2` — split val256 into (hi2-limb * 2^128 + lo2-limb) form.
  - `knuth_u_hat_mul_pow192_le` — trial-numerator * 2^192 ≤ u_nat.
  - `knuth_v_nat_lt_v_top_succ_mul_pow192` — v_nat < (v_top + 1) * 2^192.
  - `knuth_v_nat_ge_pow255_abstract` — Nat-level v_nat ≥ 2^255.
  - `knuth_q_hat_clamp_le_div` / `knuth_q_hat_clamp_lt_pow64` — min-clamp bounds.
  - `knuth_core_ineq` — `x * z < y + 2 * z → x ≤ y / z + 2` (Knuth overshoot step).
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Scale invariance of integer division on val256: multiplying both operands
    by `2^s` doesn't change the quotient. Entry point for lifting normalized
    val256 computations back to un-normalized quotients.

    Trivial from `Nat.mul_div_mul_right`. -/
theorem val256_div_scale_invariant
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (s : Nat) :
    (val256 a0 a1 a2 a3 * 2^s) / (val256 b0 b1 b2 b3 * 2^s) =
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  have hpos : 0 < (2 : Nat)^s := by positivity
  rw [Nat.mul_div_mul_right _ _ hpos]

/-- RV64 unsigned divide maps to Nat div on toNat (for nonzero divisor).

    Entry-level bridge for reasoning about `div128Quot`, which composes two
    `rv64_divu` calls with correction steps. The zero-divisor case returns
    `BitVec.allOnes 64` and is handled separately at call sites. -/
theorem rv64_divu_toNat (a b : Word) (hb : b ≠ 0) :
    (rv64_divu a b).toNat = a.toNat / b.toNat := by
  unfold rv64_divu
  split
  · rename_i hbeq
    exfalso; apply hb
    simp at hbeq
    exact hbeq
  · rw [BitVec.toNat_udiv]

/-- Under the normalization precondition `b3.toNat ≥ 2^63`, the 4-limb
    divisor is at least `2^255` (i.e. the top bit of the 256-bit value
    is set). Used by Knuth B to bound `v_nat` from below.

    Proof: `val256 ≥ b3.toNat * 2^192 ≥ 2^63 * 2^192 = 2^255`. -/
theorem val256_ge_pow255_of_normalized
    (b0 b1 b2 b3 : Word) (hb3 : b3.toNat ≥ 2^63) :
    val256 b0 b1 b2 b3 ≥ 2^255 := by
  unfold val256
  have h : b3.toNat * 2^192 ≥ 2^63 * 2^192 := Nat.mul_le_mul_right _ hb3
  have hpow : (2:Nat)^63 * 2^192 = 2^255 := by norm_num
  nlinarith

/-- Split a 4-limb value into its high-2-limb half and low-2-limb half:
    `val256 a0 a1 a2 a3 = (a3*B + a2) * B^2 + (a1*B + a0)` where `B = 2^64`.
    Used by Knuth B to express the "trial quotient" in terms of
    `u_top * 2^64 + u3` (the high pair) and `u2 * 2^64 + u1` (the low pair). -/
theorem val256_split_hi2 (a0 a1 a2 a3 : Word) :
    val256 a0 a1 a2 a3 =
      (a3.toNat * 2^64 + a2.toNat) * 2^128 +
      (a1.toNat * 2^64 + a0.toNat) := by
  unfold val256; ring

/-- Knuth B — trial numerator scales up to at most the full numerator.
    `u_nat = u_top * 2^256 + u_next * 2^192 + u_rest` implies
    `(u_top * 2^64 + u_next) * 2^192 ≤ u_nat` since `u_rest ≥ 0` and
    `2^64 * 2^192 = 2^256`. -/
theorem knuth_u_hat_mul_pow192_le
    (u_nat u_top u_next u_rest : Nat)
    (h_u_split : u_top * 2^256 + u_next * 2^192 + u_rest = u_nat) :
    (u_top * 2^64 + u_next) * 2^192 ≤ u_nat := by
  have hpow : (2:Nat)^64 * 2^192 = 2^256 := by rw [← pow_add]
  have h1 : (u_top * 2^64 + u_next) * 2^192 = u_top * 2^256 + u_next * 2^192 := by
    rw [Nat.add_mul, Nat.mul_assoc, hpow]
  omega

/-- Knuth B — full divisor is strictly less than `(v_top + 1) * 2^192`.
    Follows from `v_rest < 2^192`. -/
theorem knuth_v_nat_lt_v_top_succ_mul_pow192
    (v_nat v_top v_rest : Nat)
    (h_v_split : v_nat = v_top * 2^192 + v_rest)
    (h_v_rest : v_rest < 2^192) :
    v_nat < (v_top + 1) * 2^192 := by
  have : (v_top + 1) * 2^192 = v_top * 2^192 + 2^192 := by ring
  omega

/-- Knuth B — Nat-level version of `v_nat ≥ 2^255` under normalization.
    Abstract counterpart of `val256_ge_pow255_of_normalized`. -/
theorem knuth_v_nat_ge_pow255_abstract
    (v_nat v_top v_rest : Nat)
    (h_v_norm : v_top ≥ 2^63)
    (h_v_split : v_nat = v_top * 2^192 + v_rest) :
    v_nat ≥ 2^255 := by
  have h1 : v_top * 2^192 ≥ 2^63 * 2^192 := Nat.mul_le_mul_right _ h_v_norm
  have h2 : (2:Nat)^63 * 2^192 = 2^255 := by rw [← pow_add]
  omega

/-- Knuth B — the min-clamp quotient `q_hat = min((u_top*B + u_next)/v_top, B-1)`
    is at most the raw trial quotient. Trivial from `min_le_left`. -/
theorem knuth_q_hat_clamp_le_div (u_top u_next v_top q_hat : Nat)
    (hq : q_hat = min ((u_top * 2^64 + u_next) / v_top) (2^64 - 1)) :
    q_hat ≤ (u_top * 2^64 + u_next) / v_top := by
  rw [hq]; exact Nat.min_le_left _ _

/-- Knuth B — the min-clamp quotient is strictly less than `2^64`. -/
theorem knuth_q_hat_clamp_lt_pow64 (u_top u_next v_top q_hat : Nat)
    (hq : q_hat = min ((u_top * 2^64 + u_next) / v_top) (2^64 - 1)) :
    q_hat < 2^64 := by
  rw [hq]
  have := Nat.min_le_right ((u_top * 2^64 + u_next) / v_top) (2^64 - 1)
  have hpow : (0:Nat) < 2^64 := by positivity
  omega

/-- Knuth B core overshoot inequality (Nat-abstract):
    `x * z < y + 2 * z` plus `0 < z` implies `x ≤ y / z + 2`.

    This is the final combinator for the "q_hat ≤ q_true + 2" step. After
    accumulating `q_hat_raw * v_nat < u_nat + 2 * v_nat` (from the trial
    remainder bookkeeping + the `v_nat ≥ 2^255` normalization lower bound),
    applying this lemma yields `q_hat_raw ≤ u_nat / v_nat + 2 = q_true + 2`.

    Proof: by contradiction. If `x ≥ y / z + 3`, then
    `(y/z + 3) * z ≤ x * z < y + 2 * z`, so `(y/z) * z + 3*z < y + 2*z`,
    i.e. `(y/z) * z + z < y`. But `y = (y/z) * z + y%z` and `y%z < z`, so
    `y < (y/z) * z + z`. Contradiction. -/
theorem knuth_core_ineq (x y z : Nat) (hz : 0 < z)
    (h : x * z < y + 2 * z) :
    x ≤ y / z + 2 := by
  by_contra hgt
  push Not at hgt
  have h3 : y / z + 3 ≤ x := hgt
  have h4 : (y / z + 3) * z ≤ x * z := Nat.mul_le_mul_right z h3
  have hd : z * (y / z) + y % z = y := Nat.div_add_mod y z
  have hm : y % z < z := Nat.mod_lt y hz
  nlinarith

end EvmAsm.Evm64
