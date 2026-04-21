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
  - `knuth_q_r_v_nat_bound` — `q_r * v_nat < u_nat + 2 * v_nat` under call-trial
    assumption `u_top < v_top` (feeds `knuth_core_ineq`).
  - `knuth_theorem_b_abstract` — the Nat-abstract form of Knuth's Theorem B:
    `q_r ≤ u_nat / v_nat + 2` (call-trial regime). Composed from the above.
  - `val256_split_top_limb` — Word→Nat bridge exposing `h_v_split`/`h_v_rest`
    for concrete 4-limb val256 values (feeds abstract Knuth B).
  - `b3_prime_ge_pow63` — normalized divisor top limb `b3'` is ≥ 2^63
    (directly feeds abstract Knuth B's `h_v_norm`).
  - `isCallTrialN4_toNat_lt` — Word→Nat bridge converting `BitVec.ult u4 b3'`
    to the Nat comparison needed by abstract Knuth B's `hu_top_lt`.
  - `antiShift_toNat_mod_eq` — `(signExtend12 0 - shift).toNat % 64 = 64 - shift.toNat`
    for `1 ≤ shift.toNat ≤ 63` (the antiShift arithmetic helper).
  - `knuth_theorem_b_val256` — val256-level corollary of Knuth B, assembling the
    abstract theorem with the Word→Nat bridges against provided normalization
    hypotheses. Concludes `(u4 * B + un3) / b3' ≤ val256(a) / val256(b) + 2`.
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

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

/-- Knuth B — trial-remainder bookkeeping (Nat-abstract call-trial bound).

    Under the call-trial hypothesis `u_top < v_top` and standard normalization
    (`v_top ≥ 2^63`, `v_rest < 2^192`, `u_next < 2^64`), the raw 2-limb trial
    quotient `q_r = (u_top * 2^64 + u_next) / v_top` satisfies
    `q_r * v_nat < u_nat + 2 * v_nat`.

    Combined with `knuth_core_ineq`, this yields `q_r ≤ u_nat / v_nat + 2`,
    the "overestimate by at most 2" conclusion of Knuth's Theorem B. -/
theorem knuth_q_r_v_nat_bound
    (u_nat v_nat u_top u_next u_rest v_top v_rest : Nat)
    (h_u_split : u_top * 2^256 + u_next * 2^192 + u_rest = u_nat)
    (h_v_split : v_nat = v_top * 2^192 + v_rest)
    (h_v_rest : v_rest < 2^192)
    (h_v_norm : v_top ≥ 2^63)
    (hu_top_lt : u_top < v_top)
    (hu_next_lt : u_next < 2^64) :
    (u_top * 2^64 + u_next) / v_top * v_nat < u_nat + 2 * v_nat := by
  set u_hat := u_top * 2^64 + u_next with hu_hat_def
  set q_r := u_hat / v_top with hq_r_def
  -- Basic facts
  have hv_top_pos : 0 < v_top := by
    have : (0:Nat) < 2^63 := by positivity
    omega
  -- u_hat < v_top * 2^64 (call-trial: u_top < v_top, u_next < 2^64)
  have hu_hat_lt : u_hat < v_top * 2^64 := by
    have h1 : (u_top + 1) * 2^64 ≤ v_top * 2^64 := Nat.mul_le_mul_right _ hu_top_lt
    simp only [hu_hat_def]; nlinarith
  -- q_r < 2^64 (Nat.div_lt_of_lt_mul expects n < k * m → n / k < m)
  have hqr_lt : q_r < 2^64 := Nat.div_lt_of_lt_mul hu_hat_lt
  -- q_r * v_top ≤ u_hat (floor div)
  have hqr_vt_le : q_r * v_top ≤ u_hat := Nat.div_mul_le_self u_hat v_top
  -- u_hat * 2^192 ≤ u_nat (from knuth_u_hat_mul_pow192_le)
  have hu_hat_mul_le : u_hat * 2^192 ≤ u_nat :=
    knuth_u_hat_mul_pow192_le u_nat u_top u_next u_rest h_u_split
  -- So q_r * v_top * 2^192 ≤ u_nat
  have hqr_vt_pow : q_r * v_top * 2^192 ≤ u_nat :=
    le_trans (Nat.mul_le_mul_right _ hqr_vt_le) hu_hat_mul_le
  -- v_nat ≥ 2^255
  have hv_nat_ge : v_nat ≥ 2^255 :=
    knuth_v_nat_ge_pow255_abstract v_nat v_top v_rest h_v_norm h_v_split
  -- Expand q_r * v_nat using h_v_split
  have heq : q_r * v_nat = q_r * v_top * 2^192 + q_r * v_rest := by
    rw [h_v_split]; ring
  -- Bound q_r * v_rest < 2 * v_nat
  have h_pow : (2:Nat)^64 * 2^192 = 2^256 := by rw [← pow_add]
  have h_pow_split : (2:Nat)^256 = 2 * 2^255 := by
    rw [show (256:Nat) = 1 + 255 from rfl, pow_add, pow_one]
  have hqr_vrest_le : q_r * v_rest ≤ q_r * 2^192 :=
    Nat.mul_le_mul_left _ (by omega)
  have hqr1_pow_le : (q_r + 1) * 2^192 ≤ 2^64 * 2^192 :=
    Nat.mul_le_mul_right _ hqr_lt
  have h_expand : (q_r + 1) * 2^192 = q_r * 2^192 + 2^192 := by ring
  have h_pos192 : (0:Nat) < 2^192 := by positivity
  have h_2vnat : 2 * v_nat ≥ 2 * 2^255 := Nat.mul_le_mul_left 2 hv_nat_ge
  omega

/-- Knuth's TAOCP Vol 2 §4.3.1 Theorem B — Nat-abstract form (call-trial regime).

    Under the call-trial hypothesis `u_top < v_top` + normalization
    (`v_top ≥ 2^63`, `v_rest < 2^192`, `u_next < 2^64`), the raw 2-limb trial
    quotient `q_r = (u_top * 2^64 + u_next) / v_top` overestimates the true
    quotient `u_nat / v_nat` by at most 2:
    ```
      q_r ≤ u_nat / v_nat + 2
    ```
    This is the core mathematical content of Knuth's Theorem B.

    Proof: apply `knuth_q_r_v_nat_bound` to derive the multiplicative
    inequality, then close with `knuth_core_ineq`. -/
theorem knuth_theorem_b_abstract
    (u_nat v_nat u_top u_next u_rest v_top v_rest : Nat)
    (h_u_split : u_top * 2^256 + u_next * 2^192 + u_rest = u_nat)
    (h_v_split : v_nat = v_top * 2^192 + v_rest)
    (h_v_rest : v_rest < 2^192)
    (h_v_norm : v_top ≥ 2^63)
    (hu_top_lt : u_top < v_top)
    (hu_next_lt : u_next < 2^64) :
    (u_top * 2^64 + u_next) / v_top ≤ u_nat / v_nat + 2 := by
  have hv_nat_pos : 0 < v_nat := by
    have h1 : v_nat ≥ 2^255 :=
      knuth_v_nat_ge_pow255_abstract v_nat v_top v_rest h_v_norm h_v_split
    have : (0:Nat) < 2^255 := by positivity
    omega
  have h_mul_bound :
      (u_top * 2^64 + u_next) / v_top * v_nat < u_nat + 2 * v_nat :=
    knuth_q_r_v_nat_bound u_nat v_nat u_top u_next u_rest v_top v_rest
      h_u_split h_v_split h_v_rest h_v_norm hu_top_lt hu_next_lt
  exact knuth_core_ineq _ _ _ hv_nat_pos h_mul_bound

/-- Word→Nat bridge — val256 decomposes into top limb * 2^192 + lower-3-limb
    residue, where the residue is < 2^192.

    Directly produces the `h_v_split`/`h_v_rest` form required by the
    abstract Knuth B theorems (`knuth_q_r_v_nat_bound`,
    `knuth_theorem_b_abstract`) from a concrete 4-limb Word value. -/
theorem val256_split_top_limb (b0 b1 b2 b3 : Word) :
    ∃ v_rest, v_rest < 2^192 ∧
      val256 b0 b1 b2 b3 = b3.toNat * 2^192 + v_rest := by
  refine ⟨b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128, ?_, ?_⟩
  · have h0 := b0.isLt
    have h1 := b1.isLt
    have h2 := b2.isLt
    -- b_i < 2^64, so b0 + b1*2^64 + b2*2^128 ≤ 2^192 - 1 < 2^192
    nlinarith
  · unfold val256; ring

/-- The normalized divisor top limb `b3' = (b3 << shift) ||| (b2 >> antiShift)`
    satisfies `b3'.toNat ≥ 2^63`.

    Directly feeds the `h_v_norm` hypothesis of the abstract Knuth B theorems.
    Combines `b3_shifted_ge_pow63` with OR-monotonicity (`Nat.left_le_or`). -/
theorem b3_prime_ge_pow63 (b3 b2 : Word) (hb3nz : b3 ≠ 0)
    (antiShift : Word) :
    ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
      (b2 >>> (antiShift.toNat % 64))).toNat ≥ 2^63 := by
  have h_b3_shifted := b3_shifted_ge_pow63 b3 hb3nz
  have h_or_ge :
      ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
        (b2 >>> (antiShift.toNat % 64))).toNat ≥
      (b3 <<< ((clzResult b3).1.toNat % 64)).toNat := by
    rw [BitVec.toNat_or]; exact Nat.left_le_or
  exact le_trans h_b3_shifted h_or_ge

/-- Word→Nat bridge — `isCallTrialN4` (defined via `BitVec.ult`) yields the
    Nat comparison `u4.toNat < b3'.toNat`, which is the `hu_top_lt`
    hypothesis required by abstract Knuth B.

    Trivial `unfold + EvmWord.ult_iff`, but extracted so call sites can
    apply abstract Knuth B without knowing the internal definition. -/
theorem isCallTrialN4_toNat_lt (a3 b2 b3 : Word)
    (h : isCallTrialN4 a3 b2 b3) :
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)).toNat <
      ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat := by
  unfold isCallTrialN4 at h
  exact (EvmWord.ult_iff _ _).mp h

/-- Antishift arithmetic: under `1 ≤ shift.toNat ≤ 63`, the algorithm's
    `antiShift = signExtend12 0 - shift` satisfies `antiShift.toNat % 64 =
    64 - shift.toNat`.

    This reconciles the algorithm's `%64` modular form with `val256_normalize_general`'s
    direct `64 - s` form — a prerequisite for lifting abstract Knuth B to Word-level
    normalized limb values. Same proof pattern as in `u_top_lt_pow63_of_shift_nz`
    (MaxTrialVacuity.lean), extracted as a reusable lemma. -/
theorem antiShift_toNat_mod_eq (shift : Word)
    (h1 : 1 ≤ shift.toNat) (h63 : shift.toNat ≤ 63) :
    (signExtend12 (0 : BitVec 12) - shift).toNat % 64 = 64 - shift.toNat := by
  have h0 : (signExtend12 (0 : BitVec 12) : Word) = 0 := by decide
  rw [h0]
  have hshift_toNat : ((0 : Word) - shift).toNat = 2^64 - shift.toNat := by
    rw [BitVec.toNat_sub]; simp; omega
  rw [hshift_toNat]
  have hsplit : 2^64 - shift.toNat = (2^64 - 64) + (64 - shift.toNat) := by omega
  rw [hsplit, Nat.add_mod]
  have hmod64 : (2^64 - 64) % 64 = 0 := by decide
  rw [hmod64]
  simp
  omega

/-- Knuth B at the val256 level — assembles the abstract Nat theorem with
    the Word→Nat bridges, yielding the algorithm-facing conclusion.

    Given pre-normalized 5-limb dividend `(u4, un0..un3)` and 4-limb
    divisor `(b0', b1', b2', b3')` related to `(a, b)` by scale factor
    `2^shift`, and the call-trial hypothesis `u4 < b3'`, the raw 2-limb
    trial quotient overestimates the true quotient by at most 2:

    ```
      (u4 * 2^64 + un3) / b3'.toNat ≤ val256(a) / val256(b) + 2
    ```

    The normalization facts `hnorm_u`, `hnorm_v`, `hb3prime_ge_pow63`,
    `hu4_lt_b3prime` are hypotheses here; concrete CLZ-based callers
    discharge them via the existing helpers (`val256_normalize_general`,
    `val256_normalize`, `b3_prime_ge_pow63`, `isCallTrialN4_toNat_lt`). -/
theorem knuth_theorem_b_val256
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (u4 un0 un1 un2 un3 : Word)
    (b0' b1' b2' b3' : Word)
    (shift : Nat)
    (hnorm_u : u4.toNat * 2^256 + val256 un0 un1 un2 un3 =
               val256 a0 a1 a2 a3 * 2^shift)
    (hnorm_v : val256 b0' b1' b2' b3' = val256 b0 b1 b2 b3 * 2^shift)
    (hb3prime_ge_pow63 : b3'.toNat ≥ 2^63)
    (hu4_lt_b3prime : u4.toNat < b3'.toNat) :
    (u4.toNat * 2^64 + un3.toNat) / b3'.toNat ≤
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  -- Extract Nat-form splits from val256_split_top_limb
  obtain ⟨u_rest, hu_rest_lt, hu_split_val⟩ := val256_split_top_limb un0 un1 un2 un3
  obtain ⟨v_rest, hv_rest_lt, hv_split_val⟩ := val256_split_top_limb b0' b1' b2' b3'
  -- u_nat := val256(a) * 2^shift, v_nat := val256(b) * 2^shift
  set u_nat := val256 a0 a1 a2 a3 * 2^shift with hu_nat_def
  set v_nat := val256 b0 b1 b2 b3 * 2^shift with hv_nat_def
  -- u_nat = u4 * 2^256 + un3 * 2^192 + u_rest
  have h_u_split : u4.toNat * 2^256 + un3.toNat * 2^192 + u_rest = u_nat := by
    rw [← hnorm_u, hu_split_val]; ring
  -- v_nat = b3' * 2^192 + v_rest
  have h_v_split : v_nat = b3'.toNat * 2^192 + v_rest := by
    rw [← hnorm_v, hv_split_val]
  -- un3.toNat < 2^64 (Word limb)
  have hu_next_lt : un3.toNat < 2^64 := un3.isLt
  -- Apply abstract Knuth B
  have h_abs :=
    knuth_theorem_b_abstract u_nat v_nat u4.toNat un3.toNat u_rest b3'.toNat v_rest
      h_u_split h_v_split hv_rest_lt hb3prime_ge_pow63 hu4_lt_b3prime hu_next_lt
  -- Rewrite u_nat / v_nat via scale invariance
  rw [hu_nat_def, hv_nat_def, val256_div_scale_invariant] at h_abs
  exact h_abs

end EvmAsm.Evm64
