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
  - `b3_prime_val256_eq_scaled` — discharges `hnorm_v` for concrete CLZ shift:
    `val256(b0', b1', b2', b3') = val256(b) * 2^clz(b3)`.
  - `u_val256_eq_scaled_with_overflow` — discharges `hnorm_u` for concrete CLZ
    shift: 4-limb normalized value + overflow = `val256(a) * 2^clz(b3)`.
  - `knuth_theorem_b_from_clz` — **full Word-level Knuth B corollary** from raw
    (a, b, hb3nz, hshift_nz, hcall). No normalization hypotheses needed.
  - `div128Quot_dHi_ge_pow31` — under `vTop ≥ 2^63`, the algorithm's `dHi =
    vTop >>> 32` satisfies `dHi ≥ 2^31` (first Piece B building block).
  - `div128Quot_q1_lt_pow33` — under `dHi ≥ 2^31`, the first-round trial
    quotient `q1 = rv64_divu uHi dHi` is strictly less than `2^33`.
  - `div128Quot_first_round_euclidean` — for nonzero `dHi`, the Word-level
    Euclidean equation `q1.toNat * dHi.toNat + rhat.toNat = uHi.toNat` holds
    where `rhat = uHi - q1 * dHi` (BitVec sub).
  - `div128Quot_first_round_correction` — under `hi1 ≠ 0` and `dHi < 2^32`, the
    corrected `q1c = q1 - 1`, `rhatc = rhat + dHi` preserve the Euclidean
    equation: `q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat`.
  - `div128Quot_first_round_post` — combines no-correction (#830) and
    correction (#834) branches into a single first-round invariant via
    case-split on `hi1`. The Euclidean equation holds for the algorithm's
    actual `q1c` and `rhatc` regardless of which branch is taken.
  - `div128Quot_q1c_lt_pow33` — `q1c < 2^33` after Phase 1a correction,
    regardless of branch (Phase 1b prerequisite).
  - `div128Quot_rhatc_lt_2dHi` — `rhatc.toNat < 2 * dHi.toNat` after Phase 1a,
    regardless of branch (Phase 1b overflow-bound prerequisite).
  - `div128Quot_phase1b_check_implies_q1c_pos` — when Phase 1b's BitVec.ult
    check fires, `q1c.toNat ≥ 1` (proof: q1c = 0 ⟹ qDlo = 0 ⟹ check fails).
  - `div128Quot_phase1b_correction_eucl` — when Phase 1b's check fires and
    correction triggers (q1' = q1c - 1, rhat' = rhatc + dHi), the
    Euclidean equation `q1' * dHi + rhat' = uHi` is preserved.
  - `div128Quot_phase1b_post` — combined Phase 1b invariant covering both
    branches via case-split on the BitVec.ult check.
  - `div128Quot_rhat_prime_lt_3dHi` — `rhat'.toNat < 3 * dHi.toNat` after
    Phase 1b, regardless of branch (input bound for Round 2).
-/

import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity
import EvmAsm.Evm64.EvmWordArith.DenormLemmas

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord
open EvmAsm.Rv64.AddrNorm (bv6_toNat_32)

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
  · have := b0.isLt
    have := b1.isLt
    have := b2.isLt
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
  have h_b3_shifted := b3_shifted_ge_pow63 hb3nz
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
  exact (EvmWord.ult_iff).mp h

/-- Antishift arithmetic: under `1 ≤ shift.toNat ≤ 63`, the algorithm's
    `antiShift = signExtend12 0 - shift` satisfies `antiShift.toNat % 64 =
    64 - shift.toNat`.

    This reconciles the algorithm's `%64` modular form with `val256_normalize_general`'s
    direct `64 - s` form — a prerequisite for lifting abstract Knuth B to Word-level
    normalized limb values. Same proof pattern as in `u_top_lt_pow63_of_shift_nz`
    (MaxTrialVacuity.lean), extracted as a reusable lemma. -/
theorem antiShift_toNat_mod_eq {shift : Word}
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

/-- Discharge of `hnorm_v` from `knuth_theorem_b_val256` using a concrete
    CLZ-based shift: the algorithm's normalized divisor limbs compute to
    `val256(b) * 2^shift`.

    Combines:
    - `Nat.mod_eq_of_lt` to simplify `shift.toNat % 64 = shift.toNat`.
    - `antiShift_toNat_mod_eq` to convert antiShift's `% 64` form to `64 - s`.
    - `clzResult_fst_top_bound` for the `b3 < 2^(64-s)` bound.
    - `val256_normalize` (overflow-free variant, since normalization ensures
      `b3 < 2^(64-s)` with `s = clz(b3)`). -/
theorem b3_prime_val256_eq_scaled
    (b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    val256
      (b0 <<< ((clzResult b3).1.toNat % 64))
      ((b1 <<< ((clzResult b3).1.toNat % 64)) |||
         (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
      ((b2 <<< ((clzResult b3).1.toNat % 64)) |||
         (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
      ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
         (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
      = val256 b0 b1 b2 b3 * 2^(clzResult b3).1.toNat := by
  have h_shift_le := clzResult_fst_toNat_le b3
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b3).1.toNat % 64 = (clzResult b3).1.toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos h_shift_le]
  have hb3_bound := clzResult_fst_top_bound b3
  exact val256_normalize h_shift_pos (by omega) b0 b1 b2 b3 hb3_bound

/-- Discharge of `hnorm_u` from `knuth_theorem_b_val256` using a concrete
    CLZ-based shift: the algorithm's normalized dividend limbs plus the
    overflow `a3 >>> antiShift` (scaled to `2^256`) equal `val256(a) * 2^shift`.

    Parallel of `b3_prime_val256_eq_scaled`, but uses `val256_normalize_general`
    (the overflow-including variant) since the dividend may overshoot 2^256. -/
theorem u_val256_eq_scaled_with_overflow
    (a0 a1 a2 a3 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    val256
      (a0 <<< ((clzResult b3).1.toNat % 64))
      ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
         (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
      ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
         (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
      ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
         (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    + (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)).toNat
      * 2^256
      = val256 a0 a1 a2 a3 * 2^(clzResult b3).1.toNat := by
  have h_shift_le := clzResult_fst_toNat_le b3
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b3).1.toNat % 64 = (clzResult b3).1.toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos h_shift_le]
  exact val256_normalize_general h_shift_pos (by omega) a0 a1 a2 a3

/-- **Knuth's Theorem B at the Word level — full CLZ-driven corollary.**

    Under call-trial + CLZ-normalization hypotheses, the raw 2-limb trial
    quotient `(u4 * 2^64 + un3) / b3'` overestimates the true quotient
    `val256(a) / val256(b)` by at most 2:

    ```
      (u4.toNat * 2^64 + un3.toNat) / b3'.toNat ≤
        val256(a) / val256(b) + 2
    ```

    Composes the discharge bridges (`u_val256_eq_scaled_with_overflow`,
    `b3_prime_val256_eq_scaled`, `b3_prime_ge_pow63`, `isCallTrialN4_toNat_lt`)
    with `knuth_theorem_b_val256`. This is the algorithm-facing conclusion
    that downstream stack-spec reasoning consumes. -/
theorem knuth_theorem_b_from_clz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    ((a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)).toNat * 2^64 +
       ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
          (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat) /
      ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat ≤
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 + 2 := by
  have hnorm_u := u_val256_eq_scaled_with_overflow a0 a1 a2 a3 b3 hshift_nz
  have hnorm_v := b3_prime_val256_eq_scaled b0 b1 b2 b3 hshift_nz
  have hb3prime := b3_prime_ge_pow63 b3 b2 hb3nz
    (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
  have hu4_lt := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  exact knuth_theorem_b_val256 a0 a1 a2 a3 b0 b1 b2 b3
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
    (a0 <<< ((clzResult b3).1.toNat % 64))
    ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
       (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
       (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
       (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    (b0 <<< ((clzResult b3).1.toNat % 64))
    ((b1 <<< ((clzResult b3).1.toNat % 64)) |||
       (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    ((b2 <<< ((clzResult b3).1.toNat % 64)) |||
       (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
       (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    (clzResult b3).1.toNat
    (by linarith [hnorm_u])
    hnorm_v hb3prime hu4_lt

/-- **Piece B entry — first building block for `div128Quot` correctness.**

    Under the normalization precondition `vTop ≥ 2^63`, the `div128Quot`
    algorithm's `dHi = vTop >>> 32` satisfies `dHi.toNat ≥ 2^31`.

    Feeds subsequent Piece B proofs that bound the first-round quotient
    `q1 = rv64_divu uHi dHi` (in particular `q1 < 2^33` when `uHi < 2^64`). -/
theorem div128Quot_dHi_ge_pow31 (vTop : Word) (h : vTop.toNat ≥ 2^63) :
    (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
  rw [BitVec.toNat_ushiftRight]
  rw [bv6_toNat_32, Nat.shiftRight_eq_div_pow]
  have h1 : (2:Nat)^63 / 2^32 ≤ vTop.toNat / 2^32 := Nat.div_le_div_right h
  have h2 : (2:Nat)^63 / 2^32 = 2^31 := by decide
  omega

/-- **Second Piece B building block.** Under `dHi.toNat ≥ 2^31`, the
    first-round trial quotient `q1 = rv64_divu uHi dHi` is strictly less
    than `2^33`.

    Proof: `q1.toNat * dHi.toNat ≤ uHi.toNat < 2^64 = 2^33 * 2^31`, and
    `dHi.toNat ≥ 2^31`, so `q1.toNat * 2^31 ≤ q1.toNat * dHi.toNat <
    2^33 * 2^31`, giving `q1.toNat < 2^33` after cancelling. -/
theorem div128Quot_q1_lt_pow33 (uHi dHi : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31) :
    (rv64_divu uHi dHi).toNat < 2^33 := by
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  rw [rv64_divu_toNat uHi dHi hdHi_ne]
  have : uHi.toNat < 2^64 := uHi.isLt
  have h_pow : (2:Nat)^33 * 2^31 = 2^64 := by rw [← pow_add]
  set q1 := uHi.toNat / dHi.toNat with hq1_def
  have hq_mul : q1 * dHi.toNat ≤ uHi.toNat := Nat.div_mul_le_self _ _
  have hq_lower : q1 * 2^31 ≤ q1 * dHi.toNat := Nat.mul_le_mul_left q1 hdHi_ge
  have hq_lt_mul : q1 * 2^31 < 2^33 * 2^31 := by omega
  exact Nat.lt_of_mul_lt_mul_right hq_lt_mul

/-- **Third Piece B building block — first-round Euclidean equation.**

    For nonzero `dHi`, the algorithm's first-round invariant
    `q1.toNat * dHi.toNat + rhat.toNat = uHi.toNat` holds at the Word level,
    where `q1 = rv64_divu uHi dHi` and `rhat = uHi - q1 * dHi` (BitVec sub).

    The key facts:
    - `q1.toNat = uHi.toNat / dHi.toNat` (`rv64_divu_toNat`).
    - `q1.toNat * dHi.toNat ≤ uHi.toNat < 2^64` ensures `q1 * dHi` doesn't
      wrap as a Word multiplication.
    - The same bound makes the BitVec subtraction `uHi - q1 * dHi` reduce to
      `uHi.toNat - q1.toNat * dHi.toNat` at the Nat level. -/
theorem div128Quot_first_round_euclidean (uHi dHi : Word) (hdHi_ne : dHi ≠ 0) :
    (rv64_divu uHi dHi).toNat * dHi.toNat +
      (uHi - rv64_divu uHi dHi * dHi).toNat = uHi.toNat := by
  set q1 := rv64_divu uHi dHi with hq1_def
  have hq1_eq : q1.toNat = uHi.toNat / dHi.toNat := rv64_divu_toNat uHi dHi hdHi_ne
  have h_q1_mul_le : q1.toNat * dHi.toNat ≤ uHi.toNat := by
    rw [hq1_eq]; exact Nat.div_mul_le_self _ _
  have := uHi.isLt
  have h_q1_mul_lt : q1.toNat * dHi.toNat < 2^64 := by omega
  have hmul_toNat : (q1 * dHi).toNat = q1.toNat * dHi.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt h_q1_mul_lt
  have hrhat_toNat : (uHi - q1 * dHi).toNat = uHi.toNat - q1.toNat * dHi.toNat := by
    rw [BitVec.toNat_sub, hmul_toNat]
    omega
  omega

/-- **Fourth Piece B building block — first-round correction.**

    When `hi1 = q1 >>> 32 ≠ 0`, the algorithm corrects via
    `q1c := q1 + signExtend12 4095` (= `q1 - 1`) and `rhatc := rhat + dHi`.
    Under `dHi.toNat < 2^32` (always true since `dHi = vTop >>> 32`), the
    corrected pair preserves the Euclidean invariant:

    ```
      q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat
    ```

    Proof relies on:
    - `hi1 ≠ 0` ⟹ `q1.toNat ≥ 2^32` ≥ 1, so `q1 - 1` doesn't underflow.
    - `rhat.toNat = uHi mod dHi < dHi`, so `rhat + dHi < 2 * dHi < 2^33`,
      no Word overflow.
    - Algebraic identity at Nat: `(q1 - 1) * dHi + (rhat + dHi) = q1 * dHi + rhat`. -/
theorem div128Quot_first_round_correction (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32)
    (hhi1_nz : (rv64_divu uHi dHi) >>> (32 : BitVec 6).toNat ≠ 0) :
    (rv64_divu uHi dHi + signExtend12 4095).toNat * dHi.toNat +
      (uHi - rv64_divu uHi dHi * dHi + dHi).toNat = uHi.toNat := by
  set q1 := rv64_divu uHi dHi with hq1_def
  set rhat := uHi - q1 * dHi with hrhat_def
  -- Nat-level facts
  have hq1_eq : q1.toNat = uHi.toNat / dHi.toNat := rv64_divu_toNat uHi dHi hdHi_ne
  have h_eucl : q1.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    have := div128Quot_first_round_euclidean uHi dHi hdHi_ne
    convert this using 2
  have hdHi_pos : 0 < dHi.toNat := by
    rcases Nat.eq_zero_or_pos dHi.toNat with h | h
    · exfalso; apply hdHi_ne; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  -- rhat.toNat < dHi.toNat
  have hrhat_lt_dHi : rhat.toNat < dHi.toNat := by
    have h_dam : dHi.toNat * (uHi.toNat / dHi.toNat) + uHi.toNat % dHi.toNat = uHi.toNat :=
      Nat.div_add_mod _ _
    have h_eucl_div :
        (uHi.toNat / dHi.toNat) * dHi.toNat + rhat.toNat = uHi.toNat := by
      rw [← hq1_eq]; exact h_eucl
    have h_comm :
        dHi.toNat * (uHi.toNat / dHi.toNat) = (uHi.toNat / dHi.toNat) * dHi.toNat :=
      Nat.mul_comm _ _
    have h_mod_lt : uHi.toNat % dHi.toNat < dHi.toNat := Nat.mod_lt _ hdHi_pos
    omega
  -- hi1 ≠ 0 ⟹ q1.toNat ≥ 2^32
  have hq1_ge : q1.toNat ≥ 2^32 := by
    by_contra h
    push Not at h
    apply hhi1_nz
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    show q1.toNat / 2^32 = (0 : Word).toNat
    rw [Nat.div_eq_of_lt h]
    rfl
  -- q1c.toNat = q1.toNat - 1
  have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
  have hq1c_toNat : (q1 + signExtend12 4095).toNat = q1.toNat - 1 := by
    rw [BitVec.toNat_add, h_se_neg1]
    have : q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 := by omega
    rw [this, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by have := q1.isLt; omega)
  -- rhatc.toNat = rhat.toNat + dHi.toNat (no overflow)
  have hrhatc_toNat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat := by
    rw [BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    have : rhat.toNat + dHi.toNat < 2 * 2^32 := by omega
    omega
  rw [hq1c_toNat, hrhatc_toNat]
  -- (q1 - 1) * dHi + (rhat + dHi) = q1 * dHi + rhat = uHi
  have h_q1_ge_one : q1.toNat ≥ 1 := by omega
  have key : (q1.toNat - 1) * dHi.toNat + (rhat.toNat + dHi.toNat) =
             q1.toNat * dHi.toNat + rhat.toNat := by
    have h1 : (q1.toNat - 1 + 1) * dHi.toNat =
              (q1.toNat - 1) * dHi.toNat + dHi.toNat := by
      rw [Nat.add_mul, Nat.one_mul]
    have h_eq : q1.toNat - 1 + 1 = q1.toNat := by omega
    have h2 : (q1.toNat - 1 + 1) * dHi.toNat = q1.toNat * dHi.toNat := by
      rw [h_eq]
    omega
  rw [key]; exact h_eucl

/-- **Combined first-round invariant.** Whichever branch the algorithm
    takes (`hi1 = 0` or `hi1 ≠ 0`), the post-correction `q1c, rhatc` pair
    satisfies the Word-level Euclidean equation:

    ```
      q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat
    ```

    Proof is a case-split on `hi1 = 0` dispatching to
    `div128Quot_first_round_euclidean` or `div128Quot_first_round_correction`.

    Together with the algorithm's choice
    `q1c := if hi1 = 0 then q1 else q1 + (-1)` and similarly for `rhatc`,
    this is the input to the analogous second-round analysis (yet to come). -/
theorem div128Quot_first_round_post
    (uHi dHi : Word) (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat := by
  intro q1 rhat hi1 q1c rhatc
  by_cases h_hi1 : hi1 = 0
  · -- No-correction branch: q1c = q1, rhatc = rhat
    simp only [q1c, rhatc, h_hi1, ↓reduceIte]
    exact div128Quot_first_round_euclidean uHi dHi hdHi_ne
  · -- Correction branch: q1c = q1 + (-1), rhatc = rhat + dHi
    simp only [q1c, rhatc, h_hi1, ↓reduceIte]
    exact div128Quot_first_round_correction uHi dHi hdHi_ne hdHi_lt h_hi1

/-- **Phase 1b prerequisite — `q1c.toNat < 2^33` regardless of branch.**

    After Phase 1a's hi1-correction, the post-correction quotient `q1c`
    is bounded by `2^33`, regardless of whether the correction branch was
    taken. This is the bound the second correction (Phase 1b — Knuth's
    multiplication check) needs as input.

    - No-correction case (`hi1 = 0`): `q1c = q1 < 2^32 < 2^33`
      (from `hi1 = 0` ⟹ `q1 / 2^32 = 0` ⟹ `q1 < 2^32`).
    - Correction case (`hi1 ≠ 0`): `q1c = q1 - 1 < q1 ≤ 2^33 - 1`
      (using `div128Quot_q1_lt_pow33`).

    Both bounds give `q1c < 2^33`. -/
theorem div128Quot_q1c_lt_pow33 (uHi dHi : Word) (hdHi_ge : dHi.toNat ≥ 2^31) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat < 2^33 := by
  intro q1 hi1 q1c
  have hq1_lt : q1.toNat < 2^33 := div128Quot_q1_lt_pow33 uHi dHi hdHi_ge
  by_cases h_hi1 : hi1 = 0
  · -- q1c = q1 < 2^33
    simp only [q1c, h_hi1, ↓reduceIte]
    exact hq1_lt
  · -- q1c = q1 + (-1). q1 ≥ 1, so q1c.toNat = q1.toNat - 1 < q1.toNat < 2^33.
    simp only [q1c, h_hi1, ↓reduceIte]
    have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
    -- q1.toNat ≥ 2^32 (from hi1 ≠ 0)
    have hq1_ge : q1.toNat ≥ 2^32 := by
      by_contra h
      push Not at h
      apply h_hi1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      show q1.toNat / 2^32 = (0 : Word).toNat
      rw [Nat.div_eq_of_lt h]
      rfl
    rw [BitVec.toNat_add, h_se_neg1]
    have h_eq : q1.toNat + (2^64 - 1) = (q1.toNat - 1) + 2^64 := by omega
    rw [h_eq, Nat.add_mod_right]
    have hq1_lt_word : q1.toNat - 1 < 2^64 := by have := q1.isLt; omega
    rw [Nat.mod_eq_of_lt hq1_lt_word]
    omega

/-- **Phase 1b overflow-bound prerequisite — `rhatc.toNat < 2 * dHi.toNat`.**

    After Phase 1a's hi1-correction, the post-correction remainder `rhatc`
    is bounded by `2 * dHi`, regardless of which branch was taken. This
    bounds Phase 1b's analysis (where `rhat' = rhatc + dHi` could have
    overflowed without it).

    - No-correction case (`hi1 = 0`): `rhatc = rhat = uHi mod dHi < dHi`
      (using the Euclidean equation + `Nat.mod_lt`).
    - Correction case (`hi1 ≠ 0`): `rhatc = rhat + dHi < 2 * dHi` (since
      `rhat < dHi`, and the Word addition doesn't overflow because
      `dHi < 2^32` ⟹ `rhat + dHi < 2^33 < 2^64`). -/
theorem div128Quot_rhatc_lt_2dHi (uHi dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    rhatc.toNat < 2 * dHi.toNat := by
  intro q1 rhat hi1 rhatc
  -- rhat.toNat < dHi.toNat (Phase 1a output: rhat = uHi mod dHi)
  have hq1_eq : q1.toNat = uHi.toNat / dHi.toNat := rv64_divu_toNat uHi dHi hdHi_ne
  have h_eucl : q1.toNat * dHi.toNat + rhat.toNat = uHi.toNat :=
    div128Quot_first_round_euclidean uHi dHi hdHi_ne
  have hdHi_pos : 0 < dHi.toNat := by
    rcases Nat.eq_zero_or_pos dHi.toNat with h | h
    · exfalso; apply hdHi_ne; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hrhat_lt_dHi : rhat.toNat < dHi.toNat := by
    have h_dam : dHi.toNat * (uHi.toNat / dHi.toNat) + uHi.toNat % dHi.toNat = uHi.toNat :=
      Nat.div_add_mod _ _
    have h_eucl_div :
        (uHi.toNat / dHi.toNat) * dHi.toNat + rhat.toNat = uHi.toNat := by
      rw [← hq1_eq]; exact h_eucl
    have h_comm :
        dHi.toNat * (uHi.toNat / dHi.toNat) = (uHi.toNat / dHi.toNat) * dHi.toNat :=
      Nat.mul_comm _ _
    have h_mod_lt : uHi.toNat % dHi.toNat < dHi.toNat := Nat.mod_lt _ hdHi_pos
    omega
  by_cases h_hi1 : hi1 = 0
  · -- rhatc = rhat < dHi < 2 * dHi
    simp only [rhatc, h_hi1, ↓reduceIte]
    omega
  · -- rhatc = rhat + dHi (Word add). Word add doesn't overflow (rhat + dHi < 2^33).
    simp only [rhatc, h_hi1, ↓reduceIte]
    rw [BitVec.toNat_add]
    have h_sum_lt : rhat.toNat + dHi.toNat < 2^64 := by omega
    rw [Nat.mod_eq_of_lt h_sum_lt]
    omega

/-- **Phase 1b sub-step.** When Phase 1b's `BitVec.ult rhatUn1 qDlo` check
    fires (the Knuth multiplication check), the post-Phase-1a quotient
    `q1c` must be at least 1.

    Proof by contradiction: if `q1c = 0`, then `qDlo = 0 * dLo = 0` and
    `rhatUn1 < 0` is impossible at the Nat level. So `q1c ≥ 1`, which
    means the upcoming `q1' = q1c + signExtend12 4095` (= `q1c - 1`)
    decrement is safe (no underflow). -/
theorem div128Quot_phase1b_check_implies_q1c_pos
    (q1c dLo rhatUn1 : Word)
    (h_check : BitVec.ult rhatUn1 (q1c * dLo)) :
    q1c.toNat ≥ 1 := by
  by_contra h
  push Not at h
  have hq1c_zero : q1c.toNat = 0 := by omega
  have hq1c_eq : q1c = 0 := BitVec.eq_of_toNat_eq (by simp [hq1c_zero])
  rw [hq1c_eq] at h_check
  have h_lt : rhatUn1.toNat < ((0 : Word) * dLo).toNat :=
    (EvmWord.ult_iff).mp h_check
  have hmul_zero : ((0 : Word) * dLo).toNat = 0 := by
    rw [BitVec.toNat_mul]; simp
  rw [hmul_zero] at h_lt
  exact Nat.not_lt_zero _ h_lt

/-- **Phase 1b correction case — Euclidean preservation (factored form).**

    Takes the prerequisites as explicit hypotheses (rather than computing them
    via the let-bound algorithm chain) for cleaner type-checking. Callers
    discharge them via:
    - `h_post` from `div128Quot_first_round_post` (#837).
    - `h_q1c_pos` from `div128Quot_phase1b_check_implies_q1c_pos` (#849).
    - `h_rhatc_lt` from `div128Quot_rhatc_lt_2dHi` (#845).

    Conclusion: `q1' = q1c - 1` and `rhat' = rhatc + dHi` (Phase 1b correction)
    preserve the Word-level Euclidean equation
    `q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat`.

    Algebra: `(q1c - 1) * dHi + (rhatc + dHi) = q1c * dHi + rhatc = uHi`. -/
theorem div128Quot_phase1b_correction_eucl
    (uHi dHi q1c rhatc : Word)
    (hdHi_lt : dHi.toNat < 2^32)
    (h_post : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat)
    (h_q1c_pos : q1c.toNat ≥ 1)
    (h_rhatc_lt : rhatc.toNat < 2 * dHi.toNat) :
    (q1c + signExtend12 4095).toNat * dHi.toNat +
      (rhatc + dHi).toNat = uHi.toNat := by
  -- q1' = q1c - 1
  have h_se_neg1 : (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by decide
  have hq1'_toNat : (q1c + signExtend12 4095).toNat = q1c.toNat - 1 := by
    rw [BitVec.toNat_add, h_se_neg1]
    have h_eq : q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 := by omega
    rw [h_eq, Nat.add_mod_right]
    have hq1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
    rw [Nat.mod_eq_of_lt hq1c_lt_word]
  -- rhat' = rhatc + dHi (no overflow: rhatc < 2*dHi, dHi < 2^32 → rhatc + dHi < 3*2^32 < 2^64)
  have hrhat'_toNat : (rhatc + dHi).toNat = rhatc.toNat + dHi.toNat := by
    rw [BitVec.toNat_add]
    apply Nat.mod_eq_of_lt
    omega
  rw [hq1'_toNat, hrhat'_toNat]
  -- (q1c - 1) * dHi + (rhatc + dHi) = q1c * dHi + rhatc = uHi (h_post)
  have h_expand : (q1c.toNat - 1 + 1) * dHi.toNat =
                  (q1c.toNat - 1) * dHi.toNat + dHi.toNat := by
    rw [Nat.add_mul, Nat.one_mul]
  have h_eq : q1c.toNat - 1 + 1 = q1c.toNat := by omega
  rw [h_eq] at h_expand
  omega

/-- **Combined Phase 1b invariant.** Whichever branch the algorithm takes
    (Knuth multiplication-check fires or doesn't), the post-Phase-1b
    `q1'`, `rhat'` pair satisfies the Word-level Euclidean equation:

    ```
      q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat
    ```

    Case-split on the `BitVec.ult rhatUn1 (q1c * dLo)` check:
    - Check doesn't fire: `q1' = q1c`, `rhat' = rhatc`. Invariant unchanged
      from Phase 1a (= the supplied `h_post` hypothesis).
    - Check fires: `q1' = q1c - 1`, `rhat' = rhatc + dHi`. Apply
      `div128Quot_phase1b_correction_eucl` (which itself uses
      `div128Quot_phase1b_check_implies_q1c_pos` for safety). -/
theorem div128Quot_phase1b_post
    (uHi dHi q1c rhatc dLo rhatUn1 : Word)
    (hdHi_lt : dHi.toNat < 2^32)
    (h_post : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat)
    (h_rhatc_lt : rhatc.toNat < 2 * dHi.toNat) :
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat := by
  intro q1' rhat'
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · -- Check fires: apply correction case
    simp only [q1', rhat', h_check]
    have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    exact div128Quot_phase1b_correction_eucl uHi dHi q1c rhatc hdHi_lt
      h_post h_q1c_pos h_rhatc_lt
  · -- Check doesn't fire: q1' = q1c, rhat' = rhatc, invariant is h_post
    simp only [q1', rhat', h_check]
    exact h_post

/-- **Post-Phase-1b output bound on `rhat'`.** After Phase 1b, the
    corrected remainder `rhat'` is bounded by `3 * dHi`:

    - No-correction case: `rhat' = rhatc < 2 * dHi` (from
      `div128Quot_rhatc_lt_2dHi`) `< 3 * dHi`.
    - Correction case: `rhat' = rhatc + dHi`. Word addition doesn't
      overflow because `rhatc < 2 * dHi`, `dHi < 2^32`, so
      `rhatc + dHi < 3 * 2^32 < 2^64`.

    Used by the Round 2 entry analysis: `cu_rhat_un1 = (rhat' << 32) | div_un1`
    needs `rhat' < 2^32` to avoid OR-shift bit overlap, but the weaker
    `rhat' < 3 * dHi < 3 * 2^32` is sufficient for `un21` overflow analysis. -/
theorem div128Quot_rhat_prime_lt_3dHi (dHi rhatc : Word)
    (hdHi_lt : dHi.toNat < 2^32)
    (h_rhatc_lt : rhatc.toNat < 2 * dHi.toNat) (rhatUn1 qDlo : Word) :
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    rhat'.toNat < 3 * dHi.toNat := by
  intro rhat'
  by_cases h_check : BitVec.ult rhatUn1 qDlo
  · -- Correction: rhat' = rhatc + dHi
    show (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc).toNat < _
    rw [if_pos h_check, BitVec.toNat_add]
    have h_sum_lt : rhatc.toNat + dHi.toNat < 2^64 := by omega
    rw [Nat.mod_eq_of_lt h_sum_lt]
    omega
  · -- No correction: rhat' = rhatc < 2 * dHi < 3 * dHi
    show (if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc).toNat < _
    rw [if_neg h_check]
    omega

end EvmAsm.Evm64
