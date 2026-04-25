/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.CompensationCases

  §A of the call-skip lower bound — the core Knuth-B compensation case
  decomposition. Shows that the algorithm's combined quotient
  `(qHat = algorithmQ1Prime * 2^32 + algorithmQ0Prime)` satisfies
  `(qHat + 1) * b3' > u`, hence `u / b3' ≤ qHat` (= `div128Quot.toNat`).

  Extracted from `CallSkipLowerBoundV2.lean` for file-size hygiene.

  ## Contents

  **STATUS (2026-04-25)**: ZERO sorries. The Phase 2 tightness for un21
  ≥ 2^63 closes via the unconditional un21-level helper
  `div128Quot_q0_prime_ge_q_true_0_un21_level`, which uses the algorithm's
  own Phase 2b truncation guard to dispatch between `_small_rhatc` (when
  rhat2c < 2^32) and KB-LB3 (when rhat2c ≥ 2^32). No Knuth-B extension
  was needed — the original "genuinely-hard rhat2c ≥ 2^32 truncation
  regime" framing missed that the algorithm already handles it.

  All wide-u4 sub-cases are vacuous via `hu4_lt_pow63 : u4 < 2^63`
  threaded from the top-level theorem.

  - **A2.S1 helpers** (pure Nat algebra):
      `nat_succ_mul_gt_of_div_le`, `halfword_combine_ge_of_tight`,
      `two_step_div_identity`, `qHat_plus_one_gt_u_via_tight_phases`,
      `q_true_1_lt_pow32`.
  - **A2.S1 normal**: `_normal` (closed) — un21 < dHi*2^32 ∧ u4 < dHi*2^32.
  - **A2.S2 q1' helpers**:
      - `_of_q1_prime_overshoot` (closed) — q1' ≥ q_true_1 + 1 case.
      - `algorithmQ1Prime_ge_q1_dHi_minus_two` (closed) — wrapped Phase 1b
        lower bound (KB-2 wrapped).
      - `algorithmQ1Prime_ge_q_true_1_in_wide_u4` (closed VACUOUSLY via
        hu4_lt_pow63).
  - **Phase 2 tightness chain** (Phase 1 exact case):
      - `_of_q1_prime_eq_q_true_1_narrow_narrow` (closed)
      - `_of_q1_prime_eq_q_true_1_narrow_wide_lt_pow63` (closed via KB-LB8)
      - `_of_q1_prime_eq_q_true_1_narrow_wide_ge_pow63` (closed via the
        shared `_of_un21_ge_pow63` stub)
      - `_of_q1_prime_eq_q_true_1_narrow_wide` (closed via dispatch)
      - `_of_q1_prime_eq_q_true_1` umbrella (closed via 2x2 dispatch
        with wide-u4 vacuous via hu4_lt_pow63)
      - `algorithmQ0Prime_ge_q_true_0_of_un21_ge_pow63` (closed via the
        unconditional un21-level helper).
  - **A2.S2 not-overshoot path**:
      - `algorithmQ0Prime_compensates_phase1_deficit` (closed)
      - `algorithmUn21_lt_vTop_of_q1_prime_not_overshoot` (closed)
      - `algorithmQ0Prime_lt_pow32_of_q1_prime_not_overshoot` (closed)
      - `div128Quot_ge_q_true_full_of_q1_prime_not_overshoot` (closed)
      - `_of_q1_prime_not_overshoot` (closed)
  - **A2.S2 sub-cases** (each delegating to the q1' helpers above):
      - `_narrow_u4_tight_un21`, `_narrow_u4_wide_un21`, `_narrow_u4`
      - `_wide_un21_narrow`, `_wide_un21_wide`, `_wide_un21`
  - **A2.S2 compensation**: `_compensation` (closed).
  - **A2 main**: `div128Quot_qHat_plus_one_times_b3_gt_u` (closed).
  - **A4 wrapper**: `div128Quot_ge_q_true_normalized` (closed).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.Un21Bridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- =============================================================================
-- §A — Core Knuth-B lower bound (128/64 level)
--
-- The main theorem uses `div128Quot_ge_q_true_normalized` (A4), which in
-- turn uses `div128Quot_qHat_plus_one_times_b3_gt_u` (A2). The Knuth-B
-- UPPER form (previously scaffolded as "A1") is not on the critical path
-- and has been dropped to simplify the file.
--
-- A2's proof is decomposed into sub-lemmas (A2.S1–A2.S4 below).
-- =============================================================================

/-- **OR-shift lower bound** (Word-level): for `a < 2^32`,
    `((a <<< 32) ||| b).toNat ≥ a.toNat * 2^32`.

    Proof: `(a <<< 32).toNat = a * 2^32` (since a < 2^32 ⟹ a*2^32 < 2^64),
    and `(x ||| y).toNat ≥ x.toNat` (OR can only add bits). -/
theorem div128Quot_or_shift_ge (a b : Word) (ha : a.toNat < 2^32) :
    ((a <<< (32 : BitVec 6).toNat) ||| b).toNat ≥ a.toNat * 2^32 := by
  rw [BitVec.toNat_or]
  have h_shl : (a <<< (32 : BitVec 6).toNat).toNat = a.toNat * 2^32 := by
    rw [BitVec.toNat_shiftLeft, AddrNorm.bv6_toNat_32]
    simp only [Nat.shiftLeft_eq]
    have h_lt : a.toNat * 2^32 < 2^64 := by
      have h_pow : (2^32 : Nat) * 2^32 = 2^64 := by decide
      have h_mul_lt : a.toNat * 2^32 < 2^32 * 2^32 :=
        (Nat.mul_lt_mul_right (by omega : (0 : Nat) < 2^32)).mpr ha
      omega
    exact Nat.mod_eq_of_lt h_lt
  rw [h_shl]
  exact Nat.left_le_or

/-- **A2.S1.alg** (pure algebra): if `q1' * 2^32 + q0' ≥ u / vTop`, then
    `(q1'*2^32 + q0' + 1) * vTop > u`. Wraps `Nat.div` semantics.

    Used downstream to convert the "tight qHat" statement (qHat ≥ q_true)
    into the "gap" statement (qHat + 1 > q_true), which is what A2 asks. -/
theorem nat_succ_mul_gt_of_div_le (q u vTop : Nat) (hvTop_pos : 0 < vTop)
    (h_div_le : u / vTop ≤ q) :
    (q + 1) * vTop > u := by
  have h_div_mod : u = vTop * (u / vTop) + u % vTop := (Nat.div_add_mod u vTop).symm
  have h_mod_lt : u % vTop < vTop := Nat.mod_lt u hvTop_pos
  have h_mul : vTop * (u / vTop) ≤ vTop * q := Nat.mul_le_mul_left _ h_div_le
  calc u = vTop * (u / vTop) + u % vTop := h_div_mod
    _ ≤ vTop * q + u % vTop := by omega
    _ < vTop * q + vTop := by omega
    _ = (q + 1) * vTop := by ring

/-- **A2.S1.comp** (pure algebra): tight per-halfword combine.
    If `q1' ≥ q_true_1` AND `q0' ≥ q_true_0` AND `q0' < 2^32` AND
    `q_true_0 < 2^32`, then `q1'*2^32 + q0' ≥ q_true_1*2^32 + q_true_0`.
    Used to combine Phase 1 and Phase 2 tight bounds into the halfword
    `qHat ≥ q_true` bound. -/
theorem halfword_combine_ge_of_tight (q1' q0' q_true_1 q_true_0 : Nat)
    (h_q1'_ge : q1' ≥ q_true_1)
    (h_q0'_ge : q0' ≥ q_true_0) :
    q1' * 2^32 + q0' ≥ q_true_1 * 2^32 + q_true_0 := by
  have h1 : q_true_1 * 2^32 ≤ q1' * 2^32 := Nat.mul_le_mul_right _ h_q1'_ge
  exact Nat.add_le_add h1 h_q0'_ge

/-- **A2.S1.div_id** (pure Nat): two-step schoolbook division identity.
    `(A*2^64 + a1*2^32 + a0) / V = ((A*2^32+a1)/V)*2^32 + ((rem*2^32+a0)/V)`
    where `rem = (A*2^32+a1) % V`. This is the halfword-pair decomposition of
    the 128-bit division, showing that successive halfword divisions recover
    the true quotient. Foundational for the Knuth-B tight-phases reduction. -/
theorem two_step_div_identity (A a1 a0 V : Nat) (hV_pos : 0 < V) :
    (A * 2^64 + a1 * 2^32 + a0) / V =
    ((A * 2^32 + a1) / V) * 2^32 +
    ((((A * 2^32 + a1) % V) * 2^32 + a0) / V) := by
  set q1 := (A * 2^32 + a1) / V with hq1_def
  set r1 := (A * 2^32 + a1) % V with hr1_def
  set q0 := (r1 * 2^32 + a0) / V with hq0_def
  set r0 := (r1 * 2^32 + a0) % V with hr0_def
  have h_decomp_1 : A * 2^32 + a1 = V * q1 + r1 := (Nat.div_add_mod _ V).symm
  have h_decomp_0 : r1 * 2^32 + a0 = V * q0 + r0 := (Nat.div_add_mod _ V).symm
  have h_r0_lt : r0 < V := Nat.mod_lt _ hV_pos
  have h_full : A * 2^64 + a1 * 2^32 + a0 = r0 + (q1 * 2^32 + q0) * V := by
    calc A * 2^64 + a1 * 2^32 + a0
        = (A * 2^32 + a1) * 2^32 + a0 := by ring
      _ = (V * q1 + r1) * 2^32 + a0 := by rw [h_decomp_1]
      _ = V * q1 * 2^32 + (r1 * 2^32 + a0) := by ring
      _ = V * q1 * 2^32 + (V * q0 + r0) := by rw [h_decomp_0]
      _ = r0 + (q1 * 2^32 + q0) * V := by ring
  rw [h_full, Nat.add_mul_div_right _ _ hV_pos, Nat.div_eq_of_lt h_r0_lt,
      Nat.zero_add]

/-- **Wrapped Phase 1b lower bound** (parallel to
    `algorithmQ1Prime_le_q_true_1_plus_two` for the upper direction).

    `(algorithmQ1Prime u4 u3 b3').toNat + 2 ≥ u4.toNat / dHi.toNat`.
    Wraps KB-2 (`div128Quot_phase1b_quotient_bound`) into the algorithmQ1Prime
    bundle, exposing the Phase 1b Nat-level lower bound to downstream callers. -/
theorem algorithmQ1Prime_ge_q1_dHi_minus_two
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63) :
    (algorithmQ1Prime u4 u3 b3').toNat + 2 ≥
      u4.toNat / (b3' >>> (32 : BitVec 6).toNat).toNat := by
  set dHi := b3' >>> (32 : BitVec 6).toNat with hdHi_def
  set dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat with hdLo_def
  set div_un1 := u3 >>> (32 : BitVec 6).toNat with hdiv_un1_def
  have h_dHi_lt : dHi.toNat < 2^32 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ne : dHi ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [← hdHi_def, heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  rw [algorithmQ1Prime_unfold]
  simp only []
  let rhatUn1 : Word := (((if (rv64_divu u4 dHi) >>> (32 : BitVec 6).toNat = 0
      then u4 - rv64_divu u4 dHi * dHi
      else u4 - rv64_divu u4 dHi * dHi + dHi) <<< (32 : BitVec 6).toNat)
      ||| div_un1)
  exact (div128Quot_phase1b_quotient_bound u4 dHi h_dHi_ne h_dHi_lt
    dLo rhatUn1).1

/-- **q_true_1 < 2^32**: pure Nat helper. Under `u4 < b3'` and `a1 < 2^32`,
    `(u4 * 2^32 + a1) / b3' < 2^32`. Used by the wide-u4 no-undershoot
    sub-cases to bound q_true_1 against the algorithm's q1'. -/
theorem q_true_1_lt_pow32 (u4 a1 b3' : Nat)
    (hu4 : u4 < b3') (ha1 : a1 < 2^32) :
    (u4 * 2^32 + a1) / b3' < 2^32 := by
  apply Nat.div_lt_of_lt_mul
  -- Need: u4 * 2^32 + a1 < b3' * 2^32.
  have h_u4_mul : u4 * 2^32 + 2^32 ≤ b3' * 2^32 := by
    have : u4 + 1 ≤ b3' := hu4
    calc u4 * 2^32 + 2^32 = (u4 + 1) * 2^32 := by ring
      _ ≤ b3' * 2^32 := Nat.mul_le_mul_right _ this
  omega

/-- **A2.S1.body** (pure Nat + abstract phase hypotheses): if the algorithm's
    qHat decomposes as `q1'*2^32 + q0'` (halfword combine output) AND the
    phase-wise tight bounds `q_true_1 ≤ q1'` and `q_true_0 ≤ q0'` hold AND
    the halfword division identity ties `q_true_1`, `q_true_0` to the true
    128/64 quotient, then A2's conclusion follows.

    This is the clean "last-mile" composition: given the phase tight bounds
    abstractly, derive `(qHat+1)*vTop > u`. Pure Nat — doesn't touch the
    algorithm's let-chains. -/
theorem qHat_plus_one_gt_u_via_tight_phases
    (u q1' q0' q_true_1 q_true_0 V : Nat)
    (hV_pos : 0 < V)
    (h_qHat_decomp : u / V = q_true_1 * 2^32 + q_true_0)
    (h_ph1 : q_true_1 ≤ q1')
    (h_ph2 : q_true_0 ≤ q0') :
    (q1' * 2^32 + q0' + 1) * V > u := by
  have h_ge : u / V ≤ q1' * 2^32 + q0' := by
    rw [h_qHat_decomp]
    exact halfword_combine_ge_of_tight q1' q0' q_true_1 q_true_0 h_ph1 h_ph2
  exact nat_succ_mul_gt_of_div_le (q1' * 2^32 + q0') u V hV_pos h_ge

/-- **A2.S1**: Case "normal" — when `un21 < dHi*2^32` (Phase 2 Case A),
    both Phase 1 and Phase 2 tight bounds from existing infrastructure apply
    directly.

    Takes the stricter `un21 < dHi*2^32` as hypothesis (stronger than
    `un21 < vTop`), which covers exactly the region where
    `div128Quot_q0_prime_ge_q_true_0_of_un21_lt_dHi_mul_pow32` is applicable.

    **Sub-decomposition**: closes via:
    1. A2.S1.q1_eq_true_1: `q1'.toNat = q_true_1` (Phase 1 tight).
    2. A2.S1.un21_eq_true_rem: algorithm un21 = mathematical remainder.
    3. Phase 2 tight `_of_un21_lt_dHi_mul_pow32` (applies directly).
    4. `two_step_div_identity` + `qHat_plus_one_gt_u_via_tight_phases`.

    **TODO**: ~100 lines. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_normal
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  -- Standard precondition derivations.
  have hb3'_pos : 0 < b3'.toNat := by omega
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_vTop_decomp : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  -- u3 halfword split: u3 = div_un1 * 2^32 + div_un0
  -- where div_un1 = u3 >>> 32 (high 32 bits), div_un0 = u3 % 2^32 (low 32 bits).
  have h_u3_decomp : u3.toNat =
      (u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp u3
  -- div_un1 and div_un0 bounds.
  have h_div_un1_lt :
      (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un0_lt :
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (u3 <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (u3 <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  -- All Phase tight bounds + halfword decomp via the wrapped lemmas.
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    Nat.lt_of_lt_of_le hu4_lt_dHi_pow32 (Nat.le_add_right _ _)
  have h_un21_lt_vTop : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    Nat.lt_of_lt_of_le h_un21_lt_dHi_pow32 (Nat.le_add_right _ _)
  -- Phase 1 tight (wrapped).
  have h_ph1_tight :=
    algorithmQ1Prime_ge_q_true_1 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt_dHi_pow32 h_u4_lt_vTop
  -- Phase 2 tight (wrapped).
  have h_ph2_tight :=
    algorithmQ0Prime_ge_q_true_0 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt h_un21_lt_dHi_pow32 h_un21_lt_vTop
  -- q0' < 2^32 (wrapped form — derive via algorithmQ0Prime_unfold).
  have h_q0'_lt : (algorithmQ0Prime u4 u3 b3').toNat < 2^32 := by
    rw [algorithmQ0Prime_unfold]
    exact
      div128Quot_q0_prime_lt_pow32 (algorithmUn21 u4 u3 b3')
        (b3' >>> (32 : BitVec 6).toNat)
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) u3
        h_dHi_ge h_dHi_lt h_dLo_lt h_un21_lt_vTop
  -- qHat halfword decomp (wrapped).
  have h_qHat_decomp :=
    div128Quot_toNat_eq_algorithmQ1_Q0 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt
      (by rw [h_vTop_decomp] at hu4_lt_b3'; exact hu4_lt_b3') h_q0'_lt
  -- True-quotient halfword decomposition.
  have h_two_step :=
    two_step_div_identity u4.toNat
      (u3 >>> (32 : BitVec 6).toNat).toNat
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
      b3'.toNat hb3'_pos
  -- Bridge: algorithm un21 ≥ r1_math.
  have h_un21_ge_rmath :=
    algorithmUn21_ge_r1_math u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  -- Monotonicity: lift Phase 2 tight from algorithm un21 to r1_math.
  have h_mono_num :
      (u4.toNat * 2 ^ 32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2 ^ 32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat ≤
      (algorithmUn21 u4 u3 b3').toNat * 2 ^ 32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul_right _ h_un21_ge_rmath
  have h_q_true_0_le :
      ((u4.toNat * 2 ^ 32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2 ^ 32 +
       ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
       ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
      (algorithmQ0Prime u4 u3 b3').toNat :=
    Nat.le_trans (Nat.div_le_div_right h_mono_num) h_ph2_tight
  -- Rewrite goal.
  rw [h_u3_decomp, h_qHat_decomp]
  have h_u_rewrite : u4.toNat * 2^64 +
      ((u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
       ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) =
      u4.toNat * 2^64 +
        (u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by ring
  rw [h_u_rewrite]
  -- Use h_vTop_decomp to normalize b3'.
  have h_v_eq := h_vTop_decomp.symm
  rw [h_v_eq] at h_q_true_0_le
  -- Normalize h_two_step and h_ph1_tight by converting divisor b3' ↔ decomp.
  rw [← h_vTop_decomp] at h_ph1_tight
  -- Apply the final composition.
  apply qHat_plus_one_gt_u_via_tight_phases _ _ _ _ _ _ hb3'_pos h_two_step h_ph1_tight
  exact h_q_true_0_le

/-- **A2.S2 helper: q1' overshoot closes the goal**. Under standard hyps +
    `q1' ≥ q_true_1 + 1`, the (qHat+1)*b3' > u inequality holds via the
    OR-shift trick (div128Quot.toNat ≥ q1'*2^32 > q_true_full).

    Generalized to handle q1' ∈ {q_true_1 + 1, q_true_1 + 2, ...}. Used by:
    - `_wide_un21_wide` (un21 ≥ V forces Phase 1 false-alarm = +1).
    - `_wide_un21_narrow` (off-by-one sub-case).
    - `_narrow_u4_*` (overshoot sub-cases via the +2 weak upper bound). -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_overshoot
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (h_q1_ge : (algorithmQ1Prime u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 1) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  -- Standard preconditions.
  have hb3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un0_lt :
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (u3 <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (u3 <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un1_lt :
      (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u3_decomp : u3.toNat =
      (u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp u3
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]; exact hu4_lt_b3'
  -- algorithmQ1Prime.toNat < 2^32.
  have h_q1_lt : (algorithmQ1Prime u4 u3 b3').toNat < 2^32 := by
    rw [algorithmQ1Prime_unfold]
    exact div128Quot_q1_prime_lt_pow32 u4 (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) u3
      h_dHi_ge h_dHi_lt h_dLo_lt h_u4_lt_vTop
  -- div128Quot expressed via the algorithm wrappers.
  have h_div128_eq : div128Quot u4 u3 b3' =
      (algorithmQ1Prime u4 u3 b3') <<< (32 : BitVec 6).toNat |||
      algorithmQ0Prime u4 u3 b3' := by
    unfold div128Quot
    rw [algorithmQ1Prime_unfold, algorithmQ0Prime_unfold]
    simp only [algorithmUn21_unfold]
  -- OR-shift lower bound: div128Quot.toNat ≥ q1' * 2^32.
  have h_div128_ge : (div128Quot u4 u3 b3').toNat ≥ (algorithmQ1Prime u4 u3 b3').toNat * 2^32 := by
    rw [h_div128_eq]
    exact div128Quot_or_shift_ge _ _ h_q1_lt
  -- Use q1' ≥ q_true_1 + 1 to get div128Quot.toNat ≥ (q_true_1 + 1) * 2^32.
  set q_true_1 := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
    with hq_true_1_def
  have h_div128_ge' :
      (div128Quot u4 u3 b3').toNat ≥ (q_true_1 + 1) * 2^32 := by
    have h_step : (algorithmQ1Prime u4 u3 b3').toNat * 2^32 ≥ (q_true_1 + 1) * 2^32 :=
      Nat.mul_le_mul_right _ h_q1_ge
    linarith [h_div128_ge, h_step]
  -- Now h_div128_ge: div128Quot.toNat ≥ (q_true_1 + 1) * 2^32.
  -- Apply two_step_div_identity (after rewriting u3 = a1*2^32 + a0).
  set a1 := (u3 >>> (32 : BitVec 6).toNat).toNat with ha1_def
  set a0 := ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat with ha0_def
  have h_u3_eq : u3.toNat = a1 * 2^32 + a0 := h_u3_decomp
  have h_two_step_raw :=
    two_step_div_identity u4.toNat a1 a0 b3'.toNat hb3'_pos
  have h_two_step : (u4.toNat * 2^64 + u3.toNat) / b3'.toNat =
      ((u4.toNat * 2^32 + a1) / b3'.toNat) * 2^32 +
      (((u4.toNat * 2^32 + a1) % b3'.toNat * 2^32 + a0) / b3'.toNat) := by
    rw [h_u3_eq]
    have h_combine : u4.toNat * 2^64 + (a1 * 2^32 + a0) =
        u4.toNat * 2^64 + a1 * 2^32 + a0 := by ring
    rw [h_combine]
    exact h_two_step_raw
  -- q_true_0 < 2^32: numerator ≤ b3'*2^32 - 1, so q_true_0 ≤ 2^32 - 1.
  have h_q_true_0_lt : ((u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) %
      b3'.toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat < 2^32 := by
    apply Nat.div_lt_of_lt_mul
    have h_mod_lt : (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat <
        b3'.toNat := Nat.mod_lt _ hb3'_pos
    nlinarith
  -- q_true_full < (q_true_1 + 1) * 2^32 ≤ div128Quot.toNat.
  have h_q_true_0_lt' : ((u4.toNat * 2^32 + a1) % b3'.toNat * 2^32 + a0) / b3'.toNat < 2^32 := by
    show ((u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2^32 +
        ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat < 2^32
    exact h_q_true_0_lt
  have h_q_true_full_lt : (u4.toNat * 2^64 + u3.toNat) / b3'.toNat < (q_true_1 + 1) * 2^32 := by
    rw [h_two_step]
    have h_qt1 : q_true_1 = (u4.toNat * 2^32 + a1) / b3'.toNat := hq_true_1_def
    nlinarith [h_q_true_0_lt']
  -- (q_true_full + 1) * b3' > u (Nat.div semantics).
  have h_qhat_plus_one : ((u4.toNat * 2^64 + u3.toNat) / b3'.toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
    have h_dam := Nat.div_add_mod (u4.toNat * 2^64 + u3.toNat) b3'.toNat
    have h_mod_lt : (u4.toNat * 2^64 + u3.toNat) % b3'.toNat < b3'.toNat :=
      Nat.mod_lt _ hb3'_pos
    nlinarith
  -- Combine: div128Quot.toNat ≥ (q_true_1 + 1) * 2^32 > q_true_full.
  have h_div128_gt : (div128Quot u4 u3 b3').toNat > (u4.toNat * 2^64 + u3.toNat) / b3'.toNat :=
    Nat.lt_of_lt_of_le h_q_true_full_lt h_div128_ge'
  -- (div128Quot.toNat + 1) * b3' ≥ (q_true_full + 2) * b3' > u.
  have h_div128_succ : (div128Quot u4 u3 b3').toNat + 1 ≥
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat + 2 := by omega
  have h_step1 : ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat ≥
      ((u4.toNat * 2^64 + u3.toNat) / b3'.toNat + 2) * b3'.toNat :=
    Nat.mul_le_mul_right _ h_div128_succ
  linarith [h_step1, h_qhat_plus_one]
/-- **A2.S2 wide-u4 no-undershoot claim** (TODO — VACUOUS under
    top-level normalization, see RESOLUTION below).

    **RESOLUTION (2026-04-25)**: this claim and ALL its sub-cases (A, B.1,
    B.2) are VACUOUSLY TRUE in the actual call chain. The top-level
    theorem `div128Quot_call_skip_ge_val256_div_v2` enforces
    `u4 = a3 >> antiShift` with antiShift ≥ 1, giving `u4 < 2^63`.

    Combined with wide-u4 (u4 ≥ dHi*2^32) and hb3'_ge (dHi ≥ 2^31):
    - u4 ≥ dHi*2^32 ≥ 2^63 ∧ u4 < 2^63 → contradiction.

    To close: thread `u4 < 2^63` through `div128Quot_ge_q_true_normalized`
    and into this lemma's hypotheses. Then `exfalso` + omega closes.

    See `memory/project_wide_u4_no_undershoot_false_in_b2.md` for the
    full analysis.

    In wide-u4 (`u4 ≥ dHi*2^32`), Phase 1's q1' is never less than q_true_1.
    I.e., the algorithm's Phase 1b spurious-fire (under Word truncation when
    rhatc ≥ 2^32) does NOT cause undershoot in this specific regime.

    **Sketch (refined boundary analysis)**:
    - Wide-u4 has q1.toNat ≥ 2^32 (since u4 ≥ dHi*2^32), so Phase 1a fires:
      q1c.toNat = q1.toNat - 1 (Word arithmetic with signExtend12 4095 = -1).
    - q_true_1 < 2^32 strictly (since u_top < b3' * 2^32 ⟹ u_top/b3' < 2^32).
    - **Sub-case A** (q1.toNat ≥ 2^32 + 1, i.e., q1c.toNat ≥ 2^32): then
      q1c.toNat ≥ 2^32 > q_true_1. Phase 1b at most does q1' = q1c - 1, so
      q1' ≥ 2^32 - 1 ≥ q_true_1. ✓
    - **Sub-case B** (q1.toNat = 2^32 exactly, q1c.toNat = 2^32 - 1):
      requires u4 ∈ [dHi*2^32, dHi*2^32 + dHi). Then rhat = u4 - q1*dHi =
      u4 - dHi*2^32 ∈ [0, dHi), and rhatc = rhat + dHi ∈ [dHi, 2*dHi). With
      dHi < 2^32, rhatc < 2^33 (no Word truncation when rhatc < 2^32; minor
      truncation when rhatc ≥ 2^32 which only happens if rhat + dHi ≥ 2^32).
      - **B.1** (q_true_1 < 2^32 - 1, i.e., q_true_1 ≤ 2^32 - 2): then
        q1c = 2^32 - 1 > q_true_1. q1' ≥ q1c - 1 = 2^32 - 2 ≥ q_true_1. ✓
      - **B.2** (q_true_1 = 2^32 - 1 exactly): boundary case. Need to show
        Phase 1b ult check does NOT fire here. Open: requires careful Word
        arithmetic on `(rhatc << 32 | div_un1).toNat < (q1c * dLo).toNat`
        with rhatc, dLo, div_un1 in their constrained ranges.

    If this lemma holds: no-overshoot (q1' ≤ q_true_1) + no-undershoot
    (q1' ≥ q_true_1) ⟹ q1' = q_true_1 EXACTLY in all `_narrow_u4_*` paths.
    Then un21 = r1_math < vTop and the q0' < 2^32 + halfword decomp works. -/
theorem algorithmQ1Prime_ge_q_true_1_in_wide_u4
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat ≤
      (algorithmQ1Prime u4 u3 b3').toNat := by
  -- Vacuous: u4 ≥ dHi*2^32 ∧ dHi ≥ 2^31 → u4 ≥ 2^63, contradicting hu4_lt_pow63.
  exfalso
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have : u4.toNat ≥ 2^63 := by
    have h1 : (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 ≥ 2^31 * 2^32 :=
      Nat.mul_le_mul_right _ h_dHi_ge
    have h2 : (2^31 : Nat) * 2^32 = 2^63 := by decide
    omega
  -- Suppress unused-variable warnings for the no-longer-needed regime params.
  let _ := hu4_lt_b3'
  omega

/-- **Phase 2 tightness under Phase 1 exact, narrow-u4 + narrow-un21 sub-case** —
    closed via existing helpers.

    Specializes `algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1` to the
    fully-provable sub-case where both u4 < dHi*2^32 (narrow-u4) and
    un21 < dHi*2^32 (narrow-un21) hold.

    Closes via `algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1` (un21 =
    r1_math under narrow-u4) + `algorithmQ0Prime_ge_q_true_0` (Phase 2
    tightness under narrow-un21). -/
theorem algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_narrow
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_dHi : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (((u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  -- un21 = r1_math under narrow-u4 + q1' = q_true_1.
  have h_un21_eq := algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1 u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_q1_eq
  -- Standard b3' halves derivations.
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_un21_lt_vTop : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]
    have : (algorithmUn21 u4 u3 b3').toNat <
        (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 := h_un21_lt_dHi
    omega
  -- Apply existing Phase 2 tightness.
  have h_ph2 := algorithmQ0Prime_ge_q_true_0 u4 u3 b3'
    h_dHi_ge h_dHi_lt h_dLo_lt h_un21_lt_dHi h_un21_lt_vTop
  -- h_ph2 has divisor in decomposed form (dHi*2^32 + dLo); rewrite back
  -- to b3'.toNat to match the goal.
  rw [← h_v_eq] at h_ph2
  -- h_ph2 has un21.toNat as the numerator's first term; rewrite to r1_math.
  rw [h_un21_eq] at h_ph2
  exact h_ph2

/-- **Phase 2 tightness, narrow-u4 + wide-un21 + un21 < 2^63 sub-case** —
    closed via `_of_un21_lt_pow63` + un21 = r1_math (narrow-u4 variant). -/
theorem algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_wide_lt_pow63
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_pow63 : (algorithmUn21 u4 u3 b3').toNat < 2^63)
    (h_q1_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (((u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  have hb3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_un21_eq := algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1 u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_q1_eq
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  -- un21 < vTop via un21 = r1_math < b3'.
  have h_un21_lt_vTop : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq, h_un21_eq]
    exact Nat.mod_lt _ hb3'_pos
  -- Apply pow63 variant.
  have h_ph2 := algorithmQ0Prime_ge_q_true_0_of_un21_lt_pow63 u4 u3 b3'
    h_dHi_ge h_dHi_lt h_dLo_lt h_un21_lt_pow63 h_un21_lt_vTop
  rw [← h_v_eq] at h_ph2
  rw [h_un21_eq] at h_ph2
  exact h_ph2

/-- **Un21-level Phase 2 tightness — UNCONDITIONAL on un21 magnitude.**

    Parallel to `div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63` in
    `Div128KnuthLower.lean`, but DOES NOT require `un21 < 2^63`. Uses
    `_small_rhatc` in the no-truncation case (where rhat2c < 2^32 is
    derived from the outer truncation guard) and KB-LB3 in the truncation
    case (where the outer guard fires and q0' = q0c).

    This single un21-level helper is sufficient for BOTH the
    `un21 ≥ 2^63 ∧ rhat2c < 2^32` and `un21 ≥ 2^63 ∧ rhat2c ≥ 2^32`
    sub-cases, since the algorithm's Phase 2b truncation guard
    automatically routes to the right closure path. -/
theorem div128Quot_q0_prime_ge_q_true_0_un21_level
    (un21 dHi dLo uLo : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_un21_lt_vTop : un21.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    (un21.toNat * 2^32 + div_un0.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) ≤ q0'.toNat := by
  intro q0 rhat2 hi2 q0c rhat2c div_un0 q0'
  -- div_un0 < 2^32 (from `uLo << 32 >> 32`).
  have h_div_un0_lt : div_un0.toNat < 2^32 := by
    show ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h_shl : (uLo <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (uLo <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  show (un21.toNat * 2^32 + div_un0.toNat) /
         (dHi.toNat * 2^32 + dLo.toNat) ≤
       (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat
  unfold div128Quot_phase2b_q0'
  split
  · -- Guard doesn't fire (rhat2c >>> 32 = 0): helper yields no-guard check.
    -- Derive rhat2c.toNat < 2^32 from the case hypothesis directly.
    rename_i h_shift
    have h_rhat2c_lt_word : rhat2c.toNat < 2^32 := by
      have h_div : rhat2c.toNat / 2^32 = 0 := by
        have : (rhat2c >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [h_shift]; rfl
        rwa [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
             Nat.shiftRight_eq_div_pow] at this
      exact (Nat.div_eq_zero_iff.mp h_div).resolve_left (by decide)
    exact div128Quot_q1_prime_ge_q_true_1_small_rhatc un21 dHi dLo
      (uLo <<< (32 : BitVec 6).toNat)
      hdHi_ge hdHi_lt hdLo_lt h_un21_lt_vTop h_rhat2c_lt_word
  · -- Guard fires (rhat2c ≥ 2^32): helper = q0c. KB-LB3 at Phase 2.
    exact div128Quot_q1c_ge_q_true_1 un21 dHi dLo div_un0 hdHi_ne
      h_div_un0_lt h_un21_lt_vTop

/-- **Phase 2 tightness for un21 ≥ 2^63** — closed via the unconditional
    un21-level helper. Phase 2b's algorithm-level truncation guard
    (`if rhat2c >>> 32 = 0`) routes both rhat2c < 2^32 and rhat2c ≥ 2^32
    cases to their respective Knuth-B closures (`_small_rhatc` and KB-LB3). -/
theorem algorithmQ0Prime_ge_q_true_0_of_un21_ge_pow63
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (h_un21_ge_pow63 : (algorithmUn21 u4 u3 b3').toNat ≥ 2^63)
    (h_un21_lt_vTop :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    ((algorithmUn21 u4 u3 b3').toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  let _ := h_un21_ge_pow63
  rw [algorithmQ0Prime_unfold]
  exact div128Quot_q0_prime_ge_q_true_0_un21_level
    (algorithmUn21 u4 u3 b3')
    (b3' >>> (32 : BitVec 6).toNat)
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    u3
    hdHi_ge hdHi_lt hdLo_lt h_un21_lt_vTop

/-- **Phase 2 tightness, narrow-u4 + wide-un21 + un21 ≥ 2^63 sub-case** —
    closed via composition of the shared `_of_un21_ge_pow63` stub with the
    narrow-u4 un21 = r1_math helper. -/
theorem algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_wide_ge_pow63
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_pow63 : (algorithmUn21 u4 u3 b3').toNat ≥ 2^63)
    (h_q1_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (((u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  have hb3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_un21_eq := algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1 u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_q1_eq
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_un21_lt_vTop : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq, h_un21_eq]
    exact Nat.mod_lt _ hb3'_pos
  have h_ph2 := algorithmQ0Prime_ge_q_true_0_of_un21_ge_pow63 u4 u3 b3'
    h_dHi_ge h_dHi_lt h_dLo_lt h_un21_ge_pow63 h_un21_lt_vTop
  rw [← h_v_eq] at h_ph2
  rw [h_un21_eq] at h_ph2
  exact h_ph2

/-- **Phase 2 tightness, narrow-u4 + wide-un21 sub-case** — closed via
    dispatch on un21 vs 2^63. -/
theorem algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_wide
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_dHi : (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (((u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  let _ := h_un21_ge_dHi
  by_cases h : (algorithmUn21 u4 u3 b3').toNat < 2^63
  · exact algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_wide_lt_pow63
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h h_q1_eq
  · push Not at h
    exact algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_wide_ge_pow63
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h h_q1_eq

/-- **A2.S2 Phase 2 tightness under Phase 1 exact** — closed via 2x2 dispatch.

    Under exact Phase 1 (`q1' = q_true_1`), Phase 2's `q0'` satisfies
    Phase 2 tightness: `q0' ≥ q_true_0` where
    `q_true_0 = (r1_math * 2^32 + a0) / b3'`.

    **Closure path** (4-way 2x2 case-split on u4 regime × un21 regime):
    1. **Narrow-u4 + narrow-un21** (u4 < dHi*2^32 AND un21 < dHi*2^32):
       Closes via `algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1`
       (existing) + `algorithmQ0Prime_ge_q_true_0` (existing, requires
       un21 < dHi*2^32). FULLY PROVABLE WITH EXISTING HELPERS.
    2. **Narrow-u4 + wide-un21** (u4 < dHi*2^32, un21 ∈ [dHi*2^32, vTop)):
       un21 = r1_math holds (existing) but Phase 2 tightness in wide-un21
       case requires `_of_un21_lt_pow63` and r1_math < 2^63 (NOT
       guaranteed). Hard sub-case.
    3. **Wide-u4 + any un21**: Requires the new
       `algorithmUn21_eq_r1_math_in_wide_u4_exact` stub for un21 = r1_math.
       Then same Phase 2 tightness analysis as cases 1/2.

    The cleanest decomposition is by un21 regime (narrow vs wide) since the
    Phase 2 tightness stratifies along that boundary. -/
theorem algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63)
    (h_q1_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (((u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  by_cases hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · -- Narrow-u4: dispatch on un21 regime.
    by_cases h_un21_lt : (algorithmUn21 u4 u3 b3').toNat <
        (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
    · exact algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_narrow
        u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt h_un21_lt h_q1_eq
    · push Not at h_un21_lt
      exact algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1_narrow_wide
        u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt h_un21_lt h_q1_eq
  · -- Wide-u4: VACUOUS via hu4_lt_pow63 (u4 ≥ dHi*2^32 ≥ 2^63 ∧ u4 < 2^63).
    exfalso
    push Not at hu4_lt
    have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
    have h1 : (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 ≥ 2^31 * 2^32 :=
      Nat.mul_le_mul_right _ h_dHi_ge
    have h2 : (2^31 : Nat) * 2^32 = 2^63 := by decide
    let _ := hu4_lt_b3'
    let _ := h_q1_eq
    omega

/-- **A2.S2 un21 < vTop under no-overshoot, narrow-u4 case** — closed via
    the existing contrapositive bridge `algorithmQ1Prime_eq_q_true_1_plus_one_of_un21_ge_vTop`. -/
theorem algorithmUn21_lt_vTop_of_q1_prime_not_overshoot_hu4_lt
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (algorithmUn21 u4 u3 b3').toNat < b3'.toNat := by
  by_contra h_un21_ge
  push Not at h_un21_ge
  have h_q1_eq := algorithmQ1Prime_eq_q_true_1_plus_one_of_un21_ge_vTop u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt h_un21_ge
  omega

theorem algorithmUn21_lt_vTop_of_q1_prime_not_overshoot_hu4_ge
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (hu4_lt_pow63 : u4.toNat < 2^63)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (algorithmUn21 u4 u3 b3').toNat < b3'.toNat := by
  -- Vacuous: hu4_ge ∧ hb3'_ge → u4 ≥ 2^63, contradicting hu4_lt_pow63.
  exfalso
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h1 : (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 ≥ 2^31 * 2^32 :=
    Nat.mul_le_mul_right _ h_dHi_ge
  have h2 : (2^31 : Nat) * 2^32 = 2^63 := by decide
  let _ := hu4_lt_b3'
  let _ := h_q1_le
  omega

/-- **A2.S2 Phase 2 deficit compensation** — closed via composition.

    Strategy: derive `q1' = q_true_1` (exact Phase 1) from no-overshoot +
    no-undershoot, then apply Phase 2 tightness sub-stub
    (`algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1`). The deficit
    `q_true_full - q1' * 2^32` reduces to `q_true_0` via the two-step
    division identity.

    The no-undershoot piece case-splits on hu4_lt vs hu4_ge:
    - hu4_lt: existing `algorithmQ1Prime_ge_q_true_1` from QuotientBounds.
    - hu4_ge: NEW `algorithmQ1Prime_ge_q_true_1_in_wide_u4` (sorry stub).
    Combined with the no-overshoot hypothesis, q1' = q_true_1 EXACTLY. -/
theorem algorithmQ0Prime_compensates_phase1_deficit
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (algorithmQ0Prime u4 u3 b3').toNat ≥
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat -
      (algorithmQ1Prime u4 u3 b3').toNat * 2^32 := by
  -- Standard derivations.
  have hb3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]; exact hu4_lt_b3'
  -- No-undershoot via case-split on u4 regime.
  have h_q1_ge : (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat ≤
      (algorithmQ1Prime u4 u3 b3').toNat := by
    by_cases hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
    · -- Narrow-u4: existing helper from QuotientBounds.
      have h := algorithmQ1Prime_ge_q_true_1 u4 u3 b3'
        h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt h_u4_lt_vTop
      rw [← h_v_eq] at h; exact h
    · -- Wide-u4: closed VACUOUSLY via hu4_lt_pow63.
      push Not at hu4_lt
      exact algorithmQ1Prime_ge_q_true_1_in_wide_u4 u4 u3 b3'
        hb3'_ge hu4_lt_b3' hu4_lt hu4_lt_pow63
  -- No-overshoot + no-undershoot → q1' = q_true_1 (exact).
  have h_q1_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat := by
    omega
  -- Phase 2 tightness under exact: q0' ≥ q_true_0.
  have h_q0_ge := algorithmQ0Prime_ge_q_true_0_of_q1_prime_eq_q_true_1
    u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63 h_q1_eq
  -- Two-step division identity: q_true_full = q_true_1 * 2^32 + q_true_0.
  have h_two_step :=
    two_step_div_identity u4.toNat
      (u3 >>> (32 : BitVec 6).toNat).toNat
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
      b3'.toNat hb3'_pos
  have h_u3_decomp : u3.toNat =
      (u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp u3
  -- Combine: q0' ≥ q_true_0 = q_true_full - q_true_1 * 2^32 = q_true_full - q1' * 2^32.
  rw [h_u3_decomp, show
    u4.toNat * 2^64 +
    ((u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
     ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) =
    u4.toNat * 2^64 +
    (u3 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
    ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat from by ring,
    h_two_step]
  omega

/-- **A2.S2 un21 < vTop under no-overshoot** — closed via case-split.

    Under no-overshoot at Phase 1 (`q1' ≤ q_true_1`), the algorithm's un21
    satisfies `un21 < vTop = b3'.toNat`. This is the standard Knuth-B
    invariant for Phase 2's input being well-formed.

    Composes the two case-specific helpers (narrow-u4 closed via the
    contrapositive bridge, wide-u4 stubbed). -/
theorem algorithmUn21_lt_vTop_of_q1_prime_not_overshoot
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (algorithmUn21 u4 u3 b3').toNat < b3'.toNat := by
  by_cases hu4 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact algorithmUn21_lt_vTop_of_q1_prime_not_overshoot_hu4_lt u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4 h_q1_le
  · push Not at hu4
    exact algorithmUn21_lt_vTop_of_q1_prime_not_overshoot_hu4_ge u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4 hu4_lt_pow63 h_q1_le

/-- **A2.S2 q0' < 2^32 under no-overshoot** — closed via composition.

    Composes `algorithmUn21_lt_vTop_of_q1_prime_not_overshoot` (un21 < vTop)
    with the existing `div128Quot_q0_prime_lt_pow32` algorithm-correctness
    bound. The OR-shift halfword decomposition uses this to combine
    `q1' * 2^32` and `q0'` cleanly. -/
theorem algorithmQ0Prime_lt_pow32_of_q1_prime_not_overshoot
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (algorithmQ0Prime u4 u3 b3').toNat < 2^32 := by
  -- Standard derivations (b3' halves).
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  -- un21 < vTop (sub-lemma stub).
  have h_un21_lt_vTop := algorithmUn21_lt_vTop_of_q1_prime_not_overshoot
    u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63 h_q1_le
  rw [h_v_eq] at h_un21_lt_vTop
  -- Apply existing algorithm-correctness bound.
  rw [algorithmQ0Prime_unfold]
  exact div128Quot_q0_prime_lt_pow32 (algorithmUn21 u4 u3 b3')
    (b3' >>> (32 : BitVec 6).toNat)
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) u3
    h_dHi_ge h_dHi_lt h_dLo_lt h_un21_lt_vTop

/-- **A2.S2 global Phase 1+2 compensation lemma** — closed via composition.

    Under no-overshoot at Phase 1 (`q1' ≤ q_true_1`), Phase 2's `q0'`
    compensates so the combined `div128Quot.toNat` is at least the true
    quotient. Composes:
    - `algorithmQ0Prime_compensates_phase1_deficit` (q0' ≥ q_true_full - q1'*2^32)
    - `algorithmQ0Prime_lt_pow32_of_q1_prime_not_overshoot` (q0' < 2^32)
    - `div128Quot_toNat_eq_algorithmQ1_Q0` (halfword decomposition of div128Quot)
    + Nat algebra (omega).

    Per-phase tightness genuinely FAILS in this regime when `rhatc ≥
    2^32` and Phase 1b correction fires — see
    `memory/project_a2s2_per_phase_tightness_fails.md`. The remaining
    work is concentrated in the two sub-lemmas above. -/
theorem div128Quot_ge_q_true_full_of_q1_prime_not_overshoot
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat ≤ (div128Quot u4 u3 b3').toNat := by
  -- Standard hyp derivations (b3' halves and vTop decomposition).
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]; exact hu4_lt_b3'
  -- q0' < 2^32 (sub-lemma stub).
  have h_q0_lt := algorithmQ0Prime_lt_pow32_of_q1_prime_not_overshoot
    u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63 h_q1_le
  -- Halfword decomposition: div128Quot.toNat = q1' * 2^32 + q0'.
  have h_decomp := div128Quot_toNat_eq_algorithmQ1_Q0 u4 u3 b3'
    h_dHi_ge h_dHi_lt h_dLo_lt h_u4_lt_vTop h_q0_lt
  -- Phase 2 deficit compensation: q0' ≥ q_true_full - q1' * 2^32.
  have h_compensation := algorithmQ0Prime_compensates_phase1_deficit
    u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63 h_q1_le
  -- Combine via Nat algebra.
  omega

/-- **A2.S2 shared not-overshoot helper** — 3-line composition of the
    global Phase 1+2 compensation lemma + `nat_succ_mul_gt_of_div_le`. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_not_overshoot
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  have hb3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_div_ge := div128Quot_ge_q_true_full_of_q1_prime_not_overshoot
    u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63 h_q1_le
  exact nat_succ_mul_gt_of_div_le _ _ _ hb3'_pos h_div_ge

/-- **A2.S2.narrow_u4_tight_un21**: hu4_ge regime (Phase 1a corrects, hi1 ≠ 0)
    AND un21 < dHi*2^32 (Phase 2 narrow path).

    **Decomposition via q1' upper bound + case-split**:
    - From `algorithmQ1Prime_le_q_true_1_plus_two` (now generalized): q1' ≤ q_true_1 + 2.
    - From `div128Quot_q1_prime_lt_pow32`: q1' < 2^32.
    - So q1' ∈ {q_true_1, q_true_1 + 1, q_true_1 + 2} (in the relevant range).
    - Sub-cases q1' ≥ q_true_1 + 1 (overshoot): closed via `_of_q1_prime_overshoot`.
    - Sub-case q1' = q_true_1 (exact): genuinely hard, requires Phase 2 tight
      under hu4_ge regime. Stubbed.
    - Sub-case q1' < q_true_1: undershoot, ruled out by Knuth-B (TODO: prove). -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_tight_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  -- Upper bound q1' ≤ q_true_1 + 2 (now applies to narrow_u4 regime).
  have h_q1_le_2 := algorithmQ1Prime_le_q_true_1_plus_two u4 u3 b3' hb3'_ge hu4_lt_b3'
  set q_true_1 := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
  -- Case-split on q1' ≥ q_true_1 + 1 (overshoot) vs q1' ≤ q_true_1 (exact/undershoot).
  by_cases h_overshoot : (algorithmQ1Prime u4 u3 b3').toNat ≥ q_true_1 + 1
  · -- Overshoot: directly apply the helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' h_overshoot
  · -- q1' ≤ q_true_1. Delegate to the shared not-overshoot helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_not_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_pow63 (by omega)

/-- **A2.S2.narrow_u4_wide_un21**: hu4_ge regime AND un21 ≥ dHi*2^32.

    **Decomposition via q1' upper bound + case-split** (same as
    `_narrow_u4_tight_un21`):
    - q1' ≤ q_true_1 + 2 (from generalized weak upper bound).
    - Sub-case q1' ≥ q_true_1 + 1 (overshoot): closed via
      `_of_q1_prime_overshoot`.
    - Sub-case q1' ≤ q_true_1: per-phase tightness FAILS under narrow_u4
      (see `memory/project_a2s2_per_phase_tightness_fails.md`). Needs
      global Phase 1+2 compensation. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_wide_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  set q_true_1 := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
  by_cases h_overshoot : (algorithmQ1Prime u4 u3 b3').toNat ≥ q_true_1 + 1
  · -- Overshoot: directly apply the helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' h_overshoot
  · -- q1' ≤ q_true_1. Delegate to the shared not-overshoot helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_not_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_pow63 (by omega)

/-- **A2.S2.narrow_u4**: compensation case when `u4 ≥ dHi*2^32`.
    Dispatches to tight-un21 / wide-un21 sub-cases.

    Note: `hu4_ge` is no longer needed in the body (the sub-cases delegate
    to the shared overshoot/not-overshoot helpers, which work uniformly
    over all standard hyps). The "narrow_u4" name persists because this
    is the dispatcher path taken by `_compensation` under that regime. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_tight_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_wide_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63

/-- **A2.S2.wide_un21_narrow**: Phase 1 narrow-u4 (no Phase 1a correction) AND
    un21 ∈ [dHi*2^32, vTop) (Phase 2 wide range, before Phase 1 false-alarm).

    **Decomposition via q1' case-split**:
    - q1' = q_true_1 + 1 (off-by-one): closes via the `_of_q1_prime_overshoot`
      helper (same OR-shift trick as `_wide_un21_wide`).
    - q1' = q_true_1 (exact): un21 = r1_math, so r1_math ∈ [dHi*2^32, V).
      This is the genuinely hard Phase 2 tight-bound regime under
      un21 ≥ dHi*2^32 (Phase 2a corrects, Phase 2b may false-positive).
      Stubbed for now. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_narrow
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  -- Phase 1 q1' ∈ {q_true_1, q_true_1 + 1} (always, under standard hyps).
  have h_q1_le := algorithmQ1Prime_le_q_true_1_plus_one u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq := div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    Nat.lt_of_lt_of_le hu4_lt (Nat.le_add_right _ _)
  have h_q1_ge : (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
      ≤ (algorithmQ1Prime u4 u3 b3').toNat := by
    have h := algorithmQ1Prime_ge_q_true_1 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt h_u4_lt_vTop
    rw [← h_v_eq] at h; exact h
  set q_true_1 := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
  have h_q1_or : (algorithmQ1Prime u4 u3 b3').toNat = q_true_1 ∨
                 (algorithmQ1Prime u4 u3 b3').toNat = q_true_1 + 1 := by omega
  rcases h_q1_or with h_eq | h_eq_plus_one
  · -- Sub-case A: exact q1' = q_true_1. Delegate to the shared
    -- not-overshoot helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_not_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_pow63 (by omega)
  · -- Sub-case B: off-by-one q1' = q_true_1 + 1. Use the OR-shift helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' (by omega)


/-- **A2.S2.wide_un21_wide**: Phase 1 narrow-u4 AND un21 ≥ vTop. Closes via
    the contrapositive bridge (un21 ≥ V → q1' = q_true_1 + 1) +
    `_of_q1_prime_overshoot`. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_wide
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_vTop : (algorithmUn21 u4 u3 b3').toNat ≥ b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  have h_q1_eq := algorithmQ1Prime_eq_q_true_1_plus_one_of_un21_ge_vTop u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt h_un21_ge_vTop
  exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_overshoot u4 u3 b3'
    hb3'_ge hu4_lt_b3' (by omega)

/-- **A2.S2.wide_un21**: compensation case when `u4 < dHi*2^32` but
    `un21 ≥ dHi*2^32`. Dispatches to narrow/wide sub-cases.

    Note: `h_un21_ge` is no longer needed in the body (the un21 ≥ V
    sub-case uses `_of_q1_prime_overshoot` via the contrapositive bridge,
    and the un21 < V sub-case delegates to the shared not-overshoot
    helper). The "wide_un21" name persists because this is the dispatcher
    path taken by `_compensation` under that regime. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat < b3'.toNat
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_narrow
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt hu4_lt_pow63
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_wide
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt (by omega)

/-- **A2.S2**: Case "compensation" — when `u4 ≥ dHi*2^32 ∨ un21 ≥ dHi*2^32`.
    Dispatches to `_narrow_u4` or `_wide_un21` sub-cases.

    **Status (2026-04-25)**: 1 sorry remains, in the shared helper
    `_of_q1_prime_not_overshoot` — which is the consolidation of the 3
    previous deep exact-case sorries (`_narrow_u4_tight_un21`,
    `_narrow_u4_wide_un21`, `_wide_un21_narrow`'s exact case).

    The single remaining sorry requires GLOBAL Phase 1+2 compensation
    rather than per-phase tightness — the per-phase approach genuinely
    fails under Word truncation when rhatc/rhat2c ≥ 2^32 (see
    `memory/project_a2s2_per_phase_tightness_fails.md`).

    The OVERSHOOT half of all 4 A2.S2 sub-cases is closed via the
    `_of_q1_prime_overshoot` helper (OR-shift trick). -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_compensation
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases hu4 : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4 u4 u3 b3' hb3'_ge
      hu4_lt_b3' hu4_lt_pow63
  · push Not at hu4
    exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21 u4 u3 b3' hb3'_ge
      hu4_lt_b3' hu4 hu4_lt_pow63

/-- **A2**: Knuth-B lower form (divisibility). `(qHat + 1) * b3' > u`.
    Composed via case split on `un21 < dHi*2^32` (normal) vs
    `un21 ≥ dHi*2^32` (compensation). -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h_u4 :
    u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · by_cases h_un21 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
    · exact div128Quot_qHat_plus_one_times_b3_gt_u_normal u4 u3 b3' hb3'_ge
        hu4_lt_b3' h_u4 h_un21
    · exact div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63

/-- **A4** (the §A target, derived from A2). -/
theorem div128Quot_ge_q_true_normalized
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_pow63 : u4.toNat < 2^63) :
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat ≤
      (div128Quot u4 u3 b3').toNat := by
  have hb3'_pos : 0 < b3'.toNat := by
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_core := div128Quot_qHat_plus_one_times_b3_gt_u u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb3'_pos).mpr h_core)

end EvmAsm.Evm64
