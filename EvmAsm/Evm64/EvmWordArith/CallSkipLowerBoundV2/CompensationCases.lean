/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.CompensationCases

  §A of the call-skip lower bound — the core Knuth-B compensation case
  decomposition. Shows that the algorithm's combined quotient
  `(qHat = algorithmQ1Prime * 2^32 + algorithmQ0Prime)` satisfies
  `(qHat + 1) * b3' > u`, hence `u / b3' ≤ qHat` (= `div128Quot.toNat`).

  Extracted from `CallSkipLowerBoundV2.lean` for file-size hygiene.

  ## Contents

  - **A2.S1 helpers** (pure Nat algebra):
      - `nat_succ_mul_gt_of_div_le`
      - `halfword_combine_ge_of_tight`
      - `two_step_div_identity`
      - `qHat_plus_one_gt_u_via_tight_phases`
  - **A2.S1 normal**: `_normal` (closed) — both un21 < dHi*2^32 and u4 < dHi*2^32.
  - **A2.S2 q1' helpers** (closed via OR-shift / contrapositive):
      - `_of_q1_prime_overshoot` (closed) — q1' ≥ q_true_1 + 1 case.
  - **A2.S2 q1' helpers** (currently sorry — global Phase 1+2 compensation):
      - `_of_q1_prime_not_overshoot` (sorry) — q1' ≤ q_true_1 case.
        Shared by all 3 deep exact-case sub-cases below; closure requires
        extending `KnuthTheoremB.lean` (per-phase tightness fails — see
        `memory/project_a2s2_per_phase_tightness_fails.md`).
  - **A2.S2 sub-cases** (each delegating to the q1' helpers above):
      - `_narrow_u4_tight_un21`, `_narrow_u4_wide_un21`, `_narrow_u4`
      - `_wide_un21_narrow`, `_wide_un21_wide`, `_wide_un21`
  - **A2.S2 compensation**: `_compensation` (composes the two cases above).
  - **A2 main**: `div128Quot_qHat_plus_one_times_b3_gt_u`.
  - **A4 wrapper**: `div128Quot_ge_q_true_normalized`.
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

/-- **A2.S2 shared not-overshoot helper** (TODO).

    All 3 remaining A2.S2 exact-case sorries (`_narrow_u4_tight_un21`,
    `_narrow_u4_wide_un21`, `_wide_un21_narrow`) reduce to *this single
    statement*: under standard hypotheses + `q1' ≤ q_true_1` (i.e., the
    NOT-overshoot branch of the case-split on `q1' ≥ q_true_1 + 1`),
    `(qHat + 1) * b3' > u`.

    Per-phase tightness (`q1' ≥ q_true_1 ∧ Phase-2-tight`) genuinely FAILS
    in this regime: when `rhatc ≥ 2^32` and the Phase 1b correction fires,
    Word truncation can drop `q1'` to `q_true_1 - 1` (undershoot); see
    `memory/project_a2s2_per_phase_tightness_fails.md`. Closing this
    requires extending `KnuthTheoremB.lean` with a *global* qHat ≥
    q_true_full bound — bypassing the per-phase decomposition by handling
    the carry compensation between Phase 1 and Phase 2 directly.

    Sketch: in undershoot, q1' = q_true_1 - 1, so the algorithm's effective
    "input" to Phase 2 is shifted by V (one whole quotient digit), which
    Phase 2 absorbs via Knuth-B's compensation argument. Closure requires
    a `KnuthTheoremB`-style two-phase argument that quantifies over the
    combined `(q1', q0')` pair rather than each phase separately. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_not_overshoot
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (h_q1_le : (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  -- Suppress unused-variable warnings for the placeholder.
  let _ := hb3'_ge
  let _ := hu4_lt_b3'
  let _ := h_q1_le
  sorry

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
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
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
      hb3'_ge hu4_lt_b3' (by omega)

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
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  set q_true_1 := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
  by_cases h_overshoot : (algorithmQ1Prime u4 u3 b3').toNat ≥ q_true_1 + 1
  · -- Overshoot: directly apply the helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' h_overshoot
  · -- q1' ≤ q_true_1. Delegate to the shared not-overshoot helper.
    exact div128Quot_qHat_plus_one_times_b3_gt_u_of_q1_prime_not_overshoot u4 u3 b3'
      hb3'_ge hu4_lt_b3' (by omega)

/-- **A2.S2.narrow_u4**: compensation case when `u4 ≥ dHi*2^32`.
    Dispatches to tight-un21 / wide-un21 sub-cases.

    Note: `hu4_ge` is no longer needed in the body (the sub-cases delegate
    to the shared overshoot/not-overshoot helpers, which work uniformly
    over all standard hyps). The "narrow_u4" name persists because this
    is the dispatcher path taken by `_compensation` under that regime. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_tight_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3'
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_wide_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3'

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
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
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
      hb3'_ge hu4_lt_b3' (by omega)
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
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat < b3'.toNat
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_narrow
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt
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
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases hu4 : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4 u4 u3 b3' hb3'_ge
      hu4_lt_b3'
  · push Not at hu4
    exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21 u4 u3 b3' hb3'_ge
      hu4_lt_b3' hu4

/-- **A2**: Knuth-B lower form (divisibility). `(qHat + 1) * b3' > u`.
    Composed via case split on `un21 < dHi*2^32` (normal) vs
    `un21 ≥ dHi*2^32` (compensation). -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h_u4 :
    u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · by_cases h_un21 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
    · exact div128Quot_qHat_plus_one_times_b3_gt_u_normal u4 u3 b3' hb3'_ge
        hu4_lt_b3' h_u4 h_un21
    · exact div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3'
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3'

/-- **A4** (the §A target, derived from A2). -/
theorem div128Quot_ge_q_true_normalized
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat ≤
      (div128Quot u4 u3 b3').toNat := by
  have hb3'_pos : 0 < b3'.toNat := by
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_core := div128Quot_qHat_plus_one_times_b3_gt_u u4 u3 b3' hb3'_ge hu4_lt_b3'
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb3'_pos).mpr h_core)

end EvmAsm.Evm64
