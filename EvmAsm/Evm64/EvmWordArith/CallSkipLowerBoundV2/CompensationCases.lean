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
  - **A2.S2 sub-cases** (each currently sorry):
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
      h_un21_lt_dHi_pow32
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

/-- **A2.S2.narrow_u4_tight_un21**: hu4_ge regime (Phase 1a corrects, hi1 ≠ 0)
    AND un21 < dHi*2^32 (Phase 2 narrow path).

    **Proof structure** (analogous to _normal but with adjusted Phase 1 bound):
    - Phase 1a correction: q1 ≥ 2^32 (since u4 ≥ dHi * 2^32 → u4/dHi ≥ 2^32 → hi1 ≠ 0).
    - Post-correction q1c = q1 - 1, and Phase 1b further refines.
    - The wrapped algorithmQ1Prime_ge_q_true_1 still holds, but uses a different
      version of the tight bound that accounts for u4 ≥ dHi*2^32. Need a new
      wrapper, e.g. `algorithmQ1Prime_ge_q_true_1_of_u4_ge` that handles this.
    - Phase 2 tight + halfword bridge (algorithmUn21_ge_r1_math) work the same.
    - Final composition via qHat_plus_one_gt_u_via_tight_phases.

    ~120 lines. The main blocker is the Phase 1 tight bound under hu4_ge. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_tight_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A2.S2.narrow_u4_wide_un21**: hu4_ge regime AND un21 ≥ dHi*2^32.

    **Proof structure** (the hardest sub-case):
    - Phase 1a corrects (q1c = q1 - 1).
    - Phase 2's narrow path doesn't directly apply; un21 ≥ dHi*2^32 means
      q0 = un21/dHi ≥ 2^32, hi2 ≠ 0, Phase 2a corrects: q0c = q0 - 1.
    - Phase 2b's ult check may further correct.
    - The combined Phase 1a + 2a corrections compensate for any q' overshoot
      in the qHat = q1' * 2^32 + q0' decomposition.
    - Need a Phase 2 tight bound under un21 ≥ dHi*2^32 (currently the wrapper
      assumes un21 < dHi*2^32). New wrapper needed:
      `algorithmQ0Prime_ge_q_true_0_of_un21_ge`.
    - Strategy: prove the "augmented" tight bound for the corrected q0' under
      Phase 2a correction, then the same final composition via
      qHat_plus_one_gt_u_via_tight_phases applies.

    ~150 lines. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_wide_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge : (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A2.S2.narrow_u4**: compensation case when `u4 ≥ dHi*2^32`.
    Dispatches to tight-un21 / wide-un21 sub-cases. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_tight_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_ge h
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4_wide_un21
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_ge (by omega)

/-- **A2.S2.wide_un21_narrow**: Phase 1 narrow-u4 (no Phase 1a correction) AND
    un21 ∈ [dHi*2^32, vTop) (Phase 2 wide range, before Phase 1 false-alarm).

    **Proof strategy via case-split on un21 < 2^63 vs ≥ 2^63**:
    - **Case un21 < 2^63**: directly apply
      `div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63` (KB-LB8) which only
      needs `un21 < 2^63` + `un21 < V`. This is the same pattern as _normal,
      but with the un21 < 2^63 path instead of un21 < dHi*2^32.
    - **Case un21 ≥ 2^63**: genuinely hard. Phase 2a's hi2 ≠ 0 correction
      fires, and Phase 2b's Word check may false-positive. This is the
      Knuth-B "false-alarm-on-q0'" regime that needs separate analysis.
      For now, see `memory/project_un21_lt_vTop_plan.md`.

    The case-split decomposition turns one sorry into two, but exposes the
    really-hard sub-case clearly. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_narrow
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_dHi_pow32 : (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_vTop : (algorithmUn21 u4 u3 b3').toNat < b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h_un21_lt_pow63 : (algorithmUn21 u4 u3 b3').toNat < 2^63
  · -- Sub-case A: un21 < 2^63 — KB-LB8 applies via the existing infrastructure.
    sorry
  · -- Sub-case B: un21 ≥ 2^63 — genuinely hard, Phase 2a correction + Phase 2b
    -- false-positive analysis. Not yet attempted.
    sorry

/-- **A2.S2.wide_un21_wide**: Phase 1 narrow-u4 AND un21 ≥ vTop (= b3'.toNat).

    **Mathematical observation**: un21 ≥ b3' means the Word un21 wrapped around
    AND the wrap-around result is at least V. This happens when the wrap residue
    `2^64 - V + r1_math ≥ V`, i.e., `r1_math ≥ 2V - 2^64`. With V ≥ 2^63 and
    r1_math < V, this is the regime r1_math ∈ [2V - 2^64, V).

    **Proof strategy**: Phase 1 false-alarmed (q1' = q_true_1 + 1, the off-by-one
    case from Un21Bridge). Use:
    - algorithmUn21_ge_r1_math (proven) to get un21 ≥ r1_math, then
    - the Phase 2 fall-back: q0' has wide range, but the qHat = q1'*2^32 + q0'
      still over-approximates q_true since q1' overshot by exactly 1.
    - The (qHat + 1) * b3' > u inequality follows from the global compensation:
      q_true ≤ qHat + 1 (since qHat = q1'*2^32 + q0' ≥ q_true). Hence
      (qHat + 1) * b3' ≥ (q_true + 1) * b3' > u (by Nat.div_add_mod).

    The key fact needed: q_true_full ≤ qHat. This is the core Knuth-B
    statement, which doesn't need the tight per-phase bounds — it's a global
    Phase 1+2 compensation lemma. May need a new sub-lemma
    `qHat_ge_q_true_full_of_phase1_overshoot`.

    ~150 lines. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_wide
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_vTop : (algorithmUn21 u4 u3 b3').toNat ≥ b3'.toNat) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  sorry

/-- **A2.S2.wide_un21**: compensation case when `u4 < dHi*2^32` but
    `un21 ≥ dHi*2^32`. Dispatches to narrow/wide sub-cases. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge : (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases h : (algorithmUn21 u4 u3 b3').toNat < b3'.toNat
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_narrow
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt h_un21_ge h
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21_wide
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt (by omega)

/-- **A2.S2**: Case "compensation" — when `u4 ≥ dHi*2^32 ∨ un21 ≥ dHi*2^32`.
    Dispatches to `_narrow_u4` or `_wide_un21` sub-cases. -/
theorem div128Quot_qHat_plus_one_times_b3_gt_u_compensation
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (h_compensation : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 ∨
      (algorithmUn21 u4 u3 b3').toNat ≥
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    ((div128Quot u4 u3 b3').toNat + 1) * b3'.toNat >
      u4.toNat * 2^64 + u3.toNat := by
  by_cases hu4 : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32
  · exact div128Quot_qHat_plus_one_times_b3_gt_u_narrow_u4 u4 u3 b3' hb3'_ge
      hu4_lt_b3' hu4
  · push Not at hu4
    have h_un21 : (algorithmUn21 u4 u3 b3').toNat ≥
        (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 := by
      rcases h_compensation with h | h
      · omega
      · exact h
    exact div128Quot_qHat_plus_one_times_b3_gt_u_wide_un21 u4 u3 b3' hb3'_ge
      hu4_lt_b3' hu4 h_un21

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
    · apply div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3'
      right; omega
  · apply div128Quot_qHat_plus_one_times_b3_gt_u_compensation u4 u3 b3' hb3'_ge hu4_lt_b3'
    left; omega

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
