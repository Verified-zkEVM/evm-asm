/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.WideRhatcUB

  Closes the V4 Phase-1b / Phase-2b UB chain in the **wide-rhatc** regime
  (`rhatc ≥ 2^32`), filling the dual gap left by
  `Un21BoundDHiPow32.lean` / `Q0ddUBDHiPow32.lean` (which cover the
  narrow-rhatc regime `rhatc < 2^32`, equivalently `uHi < dHi*2^32`).

  Wide-rhatc corresponds to the Case-B regime `uHi ∈ [dHi*2^32, vTop)`
  (at Phase-1) or `un21 ∈ [dHi*2^32, vTop)` (at Phase-2), where the
  first correction `q1c = q1 - 1` does not yet bring `q1c < 2^32`.

  Key observation: in wide-rhatc the Phase-1b/Phase-2b second correction
  guards do NOT fire (their `rhat'' >> 32 = 0` precondition fails), so
  the post-corrections value `q1''` (resp. `Q0dd`) is `q1c` (resp.
  `q0c`).  The Phase Euclidean identity `q1c*dHi + rhatc = uHi` then
  gives the `+1` bound on `q1c` directly via cross-multiplication:

    rhatc ≥ 2^32 →  q1c * dLo  <  rhatc * 2^32
                   →  q1c ≤ q_true_1 + 1.

  This complements (without overlapping) the existing
  `div128Quot_q1_prime_le_q_true_1_plus_one_of_uHi_lt_dHi_mul_pow32`
  closure for narrow-rhatc; together they yield a full Phase-1b UB
  closure under just normalisation + call regime, modulo the
  intermediate `q1c → q1''` correction structure (which preserves the
  `+1` bound by `q1'' ≤ q1c` whenever the guards don't reduce).
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Q0ddUBDHiPow32

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Knuth-B-level Phase-1a UB on `q1c` in the wide-rhatc regime.

    Uses the Phase-1a Euclidean identity `q1c*dHi + rhatc = uHi`, the
    `q1c ≤ 2^32` bound, and `rhatc ≥ 2^32` to close `q1c ≤ q_true_1 + 1`
    by direct cross-multiplication — no Knuth-C contrapositive needed. -/
theorem div128Quot_q1c_le_q_true_1_plus_one_of_rhatc_ge_pow32
    (uHi dHi dLo uLo : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (h_rhatc_ge :
      (let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       rhatc.toNat) ≥ 2^32) :
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
  intro div_un1 q1 hi1 q1c
  -- Phase-1a Euclidean identity.
  have h_eucl :
      q1c.toNat * dHi.toNat +
        (if hi1 = 0 then (uHi - q1 * dHi) else (uHi - q1 * dHi) + dHi).toNat =
          uHi.toNat :=
    div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  -- q1c ≤ 2^32.
  have h_q1c_le_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt huHi_lt_vTop
  -- q1c * dLo < 2^64 (q1c ≤ 2^32 and dLo < 2^32, but careful with edge q1c = 2^32).
  have h_q1c_dLo_lt : q1c.toNat * dLo.toNat < 2^64 := by
    -- q1c ≤ 2^32 and dLo ≤ 2^32 - 1 → product ≤ 2^32 * (2^32 - 1) < 2^64.
    have h_prod : q1c.toNat * dLo.toNat ≤ 2^32 * (2^32 - 1) :=
      Nat.mul_le_mul h_q1c_le_pow32 (by omega)
    have h_eq : (2^32 : Nat) * (2^32 - 1) = 2^64 - 2^32 := by decide
    omega
  -- div_un1 < 2^32.
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (uLo >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : uLo.toNat < 2^64 := uLo.isLt
    have heq64 : (2^64 : Nat) = 2^32 * 2^32 := by decide
    omega
  -- Unfold the let-chain in `h_rhatc_ge` so it sees `q1` and `hi1` from `intro`.
  simp only at h_rhatc_ge
  -- Now `h_rhatc_ge : (if hi1 = 0 then uHi - q1*dHi else uHi - q1*dHi + dHi).toNat ≥ 2^32`.
  set rhatc := (if hi1 = 0 then (uHi - q1 * dHi) else (uHi - q1 * dHi) + dHi) with hrhatc_def
  have h_rhatc_ge_nat : rhatc.toNat ≥ 2^32 := h_rhatc_ge
  -- vTop is positive.
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h_dHi_pos : 0 < dHi.toNat := by omega
    have h_pow_pos : (0 : Nat) < 2^32 := by decide
    have : 0 < dHi.toNat * 2^32 := Nat.mul_pos h_dHi_pos h_pow_pos
    exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
  -- Phase-1a Euclidean (folded form).
  have h_q1c_dHi : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat := by
    simpa [rhatc] using h_eucl
  have h_rhatc_le_uHi : rhatc.toNat ≤ uHi.toNat := by omega
  -- Case q1c = 0: trivially q1c ≤ ... + 1.
  by_cases h_q1c_zero : q1c.toNat = 0
  · rw [h_q1c_zero]; exact Nat.zero_le _
  -- Case q1c ≥ 1.  Show (q1c - 1) * vTop ≤ uHi*2^32 + div_un1.
  have h_q1c_pos : 1 ≤ q1c.toNat := Nat.pos_of_ne_zero h_q1c_zero
  have h_key :
      (q1c.toNat - 1) * (dHi.toNat * 2^32 + dLo.toNat) ≤
        uHi.toNat * 2^32 + div_un1.toNat := by
    -- Strategy: expand (q1c - 1) * vTop as q1c*vTop - vTop, then expand
    -- q1c*vTop = q1c*dHi*2^32 + q1c*dLo, use Euclidean to rewrite
    -- q1c*dHi*2^32 = uHi*2^32 - rhatc*2^32, then conclude with omega
    -- given rhatc*2^32 ≥ 2^64 ≥ q1c*dLo.
    have h_qv_expand :
        q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) =
          q1c.toNat * dHi.toNat * 2^32 + q1c.toNat * dLo.toNat := by ring
    have h_eucl_pow :
        q1c.toNat * dHi.toNat * 2^32 + rhatc.toNat * 2^32 = uHi.toNat * 2^32 := by
      have h := h_q1c_dHi
      have : (q1c.toNat * dHi.toNat + rhatc.toNat) * 2^32 = uHi.toNat * 2^32 := by
        rw [h]
      linarith
    have h_rhatc_pow_ge : rhatc.toNat * 2^32 ≥ 2^64 := by
      have h := Nat.mul_le_mul_right (2^32) h_rhatc_ge_nat
      have hpow : (2^32 : Nat) * 2^32 = 2^64 := by decide
      omega
    -- Now everything is linear in the atoms.
    -- (q1c - 1) * vTop = q1c * vTop - vTop, with q1c ≥ 1.
    -- q1c * vTop = q1c*dHi*2^32 + q1c*dLo
    --            = (uHi*2^32 - rhatc*2^32) + q1c*dLo (from h_eucl_pow).
    -- So (q1c - 1) * vTop = uHi*2^32 - rhatc*2^32 + q1c*dLo - vTop.
    -- Bound: uHi*2^32 - rhatc*2^32 + q1c*dLo - vTop ≤ uHi*2^32 + div_un1
    -- ⟺ q1c*dLo ≤ rhatc*2^32 + div_un1 + vTop, which holds since
    -- q1c*dLo < 2^64 ≤ rhatc*2^32.
    have h_q1c_vTop_le :
        q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) ≤
          uHi.toNat * 2^32 + div_un1.toNat + (dHi.toNat * 2^32 + dLo.toNat) := by
      rw [h_qv_expand]
      -- Now use h_eucl_pow to substitute q1c*dHi*2^32.
      -- f := q1c*dHi, want f*2^32 + c ≤ uHi*2^32 + d + a*2^32 + b.
      -- From h_eucl_pow: f*2^32 + e*2^32 = uHi*2^32, so f*2^32 = uHi*2^32 - e*2^32.
      -- Goal becomes: uHi*2^32 - e*2^32 + c ≤ uHi*2^32 + d + a*2^32 + b
      --             ⟺ c ≤ e*2^32 + d + a*2^32 + b
      -- And c < 2^64 ≤ e*2^32, so this holds.
      nlinarith [h_eucl_pow, h_rhatc_pow_ge, h_q1c_dLo_lt, h_div_un1_lt]
    -- Now derive (q1c - 1) * vTop = q1c * vTop - vTop.
    have h_q1c_vTop_ge_vTop : (dHi.toNat * 2^32 + dLo.toNat) ≤
        q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) :=
      Nat.le_mul_of_pos_left _ h_q1c_pos
    have h_sub_mul : (q1c.toNat - 1) * (dHi.toNat * 2^32 + dLo.toNat) =
        q1c.toNat * (dHi.toNat * 2^32 + dLo.toNat) - (dHi.toNat * 2^32 + dLo.toNat) := by
      rw [Nat.sub_mul, Nat.one_mul]
    omega
  have h_div_ge : q1c.toNat - 1 ≤
      (uHi.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) :=
    (Nat.le_div_iff_mul_le h_vTop_pos).mpr h_key
  omega

/-- V4 Phase-2 Q0d UB in the wide-rhat2c regime via Phase-2 Euclidean.

    Specialises `div128Quot_q1c_le_q_true_1_plus_one_of_rhatc_ge_pow32`
    to `(un21, dHi, dLo, uLo <<< 32)` and folds the V4 `divKTrialCallV4Q0d`
    surface.  In wide-rhat2c (`rhat2c >> 32 ≠ 0`) the Phase-2b first
    correction guard does NOT fire, so `Q0d = q0c`, and the wide-rhatc
    Phase-1a UB applies. -/
theorem divKTrialCallV4Q0d_le_q_true_0_plus_one_of_rhat2c_ge_pow32
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (h_rhat2c_ge :
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat ≥ 2^32) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat ≤
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) + 1 := by
  have hdHi_ne : divKTrialCallV4DHi vTop ≠ 0 := by
    intro h_eq
    rw [h_eq] at hdHi_ge
    simp at hdHi_ge
  -- In wide-rhat2c, `phase2b_q0' q0c rhat2c dLo un0 = q0c` (guard does NOT fire).
  -- So Q0d = q0c, and we use the Knuth-B-level wide-rhatc UB.
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un0
  unfold div128Quot_phase2b_q0'
  -- The guard is `rhat2c >> 32 = 0`, which fails since rhat2c ≥ 2^32.
  have h_rhat2c_hi_ne_zero :
      (let un21 := divKTrialCallV4Un21 uHi uLo vTop
       let q0 := rv64_divu un21 (divKTrialCallV4DHi vTop)
       let rhat2 := un21 - q0 * divKTrialCallV4DHi vTop
       let hi2 := q0 >>> (32 : BitVec 6).toNat
       let rhat2c := if hi2 = 0 then rhat2 else rhat2 + divKTrialCallV4DHi vTop
       rhat2c >>> (32 : BitVec 6).toNat ≠ (0 : Word)) := by
    intro un21 q0 rhat2 hi2 rhat2c
    have h_rhat2c_ge_pow32_nat : rhat2c.toNat ≥ 2^32 := by
      simpa [un21, q0, rhat2, hi2, rhat2c, divKTrialCallV4Rhat2c] using h_rhat2c_ge
    intro h_zero
    have h_lt : rhat2c.toNat < 2^32 := by
      have := (ushiftRight_eq_zero_iff (val := rhat2c) ((32 : BitVec 6).toNat)).mp h_zero
      simpa using this
    omega
  rw [if_neg h_rhat2c_hi_ne_zero]
  -- Goal: q0c.toNat ≤ ... / ... + 1.
  -- Apply Knuth-B-level wide-rhatc UB at (un21, dHi, dLo, uLo << 32).
  exact div128Quot_q1c_le_q_true_1_plus_one_of_rhatc_ge_pow32
    (divKTrialCallV4Un21 uHi uLo vTop)
    (divKTrialCallV4DHi vTop)
    (divKTrialCallV4DLo vTop)
    (uLo <<< (32 : BitVec 6).toNat)
    hdHi_ne hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop
    (by simpa [divKTrialCallV4Rhat2c] using h_rhat2c_ge)

/-- V4 Phase-2 Q0dd UB in the wide-rhat2c regime.  Q0dd ≤ Q0d, so the
    bound is preserved by the second correction. -/
theorem divKTrialCallV4Q0dd_le_q_true_0_plus_one_of_rhat2c_ge_pow32
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (h_rhat2c_ge :
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat ≥ 2^32) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) + 1 := by
  have h_q0d_le :=
    divKTrialCallV4Q0d_le_q_true_0_plus_one_of_rhat2c_ge_pow32
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop h_rhat2c_ge
  exact le_trans (divKTrialCallV4Q0dd_le_q0d uHi uLo vTop) h_q0d_le

end EvmAsm.Evm64
