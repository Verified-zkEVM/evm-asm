/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.QuotientBounds

  Quotient/algorithm Word→Nat bridge wrappers and the per-step `_plus_one`
  decomposition (steps 1–6) used by §A1 / A2.S1 of the call-skip lower bound
  proof. Extracted from `CallSkipLowerBoundV2.lean` for file-size hygiene.

  ## Contents

  - `algorithmQ1Prime_ge_q_true_1` / `algorithmQ0Prime_ge_q_true_0` — wrapped
    Phase-1 / Phase-2 tight bounds folded onto the irreducible bundles.
  - `div128Quot_toNat_eq_algorithmQ1_Q0` — algorithmQ1 * 2^32 + algorithmQ0
    decomposition wrapper.
  - `algorithmQ1Prime_le_q_true_1_plus_two` — weak `+2` upper bound.
    **Generalized**: applies in BOTH narrow_u4 (u4 < dHi*2^32) AND
    wide-u4 regimes (since the proof internally only needs hu4_lt_b3').
  - `algorithmQ1Prime_step{1..6}_*` — six self-contained sub-steps
    composing the tight `+1` Knuth-B upper bound.
  - `algorithmQ1Prime_le_q_true_1_plus_one` — composition of step1/3/6 with
    `correction_step_overestimate_le_one` for the tight `+1` bound.
    Requires u4 < dHi*2^32 (Phase 1b uses rhatc < 2^32 which fails in
    narrow_u4 when dHi > 2^31).
  - `algorithmQ1Prime_ge_q_true_1_under_narrow_u4` — Phase 1 LOWER bound
    in the narrow_u4 regime. PARTIALLY UNPROVABLE per-phase (see
    docstring on the lemma + memory).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.Algorithm

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Phase 1 lower bound under narrow_u4** (PARTIALLY UNPROVABLE AS STATED):
    in the regime u4 ≥ dHi*2^32, Phase 1's q1' is NOT always ≥ q_true_1.

    **Critical discovery** (see `memory/project_a2s2_per_phase_tightness_fails.md`):
    Under `rhatc ≥ 2^32 + Phase 1b correction fires` (only when `dHi > 2^31`),
    the Word truncation `(rhatc << 32) | div_un1` causes Phase 1b's ult check
    to fire SPURIOUSLY. In this regime, `q1' = q1c - 1 = q_true_1 - 1`
    (genuine undershoot).

    Per-phase tightness DOES NOT hold in this regime. The lemma's statement
    is FALSE in this sub-case. The proof closes 3 of 4 sub-cases:
    - rhatc < 2^32: closed via KB-LB5.
    - rhatc ≥ 2^32 + no correction: closed via KB-LB3.
    - rhatc ≥ 2^32 + correction: GENUINELY UNPROVABLE per-phase. Need
      different proof structure (global qHat ≥ q_true_full, not per-phase).

    Kept as a stub (with internal sorry on the unprovable sub-case) to
    document the discovery. The 3 A2.S2 exact-case sorries that depend on
    this lemma will need to be re-architected to use global Phase 1+2
    compensation instead. -/
theorem algorithmQ1Prime_ge_q_true_1_under_narrow_u4
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_ge : u4.toNat ≥ (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat ≤
      (algorithmQ1Prime u4 u3 b3').toNat := by
  -- KB-LB3 applies in narrow_u4 (it doesn't need hu4_lt_dHi_pow32).
  -- Gives q_true_1 ≤ q1c.toNat (the post-Phase-1a lower bound).
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_div_un1_lt : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]; exact hu4_lt_b3'
  have h_q1c_ge :=
    div128Quot_q1c_ge_q_true_1 u4 (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      (u3 >>> (32 : BitVec 6).toNat) h_dHi_ne h_div_un1_lt h_u4_lt_vTop
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
  rw [h_v_eq]
  -- Sub-case-split on rhatc < 2^32 (the easy regime via KB-LB5).
  set q1 := rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) with hq1_def
  set rhat := u4 - q1 * (b3' >>> (32 : BitVec 6).toNat) with hrhat_def
  set hi1 := q1 >>> (32 : BitVec 6).toNat with hhi1_def
  set rhatc := if hi1 = 0 then rhat else rhat + (b3' >>> (32 : BitVec 6).toNat)
    with hrhatc_def
  by_cases h_rhatc_lt : rhatc.toNat < 2^32
  · -- rhatc < 2^32: KB-LB5 gives the full lower bound directly.
    rw [algorithmQ1Prime_unfold]
    exact div128Quot_q1_prime_ge_q_true_1_small_rhatc u4
      (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) u3
      h_dHi_ge h_dHi_lt h_dLo_lt h_u4_lt_vTop h_rhatc_lt
  · -- rhatc ≥ 2^32 (only when dHi > 2^31): genuine hard regime.
    -- Phase 1b case-split:
    -- - No correction (q1' = q1c): KB-LB3 directly closes.
    -- - Correction (q1' = q1c - 1): needs new analysis (truncation false-positive).
    rw [algorithmQ1Prime_unfold]
    simp only []
    by_cases h_check : BitVec.ult
        (((if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
                (32 : BitVec 6).toNat = 0 then
              u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
                (b3' >>> (32 : BitVec 6).toNat)
            else u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
                (b3' >>> (32 : BitVec 6).toNat) + (b3' >>> (32 : BitVec 6).toNat)) <<<
            (32 : BitVec 6).toNat) ||| u3 >>> (32 : BitVec 6).toNat)
        ((if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
              (32 : BitVec 6).toNat = 0 then
            rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
          else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095) *
          ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat))
    · -- Phase 1b correction fires under rhatc ≥ 2^32. CRITICAL ANALYSIS:
      --
      -- Under rhatc ≥ 2^32, the Word `(rhatc << 32) | div_un1` truncates
      -- rhatc's high bit. The Phase 1b ult check fires iff
      --   (rhatc % 2^32) * 2^32 + div_un1 < q1c * dLo
      -- But the "real" comparison (untruncated) would be:
      --   rhatc * 2^32 + div_un1 < q1c * dLo
      -- which is FALSE since rhatc ≥ 2^32 makes LHS ≥ 2^64 > q1c * dLo
      -- (the latter being < 2^64 by `div128Quot_q1_prime_dLo_no_wrap`).
      -- So the truncated check fires SPURIOUSLY.
      --
      -- In this spurious-fire regime, q1' = q1c - 1, but q1c might equal
      -- q_true_1 exactly, making q1' = q_true_1 - 1 (UNDERSHOOT).
      --
      -- **Per-phase tightness FAILS in this regime.** The `q1' ≥ q_true_1`
      -- invariant we're trying to prove is actually FALSE here.
      --
      -- This matches `memory/project_knuth_b_lower_large_rhatc.md`: per-phase
      -- tight bounds don't hold; Knuth-B's lower bound on the FULL
      -- qHat = q1' * 2^32 + q0' relies on Phase 2 COMPENSATION absorbing
      -- the Phase 1 undershoot.
      --
      -- **Conclusion**: this lemma's per-phase formulation cannot be
      -- closed in the rhatc ≥ 2^32 + correction regime. The `_narrow_u4_*`
      -- exact cases need a different proof strategy — global Phase 1+2
      -- compensation via the qHat-level argument, NOT per-phase tightness.
      rw [if_pos h_check]
      sorry
    · -- No Phase 1b correction. q1' = q1c, KB-LB3 closes.
      rw [if_neg h_check]
      exact h_q1c_ge

/-- **Phase 1 tight, wrapped**: Phase 1 tight specialized and folded into
    `algorithmQ1Prime`. Parallel to `algorithmQ0Prime_ge_q_true_0`. -/
theorem algorithmQ1Prime_ge_q_true_1
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hu4_lt_dHi_pow32 :
      u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (hu4_lt_vTop :
      u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
    (algorithmQ1Prime u4 u3 b3').toNat := by
  rw [algorithmQ1Prime_unfold]
  exact
    div128Quot_q1_prime_ge_q_true_1_of_uHi_lt_dHi_mul_pow32
      u4
      (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      u3
      hdHi_ge hdHi_lt hdLo_lt hu4_lt_dHi_pow32 hu4_lt_vTop

/-- **div128Quot decomposition, wrapped**: `div128Quot.toNat = algorithmQ1Prime.toNat
    * 2^32 + algorithmQ0Prime.toNat` under hcall + `q0' < 2^32`. Folds
    `div128Quot_toNat_eq_strict`'s internal q0'/q1' into the wrappers. -/
theorem div128Quot_toNat_eq_algorithmQ1_Q0
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hu4_lt_vTop :
      u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat)
    (hq0_lt : (algorithmQ0Prime u4 u3 b3').toNat < 2^32) :
    (div128Quot u4 u3 b3').toNat =
      (algorithmQ1Prime u4 u3 b3').toNat * 2^32 +
      (algorithmQ0Prime u4 u3 b3').toNat := by
  -- Step 1: rewrite div128Quot as halfword_combine of our wrappers.
  rw [show div128Quot u4 u3 b3' =
    ((algorithmQ1Prime u4 u3 b3') <<< (32 : BitVec 6).toNat) |||
    (algorithmQ0Prime u4 u3 b3') from by
      unfold div128Quot
      rw [algorithmQ1Prime_unfold, algorithmQ0Prime_unfold]
      simp only [algorithmUn21_unfold]]
  -- Step 2: halfword_combine.toNat = q1'.toNat * 2^32 + q0'.toNat.
  have hq1_lt : (algorithmQ1Prime u4 u3 b3').toNat < 2^32 := by
    rw [algorithmQ1Prime_unfold]
    exact
      div128Quot_q1_prime_lt_pow32 u4 (b3' >>> (32 : BitVec 6).toNat)
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) u3
        hdHi_ge hdHi_lt hdLo_lt hu4_lt_vTop
  rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
  exact EvmWord.halfword_combine _ _ hq1_lt hq0_lt

/-- **Phase 2 tight, wrapped**: Phase 2 tight specialized to our inputs
    and folded into the `algorithmQ0Prime` wrapper. Removes the q0'
    syntactic-mismatch blocker for downstream composition. -/
theorem algorithmQ0Prime_ge_q_true_0
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_vTop :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    ((algorithmUn21 u4 u3 b3').toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  rw [algorithmQ0Prime_unfold]
  exact
    div128Quot_q0_prime_ge_q_true_0_of_un21_lt_dHi_mul_pow32
      (algorithmUn21 u4 u3 b3')
      (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      u3
      hdHi_ge hdHi_lt hdLo_lt h_un21_lt_dHi_pow32 h_un21_lt_vTop

/-- **Phase 2 tight, wrapped (un21 < 2^63 variant)**: parallel to
    `algorithmQ0Prime_ge_q_true_0` but using KB-LB8 instead of KB-LB8'.
    Holds when `un21 < 2^63` (a complementary range to `un21 < dHi*2^32`).

    Used by `_wide_un21_narrow` sub-case where un21 ∈ [dHi*2^32, vTop) AND
    un21 < 2^63 — the KB-LB8' lemma doesn't apply but KB-LB8 does. -/
theorem algorithmQ0Prime_ge_q_true_0_of_un21_lt_pow63
    (u4 u3 b3' : Word)
    (hdHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (h_un21_lt_pow63 : (algorithmUn21 u4 u3 b3').toNat < 2^63)
    (h_un21_lt_vTop :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    ((algorithmUn21 u4 u3 b3').toNat * 2^32 +
      ((u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) /
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
    (algorithmQ0Prime u4 u3 b3').toNat := by
  rw [algorithmQ0Prime_unfold]
  exact
    div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63
      (algorithmUn21 u4 u3 b3')
      (b3' >>> (32 : BitVec 6).toNat)
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
      u3
      hdHi_ge hdHi_lt hdLo_lt h_un21_lt_pow63 h_un21_lt_vTop

/-- **Bridge sub-A (weak, `+2`)**: `algorithmQ1Prime.toNat ≤ q_true_1 + 2`
    stepping stone. Combines Phase 1b's q1' ≤ u4/dHi with Knuth-B trial_le
    giving u4/dHi ≤ q_true_1 + 2 (under normalization).

    Holds under just hb3'_ge + hu4_lt_b3' — does NOT require
    `u4 < dHi*2^32` (the weak bound applies even in narrow_u4 regime). -/
theorem algorithmQ1Prime_le_q_true_1_plus_two
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 2 := by
  set dHi := b3' >>> (32 : BitVec 6).toNat with hdHi_def
  set dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat with hdLo_def
  set div_un1 := u3 >>> (32 : BitVec 6).toNat with hdiv_un1_def
  have h_dHi_lt : dHi.toNat < 2^32 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    show ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_vTop_decomp : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact hu4_lt_b3'
  have h_dHi_ne : dHi ≠ 0 := by
    intro heq
    have : dHi.toNat = 0 := by rw [heq]; rfl
    omega
  have h_trial_le :=
    EvmWord.trial_quotient_le u4.toNat div_un1.toNat dHi.toNat dLo.toNat
      h_dHi_lt h_dLo_lt h_div_un1_lt h_u4_lt_vTop h_dHi_ge
  rw [algorithmQ1Prime_unfold]
  simp only []
  let rhatUn1 : Word := (((if (rv64_divu u4 dHi) >>> (32 : BitVec 6).toNat = 0
      then u4 - rv64_divu u4 dHi * dHi
      else u4 - rv64_divu u4 dHi * dHi + dHi) <<< (32 : BitVec 6).toNat)
      ||| div_un1)
  have h_q1'_le := (div128Quot_phase1b_quotient_bound u4 dHi h_dHi_ne h_dHi_lt
    dLo rhatUn1).2
  rw [h_vTop_decomp]
  exact Nat.le_trans h_q1'_le (by omega)

/-- **_plus_one sub-step 1**: Phase 1a Euclidean at Nat level. Under
    hcall, `q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat`.
    Direct wrap of `div128Quot_first_round_post`. Only needs `b3' ≥ 2^63`
    (for dHi ≠ 0 + dHi < 2^32). -/
theorem algorithmQ1Prime_step1_phase1a_euclidean
    (u4 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat := by
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  exact div128Quot_first_round_post u4 (b3' >>> (32 : BitVec 6).toNat)
    h_dHi_ne h_dHi_lt

/-- **_plus_one sub-step 2**: KB-LB3 wrapped. `q_true_1 ≤ q1c.toNat`.
    Generalized: only needs `b3' ≥ 2^63` + `u4 < b3'`, applies in
    narrow_u4 too. -/
theorem algorithmQ1Prime_step2_q1c_ge_q_true_1
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
      ≤ q1c.toNat := by
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_div_un1_lt : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    h_v_eq ▸ hu4_lt_b3'
  rw [h_v_eq]
  exact div128Quot_q1c_ge_q_true_1 u4 (b3' >>> (32 : BitVec 6).toNat)
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    (u3 >>> (32 : BitVec 6).toNat) h_dHi_ne h_div_un1_lt h_u4_lt_vTop

/-- **_plus_one sub-step 3**: `q1c ≤ q_true_1 + 2` via trial_quotient_le
    + Phase 1a monotonicity. -/
theorem algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 2 := by
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un1_lt : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    h_v_eq ▸ hu4_lt_b3'
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    omega
  -- q1.toNat = u4.toNat / dHi.toNat
  have h_q1_eq : (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)).toNat =
      u4.toNat / (b3' >>> (32 : BitVec 6).toNat).toNat :=
    EvmWord.rv64_divu_toNat u4 _ h_dHi_ne
  -- q1c ≤ q1 (Phase 1a monotonicity).
  have h_q1c_le_q1 := div128Quot_q1c_le_q1 u4 (b3' >>> (32 : BitVec 6).toNat)
  -- q1 ≤ q_true_1 + 2 (trial_quotient_le).
  have h_q1_le :=
    EvmWord.trial_quotient_le u4.toNat (u3 >>> (32 : BitVec 6).toNat).toNat
      (b3' >>> (32 : BitVec 6).toNat).toNat
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
      h_dHi_lt h_dLo_lt h_div_un1_lt h_u4_lt_vTop h_dHi_ge
  rw [h_v_eq]
  omega

/-- **_plus_one sub-step 4**: `rhatc.toNat < 2^32` under `u4 < dHi*2^32`.
    Direct wrapping of `div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32`. -/
theorem algorithmQ1Prime_step4_rhatc_lt_pow32
    (u4 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    rhatc.toNat < 2^32 := by
  have h_dHi_ne : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  exact div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32 u4
    (b3' >>> (32 : BitVec 6).toNat) h_dHi_ne hu4_lt_dHi_pow32 h_dHi_lt

/-- **_plus_one sub-step 5**: Word↔Nat ult bridge. Under hcall,
    `BitVec.ult rhatUn1 (q1c*dLo) ↔ q1c.toNat * dLo.toNat
     > rhatc.toNat * 2^32 + div_un1.toNat`. -/
theorem algorithmQ1Prime_step5_ult_bridge
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    (BitVec.ult rhatUn1 (q1c * dLo) = true) ↔
      (q1c.toNat * dLo.toNat >
       rhatc.toNat * 2^32 + div_un1.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc rhatUn1
  have h_dHi_lt : dHi.toNat < 2^32 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    show ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := h_v_eq ▸ hu4_lt_b3'
  -- q1c ≤ 2^32 (Phase 1a bound).
  have h_q1c_le : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 u4 dHi dLo h_dHi_ge h_dLo_lt h_u4_lt_vTop
  -- rhatc < 2^32 (step4).
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    algorithmQ1Prime_step4_rhatc_lt_pow32 u4 b3' hb3'_ge hu4_lt_dHi_pow32
  -- q1c * dLo no-wrap.
  have h_q1c_dLo_lt : q1c.toNat * dLo.toNat < 2^64 := by
    have : q1c.toNat * dLo.toNat ≤ 2^32 * (2^32 - 1) := by
      have h : dLo.toNat ≤ 2^32 - 1 := by omega
      exact Nat.mul_le_mul h_q1c_le h
    have : (2^32 : Nat) * (2^32 - 1) = 2^64 - 2^32 := by decide
    omega
  -- rhatUn1.toNat via halfword_combine.
  have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
    show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
    exact EvmWord.halfword_combine _ _ h_rhatc_lt h_div_un1_lt
  -- Apply ult_iff and chain the equalities.
  rw [EvmWord.ult_iff, BitVec.toNat_mul, Nat.mod_eq_of_lt h_q1c_dLo_lt,
      h_rhatUn1_eq]

/-- **_plus_one sub-step 6**: Word-level if → Nat-level if bridge for q1'.
    The algorithm's q1' (Word if on ult) equals at the .toNat level the
    Nat if on the underlying comparison. Decomposes into 2 cases: when
    ult fires (q1' = q1c - 1, needs q1c > 0 via phase1b_check_implies_q1c_pos),
    and when it doesn't (q1' = q1c).

    Body deferred — requires careful handling of `q1c + signExtend12 4095`
    as Nat subtraction by 1 (safe via phase1b_check_implies_q1c_pos). -/
theorem algorithmQ1Prime_step6_word_nat_if_bridge
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    (algorithmQ1Prime u4 u3 b3').toNat =
      (if q1c.toNat * dLo.toNat > rhatc.toNat * 2^32 + div_un1.toNat
       then q1c.toNat - 1 else q1c.toNat) := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc
  have h_ult_bridge := algorithmQ1Prime_step5_ult_bridge u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  simp only [] at h_ult_bridge
  rw [algorithmQ1Prime_unfold]
  show (if BitVec.ult _ (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat = _
  by_cases h_word_ult : BitVec.ult
      ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) (q1c * dLo) = true
  · rw [if_pos h_word_ult]
    have h_nat := h_ult_bridge.mp h_word_ult
    rw [if_pos h_nat]
    have h_q1c_pos :=
      div128Quot_phase1b_check_implies_q1c_pos q1c dLo
        ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1) h_word_ult
    rw [BitVec.toNat_add, signExtend12_4095_toNat]
    have h_q1c_lt : q1c.toNat < 2^64 := q1c.isLt
    rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
        Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : q1c.toNat - 1 < 2^64)]
  · rw [if_neg h_word_ult]
    have h_not_nat : ¬ (q1c.toNat * dLo.toNat > rhatc.toNat * 2^32 + div_un1.toNat) := by
      intro h
      exact h_word_ult (h_ult_bridge.mpr h)
    rw [if_neg h_not_nat]

/-- **Bridge sub-A** (Knuth-B upper at Phase 1b): under standard hcall,
    `algorithmQ1Prime.toNat ≤ (u4*2^32 + div_un1) / b3' + 1`.

    **Composition** (once all 6 sub-steps are filled):
    1. `algorithmQ1Prime_step1_phase1a_euclidean` — q1c*dHi + rhatc = u4.
    2. `algorithmQ1Prime_step2_q1c_ge_q_true_1` — q_true_1 ≤ q1c.
    3. `algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two` — q1c ≤ q_true_1 + 2.
    4. `half_round_overestimate_le_one` (or `correction_step_overestimate_le_one`)
       — q' ≤ q_true_1 + 1 where q' is the Nat-level if-then-else.
    5. `algorithmQ1Prime_step5_ult_bridge` — Word ult ↔ Nat comparison.
    6. `algorithmQ1Prime_step6_word_nat_if_bridge` — bridge algorithmQ1Prime.toNat
       to the Nat-level if-then-else (given step5's Word↔Nat bridge). -/
theorem algorithmQ1Prime_le_q_true_1_plus_one
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    (algorithmQ1Prime u4 u3 b3').toNat ≤
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 1 := by
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_eucl := algorithmQ1Prime_step1_phase1a_euclidean u4 b3' hb3'_ge
  have h_q1c_le := algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two u4 u3 b3'
    hb3'_ge hu4_lt_b3'
  have h_if_bridge := algorithmQ1Prime_step6_word_nat_if_bridge u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  simp only [] at h_eucl h_q1c_le h_if_bridge
  rw [h_v_eq] at h_q1c_le
  -- Rewrite goal using step6 (algorithmQ1Prime.toNat = Nat-if).
  rw [h_if_bridge]
  -- Rewrite divisor using h_v_eq.
  conv_rhs => rw [h_v_eq]
  have h_vTop_pos :
      0 < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
          ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]; have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_q1c_mul_le :
      (if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
      else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095).toNat *
      (b3' >>> (32 : BitVec 6).toNat).toNat ≤ u4.toNat := by omega
  have h_rhatc_eq :
      (if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat)
      else u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat) + (b3' >>> (32 : BitVec 6).toNat)).toNat =
      u4.toNat -
      (if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
      else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095).toNat *
      (b3' >>> (32 : BitVec 6).toNat).toNat := by omega
  exact EvmWord.correction_step_overestimate_le_one u4.toNat
    (u3 >>> (32 : BitVec 6).toNat).toNat
    (b3' >>> (32 : BitVec 6).toNat).toNat
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
    ((if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
      else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095).toNat)
    ((if (rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)) >>>
           (32 : BitVec 6).toNat = 0 then
        u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat)
      else u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
          (b3' >>> (32 : BitVec 6).toNat) + (b3' >>> (32 : BitVec 6).toNat)).toNat)
    (B := 2^32) h_vTop_pos h_rhatc_eq h_q1c_mul_le h_q1c_le

end EvmAsm.Evm64
