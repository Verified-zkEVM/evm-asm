/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainA

  Shared declaration home for the V5 lower-bound proof chain.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bNoFireBound
import EvmAsm.Evm64.EvmWordArith.Div128Lemmas
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dNoFire

  When the V5 Phase-1b 1st correction does NOT fire, the post-1st-correction
  values `algorithmQ1dV5` / `algorithmRhatdV5` coincide with the
  Phase-1a-corrected values `algorithmQ1cV5` / `algorithmRhatcV5`.

  Mirror of v4's `algorithmQ1dV4_eq_q1c_of_phase1b_no_fire`
  (`Phase1bBound.lean:89`), but adapted to V5's stricter guard
  (`rhatc >>> 32 = 0 ∧ BLTU` vs v4's bare BLTU).

  Bead `evm-asm-wbc4i.4.6.8` (V5.4.0.9). Prerequisite for V5.4.1.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- When Phase-1b 1st correction doesn't fire, `Q1d = Q1c`. -/
theorem algorithmQ1dV5_eq_q1c_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV5 uHi uLo vTop) :
    algorithmQ1dV5 uHi uLo vTop = algorithmQ1cV5 uHi vTop := by
  rw [algorithmQ1dV5_unfold]
  dsimp only
  -- The let-bindings flatten; just need to show the if-condition is false.
  -- Direct case-split: show the fire condition is false.
  have h_fire_false :
      (decide (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0) &&
        BitVec.ult
          ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo)
          (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)) ≠ true := by
    intro h_true
    rw [Bool.and_eq_true, decide_eq_true_eq] at h_true
    obtain ⟨h_hi, h_ult⟩ := h_true
    apply h_no_fire
    delta algorithmPhase1bFireV5 algorithmRhatUn1cV5
    exact ⟨h_hi, h_ult⟩
  simp only [h_fire_false, Bool.false_eq_true, if_false]

/-- When Phase-1b 1st correction doesn't fire, `Rhatd = Rhatc`. -/
theorem algorithmRhatdV5_eq_rhatc_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV5 uHi uLo vTop) :
    algorithmRhatdV5 uHi uLo vTop = algorithmRhatcV5 uHi vTop := by
  rw [algorithmRhatdV5_unfold]
  dsimp only
  -- Direct case-split: show the fire condition is false.
  have h_fire_false :
      (decide (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0) &&
        BitVec.ult
          ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo)
          (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)) ≠ true := by
    intro h_true
    rw [Bool.and_eq_true, decide_eq_true_eq] at h_true
    obtain ⟨h_hi, h_ult⟩ := h_true
    apply h_no_fire
    delta algorithmPhase1bFireV5 algorithmRhatUn1cV5
    exact ⟨h_hi, h_ult⟩
  simp only [h_fire_false, Bool.false_eq_true, if_false]

/-- When Phase-1b 1st correction doesn't fire, the Q1d/Rhatd pair
    satisfies the "overshoot ≤ vTop" bound — the algorithm-level
    precondition required by the generic
    `div128Quot_phase2b_q0'_dLo_bound_fire_case`.

    Combines V5.4.0.8 (Q1c bound) with V5.4.0.9 (Q1d = Q1c when no-fire)
    and trivially weakens to the overshoot form. Mirror of v4's
    `algorithmQ1dV4_dLo_overshoot_le_vTop_of_phase1b_no_fire`
    (`Phase1bBound.lean:838`). -/
theorem algorithmQ1dV5_dLo_overshoot_le_vTop_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat ≤
      (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV5Un1 uLo).toNat +
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
  have h_bound := algorithmQ1cV5_dLo_bound_of_phase1b_no_fire uHi uLo vTop h_no_fire
  rw [algorithmQ1dV5_eq_q1c_of_phase1b_no_fire uHi uLo vTop h_no_fire,
      algorithmRhatdV5_eq_rhatc_of_phase1b_no_fire uHi uLo vTop h_no_fire]
  exact le_trans h_bound (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dEuclidean

  Phase-1b Euclidean identity at the V5 post-1st-correction level:
  `Q1d * dHi + Rhatd = uHi`. Holds unconditionally via case analysis:
  - No-fire: Q1d = Q1c, Rhatd = Rhatc; reduce to `algorithmQ1cV5_rhatc_post`.
  - Fire: Q1d = Q1c - 1 (Word, with no-wrap from Q1c ≥ 1 derived from BLTU),
    Rhatd = Rhatc + dHi (with no-wrap from rhatc >>> 32 = 0 ⇒ Rhatc < 2^32);
    algebra cancels and reduces to the Q1c Euclidean identity.

  Mirror of v4's `algorithmQ1dV4_rhatd_post` (`Phase1bBound.lean:113`).

  Bead `evm-asm-wbc4i.4.6.11` (V5.4.0.12). Prerequisite for V5.4.0.11 (fire-case
  overshoot) and V5.4.1.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- When Phase-1b 1st correction fires, the BLTU subterm implies
    `Q1c.toNat ≥ 1` (since `BLTU x 0 = false` for any unsigned `x`). -/
private theorem q1c_pos_of_phase1b_fire
    (uHi uLo vTop : Word)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1cV5 uHi vTop).toNat ≥ 1 := by
  delta algorithmPhase1bFireV5 algorithmRhatUn1cV5 at h_fire
  obtain ⟨_, h_ult⟩ := h_fire
  by_contra hq_lt
  push Not at hq_lt
  have hq_nat : (algorithmQ1cV5 uHi vTop).toNat = 0 := by omega
  have hq0 : algorithmQ1cV5 uHi vTop = 0 := BitVec.eq_of_toNat_eq hq_nat
  rw [hq0] at h_ult
  simp [BitVec.ult] at h_ult

/-- When Phase-1b 1st correction fires, `rhatc >>> 32 = 0` (the guard half
    of `algorithmPhase1bFireV5`), and hence `Rhatc < 2^32`. -/
private theorem rhatc_lt_pow32_of_phase1b_fire
    (uHi uLo vTop : Word)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmRhatcV5 uHi vTop).toNat < 2^32 := by
  delta algorithmPhase1bFireV5 algorithmRhatUn1cV5 at h_fire
  obtain ⟨h_hi_zero, _⟩ := h_fire
  -- rhatc >>> 32 = 0 ⇒ rhatc.toNat / 2^32 = 0 ⇒ rhatc.toNat < 2^32
  have h_nat : (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat).toNat = 0 := by
    rw [h_hi_zero]; rfl
  rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
      Nat.shiftRight_eq_div_pow] at h_nat
  have h_lt : (algorithmRhatcV5 uHi vTop).toNat < 2^64 :=
    (algorithmRhatcV5 uHi vTop).isLt
  exact Nat.div_eq_zero_iff.mp h_nat |>.resolve_left (by decide)

/-- The V5 Phase-1b post-1st-correction Euclidean identity. -/
theorem algorithmQ1dV5_rhatd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
      (algorithmRhatdV5 uHi uLo vTop).toNat = uHi.toNat := by
  have h_pre := algorithmQ1cV5_rhatc_post uHi vTop hvTop_ge
  by_cases h_fire : algorithmPhase1bFireV5 uHi uLo vTop
  · -- Fire: Q1d = Q1c + signExtend12 4095, Rhatd = Rhatc + dHi.
    rw [algorithmQ1dV5_unfold, algorithmRhatdV5_unfold]
    dsimp only
    have h_fire_cond :
        (decide (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0) &&
          BitVec.ult
            ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
              divKTrialCallV5Un1 uLo)
            (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)) = true := by
      rw [algorithmPhase1bFireV5_unfold] at h_fire
      rw [algorithmRhatUn1cV5_unfold] at h_fire
      obtain ⟨h_hi, h_ult⟩ := h_fire
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h_hi, h_ult⟩
    rw [if_pos h_fire_cond, if_pos h_fire_cond]
    -- Need: (Q1c + sx 4095).toNat * dHi + (Rhatc + dHi).toNat = uHi.toNat
    set q1c := algorithmQ1cV5 uHi vTop with hq1c
    set rhatc := algorithmRhatcV5 uHi vTop with hrhatc
    set dHi := divKTrialCallV5DHi vTop with hdHi
    -- Q1c ≥ 1 from fire (BLTU on q1c*dLo ≠ 0)
    have h_q1c_pos : q1c.toNat ≥ 1 := by
      rw [hq1c]; exact q1c_pos_of_phase1b_fire uHi uLo vTop h_fire
    -- Q1c < 2^32 from cap
    have h_q1c_lt : q1c.toNat < 2^32 := by
      rw [hq1c]; exact algorithmQ1cV5_lt_pow32 uHi vTop
    -- Rhatc < 2^32 from fire's high-half guard
    have h_rhatc_lt : rhatc.toNat < 2^32 := by
      rw [hrhatc]; exact rhatc_lt_pow32_of_phase1b_fire uHi uLo vTop h_fire
    -- dHi < 2^32
    have h_dHi_lt : dHi.toNat < 2^32 := by
      rw [hdHi]; exact divKTrialCallV5DHi_lt_pow32 vTop
    -- (Q1c + signExtend12 4095).toNat = Q1c.toNat - 1 (no-wrap since Q1c ≥ 1)
    have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
    have h_q1d_eq : (q1c + signExtend12 4095).toNat = q1c.toNat - 1 := by
      rw [BitVec.toNat_add, h_se]
      have h_sum : q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 := by omega
      rw [h_sum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q1c.toNat - 1 < 2^64)]
    -- (Rhatc + dHi).toNat = Rhatc.toNat + dHi.toNat (no-wrap since both < 2^32)
    have h_rhatd_eq : (rhatc + dHi).toNat = rhatc.toNat + dHi.toNat := by
      rw [BitVec.toNat_add]
      apply Nat.mod_eq_of_lt; omega
    rw [h_q1d_eq, h_rhatd_eq]
    -- Need: (Q1c - 1) * dHi + (Rhatc + dHi) = Q1c * dHi + Rhatc = uHi.toNat
    have h_q1c_dHi : q1c.toNat * dHi.toNat = (q1c.toNat - 1) * dHi.toNat + dHi.toNat := by
      have : q1c.toNat = (q1c.toNat - 1) + 1 := by omega
      calc q1c.toNat * dHi.toNat
          = ((q1c.toNat - 1) + 1) * dHi.toNat := by rw [← this]
        _ = (q1c.toNat - 1) * dHi.toNat + dHi.toNat := by ring
    have h_pre' : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat := by
      rw [hq1c, hdHi, hrhatc] at *; exact h_pre
    omega
  · -- No-fire: Q1d = Q1c, Rhatd = Rhatc.
    rw [algorithmQ1dV5_eq_q1c_of_phase1b_no_fire uHi uLo vTop h_fire,
        algorithmRhatdV5_eq_rhatc_of_phase1b_no_fire uHi uLo vTop h_fire]
    exact h_pre

/-- The product `Q1d * dLo` does not wrap mod 2^64 under the V5 cap.
    Trivial consequence of `Q1d < 2^32` (V5.4.0.6) and `dLo < 2^32`
    (V5.4.0.5). Used by V5.4.1 when bridging the Phase-1b 2nd
    correction's word-level BLTU to the Nat-level dLo bound. -/
theorem algorithmQ1dV5_dLo_no_wrap (uHi uLo vTop : Word) :
    (algorithmQ1dV5 uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  have h_q := algorithmQ1dV5_lt_pow32 uHi uLo vTop
  have h_d := divKTrialCallV5DLo_lt_pow32 vTop
  have : (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat <
      2^32 * 2^32 := Nat.mul_lt_mul'' h_q h_d
  calc (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat
      < 2^32 * 2^32 := this
    _ = 2^64 := by norm_num

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cKnuthB

  Knuth-B upper bound on the V5 Phase-1a-corrected quotient:
  `Q1c.toNat ≤ q_true_1 + 2` under `vTop ≥ 2^63` and `uHi < vTop`,
  where `q_true_1 = (uHi*2^32 + un1) / vTop`.

  Mirror of v2's `algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two`
  (`CallSkipLowerBoundV2/QuotientBounds.lean:284`), adapted to the V5
  cap. Sub-cases on the Phase-1a `hi1`:
  - `hi1 = 0`: Q1c = q1, direct from `trial_quotient_le` (Knuth-B).
  - `hi1 ≠ 0`: Q1c = 2^32 - 1; combined with `q1 ≥ 2^32` and Knuth-B
    `q1 ≤ q_true_1 + 2`, we get `q_true_1 ≥ 2^32 - 2 ≥ 2^32 - 3` so
    `Q1c = 2^32 - 1 ≤ q_true_1 + 2`.

  Bead `evm-asm-wbc4i.4.6.14` (V5.4.0.15). Prerequisite for V5.4.0.11
  (fire-case Q1d overshoot bound) and onward to V5.4.1.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Knuth-B upper bound for V5's Phase-1a-corrected quotient. -/
theorem algorithmQ1cV5_le_q_true_1_plus_two
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (algorithmQ1cV5 uHi vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 2 := by
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un1 := divKTrialCallV5Un1 uLo with hun1
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    rw [hdHi]; unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_lt : dHi.toNat < 2^32 := by
    rw [hdHi]; exact divKTrialCallV5DHi_lt_pow32 vTop
  have h_dLo_lt : dLo.toNat < 2^32 := by
    rw [hdLo]; exact divKTrialCallV5DLo_lt_pow32 vTop
  have h_un1_lt : un1.toNat < 2^32 := by
    rw [hun1]; exact divKTrialCallV5Un1_lt_pow32 uLo
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  have h_uHi_lt : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact huHi_lt_vTop
  have h_dHi_ne : dHi ≠ 0 := by
    intro h
    have : dHi.toNat = 0 := by rw [h]; rfl
    omega
  -- q1.toNat = uHi.toNat / dHi.toNat
  set q1 : Word := rv64_divu uHi dHi with hq1
  have h_q1_eq : q1.toNat = uHi.toNat / dHi.toNat := by
    rw [hq1]; unfold rv64_divu
    have : ¬ (dHi == 0#64) := by simpa using h_dHi_ne
    rw [if_neg this, BitVec.toNat_udiv]
  -- Knuth-B: q1 ≤ q_true_1 + 2
  have h_q1_le : q1.toNat ≤
      (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat + 2 := by
    rw [h_q1_eq, h_vTop_decomp]
    exact EvmWord.trial_quotient_le uHi.toNat un1.toNat dHi.toNat dLo.toNat
      h_dHi_lt h_dLo_lt h_un1_lt h_uHi_lt h_dHi_ge
  -- Case split on hi1
  rw [algorithmQ1cV5_unfold]
  dsimp only
  by_cases h_hi1 : q1 >>> (32 : BitVec 6).toNat = (0 : Word)
  · -- hi1 = 0: Q1c = q1
    simp only [hq1, hdHi] at h_hi1
    rw [if_pos h_hi1]
    -- Goal: q1.toNat ≤ ...
    have h_q1_eq' : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat = q1.toNat := by
      rw [hq1]
    rw [h_q1_eq']
    exact h_q1_le
  · -- hi1 ≠ 0: Q1c = q1cCap = 2^32 - 1
    simp only [hq1, hdHi] at h_hi1
    rw [if_neg h_hi1]
    -- Goal: q1cCap.toNat ≤ ...
    have h_cap : ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat : Word).toNat = 2^32 - 1 := by
      decide
    rw [h_cap]
    -- q1 ≥ 2^32 (from hi1 ≠ 0)
    have h_q1_ge : q1.toNat ≥ 2^32 := by
      have h_shift : (q1 >>> (32 : BitVec 6).toNat).toNat = q1.toNat / 2^32 := by
        rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      -- h_hi1 : q1 >>> 32 ≠ 0 (as Words), so its toNat is nonzero, so q1 / 2^32 ≥ 1.
      have h_ne_nat : (q1 >>> (32 : BitVec 6).toNat).toNat ≠ 0 := by
        intro h
        apply h_hi1
        exact BitVec.eq_of_toNat_eq (by simpa using h)
      omega
    omega

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dKnuthAFire

  Knuth-A upper bound for the V5 post-Phase-1b-1st-correction quotient
  in the FIRE case: `Q1d.toNat ≤ q_true_1 + 1` under V5's fire condition
  (the `decide guard && BLTU` form).

  Composes V5.4.0.15 (Q1c ≤ q_true_1 + 2) with the fire-induced Q1c ≥ 1
  (from `q1c_pos_of_phase1b_fire`) to derive Q1d = Q1c - 1 ≤ q_true_1 + 1
  at the Nat level.

  Mirror of v4's `algorithmQ1dV4_le_qtrue_plus_one_of_phase1b_fire`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:526`).

  Bead `evm-asm-wbc4i.4.6.15` (V5.4.0.16). Prerequisite for V5.4.0.11
  (fire-case overshoot bound) and onward to V5.4.1 / V5.4.2.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- When V5 Phase-1b 1st correction fires, the post-correction quotient
    Q1d is at most `q_true_1 + 1`. -/
theorem algorithmQ1dV5_le_qtrue_plus_one_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1dV5 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1 := by
  -- Knuth-B bound on Q1c
  have h_q1c_le : (algorithmQ1cV5 uHi vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 2 :=
    algorithmQ1cV5_le_q_true_1_plus_two uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Q1c ≥ 1 from fire (BLTU on q1c * dLo ≠ 0)
  have h_q1c_pos : (algorithmQ1cV5 uHi vTop).toNat ≥ 1 := by
    rw [algorithmPhase1bFireV5_unfold] at h_fire
    obtain ⟨_, h_ult⟩ := h_fire
    by_contra hq_lt
    push Not at hq_lt
    have hq_nat : (algorithmQ1cV5 uHi vTop).toNat = 0 := by omega
    have hq0 : algorithmQ1cV5 uHi vTop = 0 := BitVec.eq_of_toNat_eq hq_nat
    rw [algorithmRhatUn1cV5_unfold] at h_ult
    rw [hq0] at h_ult
    simp [BitVec.ult] at h_ult
  -- Q1c < 2^32 from cap (V5.4.0.4)
  have h_q1c_lt : (algorithmQ1cV5 uHi vTop).toNat < 2^32 :=
    algorithmQ1cV5_lt_pow32 uHi vTop
  -- Unfold Q1d and apply the fire-case branch
  rw [algorithmQ1dV5_unfold]
  dsimp only
  -- Show the if-condition is `true`
  have h_fire_cond :
      (decide (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0) &&
        BitVec.ult
          ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo)
          (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)) = true := by
    rw [algorithmPhase1bFireV5_unfold] at h_fire
    rw [algorithmRhatUn1cV5_unfold] at h_fire
    obtain ⟨h_hi, h_ult⟩ := h_fire
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h_hi, h_ult⟩
  rw [if_pos h_fire_cond]
  -- Q1c + signExtend12 4095 = Q1c - 1 mod 2^64 (no-wrap since Q1c ≥ 1)
  have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  rw [BitVec.toNat_add, h_se]
  have h_sum : (algorithmQ1cV5 uHi vTop).toNat + (2^64 - 1) =
      ((algorithmQ1cV5 uHi vTop).toNat - 1) + 2^64 := by omega
  rw [h_sum, Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt (by omega : (algorithmQ1cV5 uHi vTop).toNat - 1 < 2^64)]
  omega

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dFireOvershoot

  Fire-case overshoot bound at the V5 Phase-1b post-1st-correction:

    Q1d * dLo ≤ Rhatd * 2^32 + un1 + dHi * 2^32 + dLo

  Composes V5.4.0.16 (Q1d ≤ q_true_1 + 1 in fire) + V5.4.0.12 (Q1d
  Euclidean) algebraically:
  - Q1d ≤ q_true_1 + 1 ⇒ Q1d * vTop ≤ uHi*2^32 + un1 + vTop.
  - Q1d Euclidean ⇒ Q1d * dHi + Rhatd = uHi at Nat level.
  - vTop = dHi*2^32 + dLo decomposition + Q1d*vTop expansion gives the
    overshoot bound after Nat rearrangement.

  Mirror of v4's `algorithmQ1dV4_dLo_overshoot_le_vTop_of_phase1b_fire`
  (`Phase1bBound.lean:711`). Used by V5.4.1 case-split (with V5.4.0.10
  for the no-fire branch) to discharge the phase2b-fire-case helper's
  precondition.

  Bead `evm-asm-wbc4i.4.6.10` (V5.4.0.11). Prerequisite for V5.4.1.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem algorithmQ1dV5_dLo_overshoot_le_vTop_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat ≤
      (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV5Un1 uLo).toNat +
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
  -- Knuth-A fire-case bound: Q1d ≤ q_true_1 + 1.
  have h_q1d_le : (algorithmQ1dV5 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1 :=
    algorithmQ1dV5_le_qtrue_plus_one_of_phase1b_fire uHi uLo vTop
      hvTop_ge huHi_lt_vTop h_fire
  -- Q1d Euclidean: Q1d * dHi + Rhatd = uHi.
  have h_eucl : (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat +
      (algorithmRhatdV5 uHi uLo vTop).toNat = uHi.toNat :=
    algorithmQ1dV5_rhatd_post uHi uLo vTop hvTop_ge
  -- vTop = dHi * 2^32 + dLo.
  have h_vTop : vTop.toNat =
      (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
    unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  -- vTop ≥ 1 (from normalization).
  have h_vTop_pos : vTop.toNat ≥ 1 := by omega
  -- q_true_1 * vTop ≤ uHi*2^32 + un1.
  have h_qtrue_mul : ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
        vTop.toNat) * vTop.toNat ≤ uHi.toNat * 2^32 +
      (divKTrialCallV5Un1 uLo).toNat := Nat.div_mul_le_self _ _
  -- Q1d * vTop ≤ uHi*2^32 + un1 + vTop.
  have h_q1d_vTop : (algorithmQ1dV5 uHi uLo vTop).toNat * vTop.toNat ≤
      uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat + vTop.toNat := by
    have h_mul_le : (algorithmQ1dV5 uHi uLo vTop).toNat * vTop.toNat ≤
        ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1) *
          vTop.toNat := Nat.mul_le_mul_right _ h_q1d_le
    have h_expand :
        ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1) *
          vTop.toNat =
        ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat) *
          vTop.toNat + vTop.toNat := by ring
    omega
  -- Substitute vTop expansion to get Q1d * dHi * 2^32 + Q1d * dLo ≤ ...
  have h_q1d_split : (algorithmQ1dV5 uHi uLo vTop).toNat * vTop.toNat =
      (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
      (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DLo vTop).toNat := by
    rw [h_vTop]; ring
  -- From Euclidean: Q1d * dHi = uHi - Rhatd (with Rhatd ≤ uHi).
  have h_rhatd_le_uHi : (algorithmRhatdV5 uHi uLo vTop).toNat ≤ uHi.toNat := by
    omega
  have h_q1d_dHi : (algorithmQ1dV5 uHi uLo vTop).toNat *
      (divKTrialCallV5DHi vTop).toNat =
      uHi.toNat - (algorithmRhatdV5 uHi uLo vTop).toNat := by omega
  -- Now Q1d * dLo = Q1d * vTop - Q1d * dHi * 2^32, and Q1d * dHi * 2^32 =
  -- (uHi - Rhatd) * 2^32 = uHi*2^32 - Rhatd*2^32.
  rw [h_vTop] at h_q1d_vTop
  -- Goal restated using h_q1d_split, h_q1d_dHi, and h_q1d_vTop.
  have h_q1d_dHi_pow32 :
      (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat * 2^32 =
      uHi.toNat * 2^32 - (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 := by
    rw [h_q1d_dHi]; rw [Nat.sub_mul]
  have h_rhatd_pow32_le : (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 ≤
      uHi.toNat * 2^32 := Nat.mul_le_mul_right _ h_rhatd_le_uHi
  -- Set up abbreviations and key linear facts.
  set Q := (algorithmQ1dV5 uHi uLo vTop).toNat
  set R := (algorithmRhatdV5 uHi uLo vTop).toNat
  set D := (divKTrialCallV5DHi vTop).toNat
  set L := (divKTrialCallV5DLo vTop).toNat
  set U := uHi.toNat
  set U1 := (divKTrialCallV5Un1 uLo).toNat
  -- h_q1d_vTop is already in the form `Q*(D*2^32+L) ≤ ...` after the earlier rw [h_vTop].
  -- Expand Q * (D*2^32 + L) = Q*D*2^32 + Q*L.
  have h_expand : Q * (D * 2^32 + L) = Q * D * 2^32 + Q * L := by ring
  have h_QD : Q * D * 2^32 = U * 2^32 - R * 2^32 := h_q1d_dHi_pow32
  have h_R_pow32 : R * 2^32 ≤ U * 2^32 := h_rhatd_pow32_le
  -- Goal: Q * L ≤ R * 2^32 + U1 + D * 2^32 + L.
  linarith [h_q1d_vTop, h_expand, h_QD, h_R_pow32]

/-- Unconditional Phase-1b overshoot bound for V5's Q1d. Combines the
    no-fire (V5.4.0.10) and fire (V5.4.0.11) branches via a single
    case-split on `algorithmPhase1bFireV5`. Bead `evm-asm-wbc4i.4.6.16`
    (V5.4.0.17). Prerequisite for V5.4.1. -/
theorem algorithmQ1dV5_dLo_overshoot_le_vTop_closed
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat ≤
      (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV5Un1 uLo).toNat +
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
  by_cases h_fire : algorithmPhase1bFireV5 uHi uLo vTop
  · exact algorithmQ1dV5_dLo_overshoot_le_vTop_of_phase1b_fire
      uHi uLo vTop hvTop_ge huHi_lt_vTop h_fire
  · exact algorithmQ1dV5_dLo_overshoot_le_vTop_of_phase1b_no_fire
      uHi uLo vTop h_fire

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bBound

  The V5 Phase-1b post-2nd-correction dLo bound (algorithm-level form) —
  V5.4.1's headline theorem at the `div128Quot_phase2b_q0'` interface:

    Q1dd_alg.toNat * dLo.toNat ≤ Rhatdd_alg.toNat * 2^32 + un1.toNat

  where `Q1dd_alg := div128Quot_phase2b_q0' Q1d Rhatd dLo un1` and
  `Rhatdd_alg` is the corresponding `rhat` update — both at the V5
  algorithm level (over `algorithmQ1dV5` / `algorithmRhatdV5`).

  Composes the V5.4.0 chain (algorithm bundles, cap bounds, no-wrap,
  Euclidean, overshoot) with the generic
  `div128Quot_phase2b_q0'_dLo_bound_{fire,no_fire}` helpers from
  `CallSkipLowerBoundV4/Phase2bFireBound.lean` and `Phase2bNoFireBound.lean`.

  The irreducible-form wrapper `divKTrialCallV5_phase1b_dLo_bound`
  (matching the V5.4.1 bead's literal statement on `divKTrialCallV5Q1dd`
  / `divKTrialCallV5Rhatdd`) is left to a follow-up bead: the
  let-binding factoring between V5.2's `divKTrialCallV5Q1dd_eq_phase2b`
  (top-level lets) and the algorithm-level form (lets nested in
  arguments) doesn't normalize via `rfl`. Future bead can either
  refactor V5.2's eq_phase2b to factor lets identically, or do the
  bridge via per-component equational reasoning.

  Mirror of v4's `divKTrialCallV4_phase1b_dLo_bound`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:988`).

  Bead `evm-asm-wbc4i.4.1` (V5.4.1, algorithm-level half).
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **V5.4.1 algorithm-level**: Phase-1b 2nd-correction dLo bound for V5
    at the `div128Quot_phase2b_q0'` interface.

    Both `Q1dd_alg` and `Rhatdd_alg` are computed from `(Q1d, Rhatd)`
    via the generic phase2b_q0' helper and its corresponding `rhat`
    update; the bound holds unconditionally under normalisation. -/
theorem algorithmQ1dV5_phase1b_dLo_bound
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let q := algorithmQ1dV5 uHi uLo vTop
    let rhat := algorithmRhatdV5 uHi uLo vTop
    let dHi := divKTrialCallV5DHi vTop
    let dLo := divKTrialCallV5DLo vTop
    let un := divKTrialCallV5Un1 uLo
    (div128Quot_phase2b_q0' q rhat dLo un).toNat * dLo.toNat ≤
      (if rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
          BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
        rhat + dHi else rhat).toNat * 2^32 + un.toNat := by
  intro q rhat dHi dLo un
  have h_q_lt : q.toNat < 2^32 := algorithmQ1dV5_lt_pow32 uHi uLo vTop
  have h_q_le : q.toNat ≤ 2^32 + 1 := by omega
  have h_dLo_lt : dLo.toNat < 2^32 := divKTrialCallV5DLo_lt_pow32 vTop
  have h_un_lt : un.toNat < 2^32 := divKTrialCallV5Un1_lt_pow32 uLo
  have h_dHi_lt : dHi.toNat < 2^32 := divKTrialCallV5DHi_lt_pow32 vTop
  have h_no_wrap_q : (q * dLo).toNat = q.toNat * dLo.toNat :=
    algorithmQ1dV5_dLo_no_wrap uHi uLo vTop
  have h_overshoot : q.toNat * dLo.toNat ≤
      rhat.toNat * 2^32 + un.toNat + dHi.toNat * 2^32 + dLo.toNat :=
    algorithmQ1dV5_dLo_overshoot_le_vTop_closed uHi uLo vTop
      hvTop_ge huHi_lt_vTop
  by_cases h_guard : rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
    BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
  · -- Fire case
    have h_guard_full := h_guard
    obtain ⟨h_rhat_hi_zero, h_ult⟩ := h_guard
    have h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat :=
      phase2b_rhat_add_dHi_no_wrap_of_hi_zero rhat dHi h_rhat_hi_zero h_dHi_lt
    have h_q_pos : q.toNat ≥ 1 :=
      phase2b_q_pos_of_fire_ult q dLo ((rhat <<< (32 : BitVec 6).toNat) ||| un) h_ult
    obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_fire_case
      q rhat dLo dHi un h_no_wrap_rhat h_q_pos h_rhat_hi_zero h_ult h_overshoot
    rw [h_qeq, if_pos h_guard_full]
    exact h_bound
  · -- No-fire case
    obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_no_fire
      q rhat dLo un h_q_le h_dLo_lt h_un_lt h_no_wrap_q h_guard
    rw [h_qeq, if_neg h_guard]
    exact h_bound

/-- Bridge: `divKTrialCallV5Q1dd` = `phase2b_q0'` on `(algorithmQ1d, algorithmRhatd)`.

    Sidesteps the let-factoring mismatch via case-split on `hi1`: in each
    branch, V5.2's symbolic `q1c` reference inside `rhatc` reduces to the
    same concrete value as `algorithmRhatcV5_unfold`'s direct `q1cCap`
    substitution. Bead `evm-asm-wbc4i.4.1.1` (V5.4.1.1). -/
theorem divKTrialCallV5Q1dd_eq_alg (uHi uLo vTop : Word) :
    divKTrialCallV5Q1dd uHi uLo vTop =
      div128Quot_phase2b_q0'
        (algorithmQ1dV5 uHi uLo vTop)
        (algorithmRhatdV5 uHi uLo vTop)
        (divKTrialCallV5DLo vTop)
        (divKTrialCallV5Un1 uLo) := by
  rw [divKTrialCallV5Q1dd_eq_phase2b]
  rw [algorithmQ1dV5_unfold, algorithmRhatdV5_unfold]
  rw [algorithmQ1cV5_unfold, algorithmRhatcV5_unfold]
  by_cases h : rv64_divu uHi (divKTrialCallV5DHi vTop) >>>
      (32 : BitVec 6).toNat = (0 : Word)
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]

/-- Bridge for `divKTrialCallV5Rhatdd` — NESTED form to match V5.2's
    eq_phase2b RHS exactly. -/
theorem divKTrialCallV5Rhatdd_eq_alg (uHi uLo vTop : Word) :
    divKTrialCallV5Rhatdd uHi uLo vTop =
      (if algorithmRhatdV5 uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word) then
        let qDlo2 := algorithmQ1dV5 uHi uLo vTop * divKTrialCallV5DLo vTop
        let rhatUn1' :=
          (algorithmRhatdV5 uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo
        if BitVec.ult rhatUn1' qDlo2 then
          algorithmRhatdV5 uHi uLo vTop + divKTrialCallV5DHi vTop
        else algorithmRhatdV5 uHi uLo vTop
      else algorithmRhatdV5 uHi uLo vTop) := by
  rw [divKTrialCallV5Rhatdd_eq_phase2b]
  rw [algorithmQ1dV5_unfold, algorithmRhatdV5_unfold]
  rw [algorithmQ1cV5_unfold, algorithmRhatcV5_unfold]
  by_cases h : rv64_divu uHi (divKTrialCallV5DHi vTop) >>>
      (32 : BitVec 6).toNat = (0 : Word)
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]

/-- **V5.4.1 irreducible-form**: Phase-1b 2nd-correction dLo bound for V5
    on the literal `divKTrialCallV5Q1dd` / `divKTrialCallV5Rhatdd`
    irreducibles. Wraps the algorithm-level version via the two
    case-split bridges. Closes the V5.4.1 bead's literal statement. -/
theorem divKTrialCallV5_phase1b_dLo_bound
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV5DLo vTop).toNat ≤
      (divKTrialCallV5Rhatdd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV5Un1 uLo).toNat := by
  rw [divKTrialCallV5Q1dd_eq_alg, divKTrialCallV5Rhatdd_eq_alg]
  -- Convert nested if (from Rhatdd bridge) to flat-AND if (algorithm-level statement).
  have h_alg := algorithmQ1dV5_phase1b_dLo_bound uHi uLo vTop hvTop_ge huHi_lt_vTop
  dsimp only at h_alg ⊢
  by_cases h_outer : algorithmRhatdV5 uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word)
  · rw [if_pos h_outer]
    by_cases h_inner :
        BitVec.ult
          ((algorithmRhatdV5 uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo)
          (algorithmQ1dV5 uHi uLo vTop * divKTrialCallV5DLo vTop)
    · rw [if_pos h_inner]
      rw [if_pos ⟨h_outer, h_inner⟩] at h_alg
      exact h_alg
    · rw [if_neg h_inner]
      rw [if_neg (fun h => h_inner h.2)] at h_alg
      exact h_alg
  · rw [if_neg h_outer]
    rw [if_neg (fun h => h_outer h.1)] at h_alg
    exact h_alg

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1ddBound

  V5.4.2: the V5 post-Phase-1b-2nd-correction quotient does not overshoot
  the abstract first 128/64 quotient digit:

    Q1dd.toNat ≤ q_true_1 = (uHi * 2^32 + un1) / vTop

  Builds on V5.4.1 (`divKTrialCallV5_phase1b_dLo_bound`) and the V5.4.0
  Euclidean foundations to derive the Nat-level inequality.

  Mirror of v4's `divKTrialCallV4Q1dd_le_q_true_1`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:1105`).

  Bead `evm-asm-wbc4i.4.2` (V5.4.2).
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Phase-1b 2-correction Euclidean identity at the V5 irreducible level:
    `Q1dd * dHi + Rhatdd = uHi`. Lifts the algorithm-level
    `algorithmQ1dV5_rhatd_post` (V5.4.0.12, post-1st-correction) to the
    post-2nd-correction Q1dd/Rhatdd irreducibles. -/
theorem divKTrialCallV5Q1dd_rhatdd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (divKTrialCallV5Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat +
      (divKTrialCallV5Rhatdd uHi uLo vTop).toNat =
      uHi.toNat := by
  have h_pre := algorithmQ1dV5_rhatd_post uHi uLo vTop hvTop_ge
  rw [divKTrialCallV5Q1dd_eq_alg, divKTrialCallV5Rhatdd_eq_alg]
  set q := algorithmQ1dV5 uHi uLo vTop with hq
  set rhat := algorithmRhatdV5 uHi uLo vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  -- The Q1dd bridge gives `div128Quot_phase2b_q0' q rhat dLo un`.
  -- The Rhatdd bridge gives nested-if form.
  -- Case-split on the Phase-1b 2nd correction guard (rhat>>>32 = 0 AND BLTU).
  by_cases h_outer : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · rw [if_pos h_outer]
    by_cases h_inner :
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · -- Fire: Q1dd = q + signExtend12 4095 (= q - 1 if q ≥ 1), Rhatdd = rhat + dHi.
      rw [if_pos h_inner]
      have h_dHi_lt : dHi.toNat < 2^32 := divKTrialCallV5DHi_lt_pow32 vTop
      have h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat :=
        phase2b_rhat_add_dHi_no_wrap_of_hi_zero rhat dHi h_outer h_dHi_lt
      have h_q_pos : q.toNat ≥ 1 :=
        phase2b_q_pos_of_fire_ult q dLo
          ((rhat <<< (32 : BitVec 6).toNat) ||| un) h_inner
      -- div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 when fire.
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 :=
        div128Quot_phase2b_q0'_eq_q_dec_of_fire q rhat dLo un h_outer h_inner
      rw [h_q1dd_eq]
      have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
      have h_q_dec : (q + signExtend12 4095).toNat = q.toNat - 1 := by
        rw [BitVec.toNat_add, h_se]
        have h_sum : q.toNat + (2^64 - 1) = (q.toNat - 1) + 2^64 := by omega
        rw [h_sum, Nat.add_mod_right]
        rw [Nat.mod_eq_of_lt (by have : q.toNat < 2^64 := q.isLt; omega)]
      rw [h_q_dec, h_no_wrap_rhat]
      -- Goal: (q - 1) * dHi + (rhat + dHi) = uHi
      -- = q * dHi - dHi + rhat + dHi = q * dHi + rhat = uHi.
      have h_rearrange :
          (q.toNat - 1) * dHi.toNat + (rhat.toNat + dHi.toNat) =
            q.toNat * dHi.toNat + rhat.toNat := by
        have hq_eq : q.toNat = (q.toNat - 1) + 1 := by omega
        calc
          (q.toNat - 1) * dHi.toNat + (rhat.toNat + dHi.toNat)
              = ((q.toNat - 1) * dHi.toNat + dHi.toNat) + rhat.toNat := by omega
            _ = ((q.toNat - 1) + 1) * dHi.toNat + rhat.toNat := by ring
            _ = q.toNat * dHi.toNat + rhat.toNat := by rw [← hq_eq]
      rw [h_rearrange]
      exact h_pre
    · -- No-fire BLTU: Q1dd = q, Rhatdd = rhat.
      rw [if_neg h_inner]
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_outer, if_neg h_inner]
      rw [h_q1dd_eq]
      exact h_pre
  · -- No-fire outer: Q1dd = q (phase2b_q0' guard fails), Rhatdd = rhat.
    rw [if_neg h_outer]
    have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
      unfold div128Quot_phase2b_q0'
      rw [if_neg h_outer]
    rw [h_q1dd_eq]
    exact h_pre

/-- **V5.4.2 headline**: the V5 Phase-1b 2-correction quotient digit
    does not overshoot the abstract first 128/64 quotient digit. -/
theorem divKTrialCallV5Q1dd_le_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Q1dd uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat := by
  set q := divKTrialCallV5Q1dd uHi uLo vTop with hq
  set rhat := divKTrialCallV5Rhatdd uHi uLo vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un1 := divKTrialCallV5Un1 uLo with hun1
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    rw [hq, hrhat, hdHi]
    exact divKTrialCallV5Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_dLo_bound : q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un1.toNat := by
    rw [hq, hrhat, hdLo, hun1]
    exact divKTrialCallV5_phase1b_dLo_bound uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_mul_le : q.toNat * vTop.toNat ≤ uHi.toNat * 2^32 + un1.toNat := by
    rw [h_vTop_decomp]
    calc q.toNat * (dHi.toNat * 2^32 + dLo.toNat)
        = q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by ring
      _ ≤ q.toNat * dHi.toNat * 2^32 + (rhat.toNat * 2^32 + un1.toNat) := by omega
      _ = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by ring
      _ = uHi.toNat * 2^32 + un1.toNat := by rw [h_post]
  have hvTop_pos : 0 < vTop.toNat := by omega
  exact (Nat.le_div_iff_mul_le hvTop_pos).2 h_mul_le

end EvmAsm.Evm64
