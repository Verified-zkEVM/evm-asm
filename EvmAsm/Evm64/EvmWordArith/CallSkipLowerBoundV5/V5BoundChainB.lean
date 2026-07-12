/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainB

  Shared declaration home for the V5 lower-bound proof chain.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainA
import EvmAsm.Evm64.EvmWordArith.Div128KnuthLower
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cLB

  Knuth-A lower bound for V5's Phase-1a-corrected quotient in the
  wide-uHi case (the V4 exclusion zone): `Q1c ≥ q_true_1` when
  `uHi ≥ dHi * 2^32`.

  The narrow case (`uHi < dHi * 2^32`) reduces to the v2 Knuth-A LB
  `algorithmQ1Prime_ge_q_true_1`; the wide case here is the V5-specific
  half that wasn't accessible under v4 (because v4's q1c = q1 - 1 in
  the wide regime could undershoot, motivating the wide-uHi
  counterexamples in PR #7077).

  Bead `evm-asm-wbc4i.5.4` (V5.5.0.1). Prerequisite for V5.5.1.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- In the wide-uHi regime (`uHi ≥ dHi*2^32`), the V5 cap forces
    `Q1c = 2^32 - 1`. Combined with `q_true_1 < 2^32` (from `uHi < vTop`),
    this gives the Knuth-A LB unconditionally for the wide case. -/
theorem algorithmQ1cV5_ge_q_true_1_of_uHi_ge_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_ge_dHi_pow32 : uHi.toNat ≥ (divKTrialCallV5DHi vTop).toNat * 2^32) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (algorithmQ1cV5 uHi vTop).toNat := by
  -- Q1c = 2^32 - 1 in this case (cap fires).
  have h_dHi_lt : (divKTrialCallV5DHi vTop).toNat < 2^32 :=
    divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_ge : (divKTrialCallV5DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_ne : divKTrialCallV5DHi vTop ≠ 0 := by
    intro h
    have : (divKTrialCallV5DHi vTop).toNat = 0 := by rw [h]; rfl
    omega
  -- q1 = uHi / dHi.
  have h_q1_eq : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat =
      uHi.toNat / (divKTrialCallV5DHi vTop).toNat := by
    unfold rv64_divu
    have : ¬ (divKTrialCallV5DHi vTop == 0#64) := by simpa using h_dHi_ne
    rw [if_neg this, BitVec.toNat_udiv]
  -- uHi ≥ dHi*2^32 ⇒ q1 = uHi/dHi ≥ 2^32 ⇒ hi1 = q1>>>32 ≠ 0.
  have h_q1_ge : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat ≥ 2^32 := by
    rw [h_q1_eq]
    have h_div : uHi.toNat / (divKTrialCallV5DHi vTop).toNat ≥
        ((divKTrialCallV5DHi vTop).toNat * 2^32) / (divKTrialCallV5DHi vTop).toNat :=
      Nat.div_le_div_right huHi_ge_dHi_pow32
    have h_eq : ((divKTrialCallV5DHi vTop).toNat * 2^32) /
        (divKTrialCallV5DHi vTop).toNat = 2^32 :=
      Nat.mul_div_cancel_left _ (by omega)
    omega
  have h_hi1_ne : (rv64_divu uHi (divKTrialCallV5DHi vTop)) >>>
      (32 : BitVec 6).toNat ≠ (0 : Word) := by
    intro h
    have h_nat : ((rv64_divu uHi (divKTrialCallV5DHi vTop)) >>>
        (32 : BitVec 6).toNat).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow] at h_nat
    have h_div : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat / 2^32 = 0 := h_nat
    omega
  -- Q1c = q1cCap = 2^32 - 1.
  have h_q1c : (algorithmQ1cV5 uHi vTop).toNat = 2^32 - 1 := by
    rw [algorithmQ1cV5_unfold]
    dsimp only
    rw [if_neg h_hi1_ne]
    decide
  -- q_true_1 < 2^32 (from uHi < vTop and vTop ≥ 1).
  have h_vTop_pos : vTop.toNat ≥ 1 := by omega
  have h_un1_lt : (divKTrialCallV5Un1 uLo).toNat < 2^32 :=
    divKTrialCallV5Un1_lt_pow32 uLo
  have h_num_lt : uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat <
      vTop.toNat * 2^32 := by
    have h_uHi_le : uHi.toNat ≤ vTop.toNat - 1 := by omega
    have h_uHi_mul : uHi.toNat * 2^32 ≤ (vTop.toNat - 1) * 2^32 :=
      Nat.mul_le_mul_right _ h_uHi_le
    -- vTop ≥ 2^63 ⇒ vTop * 2^32 ≥ 2^95 ≫ uHi * 2^32 + un1 < (vTop-1)*2^32 + 2^32.
    have h_vTop_mul_ge : vTop.toNat * 2^32 ≥ 2^32 := by
      have : vTop.toNat ≥ 1 := h_vTop_pos
      nlinarith
    have h1 : (vTop.toNat - 1) * 2^32 + 2^32 = vTop.toNat * 2^32 := by
      have hv_eq : vTop.toNat = (vTop.toNat - 1) + 1 := by omega
      calc (vTop.toNat - 1) * 2^32 + 2^32
          = ((vTop.toNat - 1) + 1) * 2^32 := by ring
        _ = vTop.toNat * 2^32 := by rw [← hv_eq]
    linarith
  have h_q_true_lt : (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
      vTop.toNat < 2^32 :=
    Nat.div_lt_of_lt_mul h_num_lt
  -- Combine.
  rw [h_q1c]
  omega

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cLBUncond

  V5.5.0.2: unconditional Knuth-A lower bound for V5's Phase-1a-corrected
  quotient: `Q1c ≥ q_true_1`.

  Case-split on `hi1 = q1 >>> 32`:
  - `hi1 = 0` (narrow uHi): Q1c = q1; use existing `div128Quot_q1c_ge_q_true_1`
    from `Div128KnuthLower.lean` (which holds for q1 - 1 form, but the
    narrow branch is q1 in both forms).
  - `hi1 ≠ 0` (wide uHi, ≥ dHi*2^32): use V5.5.0.1.

  Bead `evm-asm-wbc4i.5.5` (V5.5.0.2). Prerequisite for V5.5.1.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem algorithmQ1cV5_ge_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (algorithmQ1cV5 uHi vTop).toNat := by
  have h_dHi_lt : (divKTrialCallV5DHi vTop).toNat < 2^32 :=
    divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_ge : (divKTrialCallV5DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_ne : divKTrialCallV5DHi vTop ≠ 0 := by
    intro h
    have : (divKTrialCallV5DHi vTop).toNat = 0 := by rw [h]; rfl
    omega
  have h_un1_lt : (divKTrialCallV5Un1 uLo).toNat < 2^32 :=
    divKTrialCallV5Un1_lt_pow32 uLo
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
    unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  by_cases h_wide : uHi.toNat ≥ (divKTrialCallV5DHi vTop).toNat * 2^32
  · -- Wide case: V5.5.0.1.
    exact algorithmQ1cV5_ge_q_true_1_of_uHi_ge_dHi_pow32 uHi uLo vTop
      hvTop_ge huHi_lt_vTop h_wide
  · -- Narrow case: Q1c = q1, use the existing Div128KnuthLower fact.
    push Not at h_wide
    have h_uHi_lt_decomp : uHi.toNat <
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
          (divKTrialCallV5DLo vTop).toNat := by
      rw [← h_vTop_decomp]; exact huHi_lt_vTop
    -- div128Quot_q1c_ge_q_true_1 uses v2's cap form (q1 - 1), but in the
    -- narrow case (hi1 = 0), both v2 and V5 caps reduce to q1c = q1.
    have h_q1_ge :
        (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
          ((divKTrialCallV5DHi vTop).toNat * 2^32 +
            (divKTrialCallV5DLo vTop).toNat) ≤
        (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat := by
      exact div128Quot_q1_ge_q_true_1 uHi (divKTrialCallV5DHi vTop)
        (divKTrialCallV5DLo vTop) (divKTrialCallV5Un1 uLo)
        h_dHi_ne h_un1_lt
    rw [h_vTop_decomp]
    -- Need: q_true_1 ≤ Q1c.toNat. We have q_true_1 ≤ q1.toNat. Show Q1c = q1
    -- when hi1 = 0 (which follows from h_wide_neg : uHi < dHi*2^32).
    have h_q1_eq : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat =
        uHi.toNat / (divKTrialCallV5DHi vTop).toNat := by
      unfold rv64_divu
      have : ¬ (divKTrialCallV5DHi vTop == 0#64) := by simpa using h_dHi_ne
      rw [if_neg this, BitVec.toNat_udiv]
    have h_q1_lt : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat < 2^32 := by
      rw [h_q1_eq]
      exact Nat.div_lt_of_lt_mul (by linarith)
    have h_hi1_zero : rv64_divu uHi (divKTrialCallV5DHi vTop) >>>
        (32 : BitVec 6).toNat = (0 : Word) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
          Nat.shiftRight_eq_div_pow]
      show (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat / 2^32 = 0
      exact Nat.div_eq_of_lt h_q1_lt
    -- Q1c = q1 in narrow case.
    have h_q1c_eq : (algorithmQ1cV5 uHi vTop).toNat =
        (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat := by
      rw [algorithmQ1cV5_unfold]
      dsimp only
      rw [if_pos h_hi1_zero]
    rw [h_q1c_eq]
    exact h_q1_ge

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cStrictLT

  V5.5.0.3: when V5's Phase-1b 1st correction fires, the abstract first
  quotient digit is STRICTLY less than the Phase-1a-corrected quotient:

    algorithmPhase1bFireV5 ⇒ q_true_1 < Q1c.toNat

  Uses the generic `phase1b_fire_q_true_1_lt_q_nat` helper from
  `CallSkipLowerBoundV4/Phase1bBound.lean` + Q1c Euclidean (V5.4.0.7)
  + bit-level no-wrap facts.

  Bead `evm-asm-wbc4i.5.6` (V5.5.0.3). Prerequisite for V5.5.1 to show
  Q1d = Q1c - 1 ≥ q_true_1 in the fire case.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

theorem algorithmQ1cV5_q_true_1_lt_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat <
      (algorithmQ1cV5 uHi vTop).toNat := by
  -- Extract fire's two conditions.
  rw [algorithmPhase1bFireV5_unfold] at h_fire
  rw [algorithmRhatUn1cV5_unfold] at h_fire
  obtain ⟨h_rhat_hi_zero, h_ult⟩ := h_fire
  -- Setup names.
  set q := algorithmQ1cV5 uHi vTop with hq
  set rhat := algorithmRhatcV5 uHi vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  -- Get vTop decomposition.
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  -- Get Q1c Euclidean (V5.4.0.7): q * dHi + rhat = uHi.
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    rw [hq, hrhat, hdHi]
    exact algorithmQ1cV5_rhatc_post uHi vTop hvTop_ge
  -- rhat < 2^32 from h_rhat_hi_zero.
  have h_rhat_lt : rhat.toNat < 2^32 := by
    have h_nat : (rhat >>> (32 : BitVec 6).toNat).toNat = 0 := by
      rw [h_rhat_hi_zero]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow] at h_nat
    have : rhat.toNat < 2^64 := rhat.isLt
    omega
  have h_un_lt : un.toNat < 2^32 := by
    rw [hun]; exact divKTrialCallV5Un1_lt_pow32 uLo
  -- (rhat <<< 32 ||| un).toNat = rhat * 2^32 + un.
  have h_lhs_toNat :
      (((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat) =
        rhat.toNat * 2^32 + un.toNat := by
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
    exact halfword_combine rhat un h_rhat_lt h_un_lt
  -- (q * dLo).toNat = q * dLo (no-wrap, V5.4.0.5).
  have h_rhs_toNat : (q * dLo).toNat = q.toNat * dLo.toNat := by
    rw [hq, hdLo]; exact algorithmQ1cV5_dLo_no_wrap uHi vTop
  -- Convert BLTU to Nat-level <.
  have h_ult_nat :
      rhat.toNat * 2^32 + un.toNat < q.toNat * dLo.toNat := by
    have h_word : ((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat <
        (q * dLo).toNat := by
      simpa [BitVec.ult, hq, hrhat, hdLo, hun] using h_ult
    rw [h_lhs_toNat, h_rhs_toNat] at h_word
    exact h_word
  -- Apply generic phase1b_fire_q_true_1_lt_q_nat.
  have h_core := phase1b_fire_q_true_1_lt_q_nat
    uHi.toNat un.toNat dHi.toNat dLo.toNat q.toNat rhat.toNat
    (by rw [← h_vTop_decomp]; omega)
    h_post h_ult_nat
  rw [← h_vTop_decomp] at h_core
  exact h_core

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dLB

  V5.5.0.4: unconditional Knuth-A LB on V5's post-Phase-1b-1st-correction
  quotient: `Q1d ≥ q_true_1`.

  Composes V5.5.0.2 (Q1c ≥ q_true_1) + V5.5.0.3 (1st-fire ⇒ strict)
  via case-split on the Phase-1b 1st correction firing:
  - No-fire: Q1d = Q1c ≥ q_true_1.
  - Fire: Q1d = Q1c - 1; strict gives q_true_1 < Q1c, so q_true_1 ≤ Q1c - 1 = Q1d.

  Bead `evm-asm-wbc4i.5.7` (V5.5.0.4). Prerequisite for V5.5.1.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem algorithmQ1dV5_ge_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (algorithmQ1dV5 uHi uLo vTop).toNat := by
  -- Knuth-A LB on Q1c (V5.5.0.2).
  have h_q1c_ge : (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
      vTop.toNat ≤ (algorithmQ1cV5 uHi vTop).toNat :=
    algorithmQ1cV5_ge_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Case-split on Phase-1b 1st correction.
  by_cases h_fire : algorithmPhase1bFireV5 uHi uLo vTop
  · -- Fire: Q1d = Q1c + signExtend12 4095 (= Q1c - 1 mod 2^64).
    rw [algorithmQ1dV5_unfold]
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
    rw [if_pos h_fire_cond]
    -- Strict overshoot (V5.5.0.3): q_true_1 < Q1c.
    have h_strict :=
      algorithmQ1cV5_q_true_1_lt_of_phase1b_fire uHi uLo vTop hvTop_ge h_fire
    -- (Q1c + signExtend12 4095).toNat = Q1c.toNat - 1 (no-wrap since Q1c ≥ 1).
    have h_q1c_lt : (algorithmQ1cV5 uHi vTop).toNat < 2^32 :=
      algorithmQ1cV5_lt_pow32 uHi vTop
    have h_q1c_pos : (algorithmQ1cV5 uHi vTop).toNat ≥ 1 :=
      Nat.one_le_iff_ne_zero.mpr (fun h => by
        rw [h] at h_strict; exact Nat.not_lt_zero _ h_strict)
    have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se]
    have h_sum : (algorithmQ1cV5 uHi vTop).toNat + (2^64 - 1) =
        ((algorithmQ1cV5 uHi vTop).toNat - 1) + 2^64 := by omega
    have h_lt_pow64 : (algorithmQ1cV5 uHi vTop).toNat - 1 < 2^64 := by
      have : (algorithmQ1cV5 uHi vTop).toNat < 2^32 := h_q1c_lt
      have : (2 : Nat)^32 < 2^64 := by decide
      omega
    rw [h_sum, Nat.add_mod_right, Nat.mod_eq_of_lt h_lt_pow64]
    exact Nat.le_sub_one_of_lt h_strict
  · -- No-fire: Q1d = Q1c, LB is direct.
    rw [algorithmQ1dV5_eq_q1c_of_phase1b_no_fire uHi uLo vTop h_fire]
    exact h_q1c_ge

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dStrictLT

  V5.5.0.5: when V5's Phase-1b 2nd correction fires, the abstract first
  quotient digit is STRICTLY less than the post-1st-correction quotient
  Q1d.

  Mirror of v4's `algorithmQ1dV4_q_true_1_lt_of_phase2b_fire`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:1161`).

  Bead `evm-asm-wbc4i.5.8` (V5.5.0.5). Prerequisite for V5.5.1 to show
  Q1dd = Q1d - 1 ≥ q_true_1 in the 2nd-correction fire case.
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

theorem algorithmQ1dV5_q_true_1_lt_of_phase2b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (h_rhat_hi_zero :
      algorithmRhatdV5 uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_ult :
      BitVec.ult ((algorithmRhatdV5 uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV5Un1 uLo)
        (algorithmQ1dV5 uHi uLo vTop * divKTrialCallV5DLo vTop)) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat <
      (algorithmQ1dV5 uHi uLo vTop).toNat := by
  set q := algorithmQ1dV5 uHi uLo vTop with hq
  set rhat := algorithmRhatdV5 uHi uLo vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  -- vTop decomposition.
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  -- Q1d Euclidean (V5.4.0.12).
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    rw [hq, hrhat, hdHi]
    exact algorithmQ1dV5_rhatd_post uHi uLo vTop hvTop_ge
  -- rhat < 2^32 from h_rhat_hi_zero.
  have h_rhat_lt : rhat.toNat < 2^32 := by
    have h_nat : (rhat >>> (32 : BitVec 6).toNat).toNat = 0 := by
      rw [h_rhat_hi_zero]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow] at h_nat
    have : rhat.toNat < 2^64 := rhat.isLt
    omega
  have h_un_lt : un.toNat < 2^32 := by
    rw [hun]; exact divKTrialCallV5Un1_lt_pow32 uLo
  -- (rhat <<< 32 ||| un).toNat = rhat * 2^32 + un.
  have h_lhs_toNat :
      (((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat) =
        rhat.toNat * 2^32 + un.toNat := by
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
    exact halfword_combine rhat un h_rhat_lt h_un_lt
  -- (q * dLo).toNat = q * dLo (V5.4.0.13).
  have h_rhs_toNat : (q * dLo).toNat = q.toNat * dLo.toNat := by
    rw [hq, hdLo]; exact algorithmQ1dV5_dLo_no_wrap uHi uLo vTop
  -- BLTU → Nat-level <.
  have h_ult_nat :
      rhat.toNat * 2^32 + un.toNat < q.toNat * dLo.toNat := by
    have h_word : ((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat <
        (q * dLo).toNat := by
      simpa [BitVec.ult, hq, hrhat, hdLo, hun] using h_ult
    rw [h_lhs_toNat, h_rhs_toNat] at h_word
    exact h_word
  -- Apply generic phase1b_fire_q_true_1_lt_q_nat.
  have h_core := phase1b_fire_q_true_1_lt_q_nat
    uHi.toNat un.toNat dHi.toNat dLo.toNat q.toNat rhat.toNat
    (by rw [← h_vTop_decomp]; omega)
    h_post h_ult_nat
  rw [← h_vTop_decomp] at h_core
  exact h_core

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1ddLB

  **V5.5.1 headline**: the V5 post-Phase-1b-2nd-correction quotient does
  not undershoot the abstract first 128/64 quotient digit:

    Q1dd.toNat ≥ q_true_1

  Unconditional under `vTop ≥ 2^63` and `uHi < vTop` (no `uHi < 2^63`
  exclusion — the V5 cap eliminates v4's wide-uHi counterexamples from
  PR #7077).

  Compose:
  - V5.5.0.4 (Q1d ≥ q_true_1).
  - V5.5.0.5 (2nd-fire ⇒ q_true_1 < Q1d strict) for the fire case.
  - V5.4.1.1 bridges (`divKTrialCallV5{Q1dd,Rhatdd}_eq_alg`) to lift to
    irreducible form.

  Mirror of v4's `divKTrialCallV4Q1dd_ge_q_true_1_of_uHi_lt_pow63`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:1213`) but STRONGER: V5
  drops the `uHi < 2^63` precondition.

  Bead `evm-asm-wbc4i.5.1` (V5.5.1).
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divKTrialCallV5Q1dd_ge_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (divKTrialCallV5Q1dd uHi uLo vTop).toNat := by
  -- Q1d ≥ q_true_1 unconditionally (V5.5.0.4).
  have h_q1d_ge : (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
      vTop.toNat ≤ (algorithmQ1dV5 uHi uLo vTop).toNat :=
    algorithmQ1dV5_ge_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Bridge: divKTrialCallV5Q1dd = div128Quot_phase2b_q0' Q1d Rhatd dLo un.
  rw [divKTrialCallV5Q1dd_eq_alg]
  set q := algorithmQ1dV5 uHi uLo vTop with hq
  set rhat := algorithmRhatdV5 uHi uLo vTop with hrhat
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  set qTrue := (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat
    with hqTrue
  -- Case-split on the 2nd correction guard.
  by_cases h_outer : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · by_cases h_inner :
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · -- 2nd correction FIRES: phase2b_q0' = q + signExtend12 4095 = q - 1.
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 :=
        div128Quot_phase2b_q0'_eq_q_dec_of_fire q rhat dLo un h_outer h_inner
      rw [h_q1dd_eq]
      -- Strict overshoot (V5.5.0.5): q_true_1 < Q1d.
      have h_strict : qTrue < q.toNat := by
        rw [hqTrue, hq]
        exact algorithmQ1dV5_q_true_1_lt_of_phase2b_fire uHi uLo vTop
          hvTop_ge h_outer h_inner
      -- Q1d < 2^32 (V5.4.0.6).
      have h_q_lt : q.toNat < 2^32 := by
        rw [hq]; exact algorithmQ1dV5_lt_pow32 uHi uLo vTop
      have h_q_pos : q.toNat ≥ 1 :=
        Nat.one_le_iff_ne_zero.mpr (fun h => by
          rw [h] at h_strict; exact Nat.not_lt_zero _ h_strict)
      -- (q + signExtend12 4095).toNat = q.toNat - 1 mod 2^64 (no-wrap).
      have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
      rw [BitVec.toNat_add, h_se]
      have h_sum : q.toNat + (2^64 - 1) = (q.toNat - 1) + 2^64 := by omega
      have h_lt_pow64 : q.toNat - 1 < 2^64 := by
        have h32 : (2 : Nat)^32 < 2^64 := by decide
        omega
      rw [h_sum, Nat.add_mod_right, Nat.mod_eq_of_lt h_lt_pow64]
      exact Nat.le_sub_one_of_lt h_strict
    · -- 2nd correction doesn't fire (BLTU false): phase2b_q0' = q.
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_outer, if_neg h_inner]
      rw [h_q1dd_eq]
      exact h_q1d_ge
  · -- Outer guard false: phase2b_q0' = q.
    have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
      unfold div128Quot_phase2b_q0'
      rw [if_neg h_outer]
    rw [h_q1dd_eq]
    exact h_q1d_ge

/-- **V5 Knuth-A pin**: the Phase-1b 2-correction quotient digit equals
    the abstract first 128/64 quotient digit EXACTLY:

      Q1dd.toNat = (uHi * 2^32 + un1) / vTop

    Direct `le_antisymm` of V5.4.2 (UB) and V5.5.1 (LB). Unconditional —
    no `uHi < 2^63` exclusion. Mirror of v4's
    `divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_pow63`
    (`Phase1bBound.lean:1309`) but STRONGER.

    Bead `evm-asm-wbc4i.5.9` (V5.5.0.6). Useful corollary for V5.4.3 /
    V5.5.2 / V5.6 chain. -/
theorem divKTrialCallV5Q1dd_eq_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Q1dd uHi uLo vTop).toNat =
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat := by
  apply le_antisymm
  · exact divKTrialCallV5Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  · exact divKTrialCallV5Q1dd_ge_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop

end EvmAsm.Evm64

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Un21Bound

  V5.4.3 prereq: `Q1dd * dLo` no-wrap helper at the irreducible level
  (lifts V5.4.0.13's algorithm-level no-wrap through the
  `div128Quot_phase2b_q0'` step).

  V5.4.3 (`divKTrialCallV5Un21 < vTop`) itself has a non-trivial proof
  via the algebraic identity `un21 = (uHi*2^32 + un1) - Q1dd*vTop`,
  which equals `(uHi*2^32 + un1) mod vTop` when `Q1dd = q_true_1`
  (V5.5.0.6). The BitVec `Rhatdd << 32` truncation doesn't break the
  identity because the truncated bits represent `Rhatdd div 2^32 * 2^64`
  which is `0 mod 2^64`. Future iteration ships the headline; this PR
  lands the no-wrap step that the proof composition needs.

  Bead `evm-asm-wbc4i.4.3` (V5.4.3, no-wrap prereq).
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `Q1dd * dLo` no-wrap at the irreducible level. Lifts V5.4.0.13's
    algorithm-level bound (Q1d * dLo ≤ Q1d * dLo < 2^32 * 2^32) through
    `div128Quot_phase2b_q0'`'s monotonicity (Q1dd ≤ Q1d). -/
theorem divKTrialCallV5Q1dd_dLo_no_wrap (uHi uLo vTop : Word) :
    (divKTrialCallV5Q1dd uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (divKTrialCallV5Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV5DLo vTop).toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  -- Q1dd.toNat ≤ algorithmQ1dV5 (via phase2b_q0' monotonicity through
  -- the V5.4.1.1 bridge); algorithmQ1dV5 < 2^32; dLo < 2^32.
  rw [divKTrialCallV5Q1dd_eq_alg]
  have h_q1d_lt : (algorithmQ1dV5 uHi uLo vTop).toNat < 2^32 :=
    algorithmQ1dV5_lt_pow32 uHi uLo vTop
  have h_dLo_lt : (divKTrialCallV5DLo vTop).toNat < 2^32 :=
    divKTrialCallV5DLo_lt_pow32 vTop
  -- div128Quot_phase2b_q0' q rhat dLo un ≤ q at Nat level.
  -- Generic helper-style: phase2b_q0' is either q or q + signExtend12 4095.
  have h_phase2b_le :
      ∀ (q rhat dLo un : Word),
      (div128Quot_phase2b_q0' q rhat dLo un).toNat ≤ q.toNat := by
    intro q rhat dLo un
    unfold div128Quot_phase2b_q0'
    by_cases h_outer : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
    · rw [if_pos h_outer]
      by_cases h_inner : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
      · simp only [h_inner, ↓reduceIte]
        rw [BitVec.toNat_add]
        have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
        rw [h_se]
        by_cases hq : q.toNat = 0
        · -- q = 0 contradicts fire: BLTU x 0 = false for any x.
          exfalso
          have h_q_eq : q = 0 := BitVec.eq_of_toNat_eq hq
          have h_mul_zero : q * dLo = 0 := by rw [h_q_eq]; exact BitVec.zero_mul
          rw [h_mul_zero] at h_inner
          simp [BitVec.ult] at h_inner
        · have h_pos : q.toNat ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq
          have h_sum : q.toNat + (2^64 - 1) = (q.toNat - 1) + 2^64 := by omega
          rw [h_sum, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by have : q.toNat < 2^64 := q.isLt; omega)]
          omega
      · simp only [h_inner, ↓reduceIte, Bool.false_eq_true]
        rfl
    · rw [if_neg h_outer]
  have h_phase2b_q1d := h_phase2b_le (algorithmQ1dV5 uHi uLo vTop)
    (algorithmRhatdV5 uHi uLo vTop) (divKTrialCallV5DLo vTop)
    (divKTrialCallV5Un1 uLo)
  -- Compose: phase2b_q0' result ≤ algorithmQ1dV5 < 2^32, so product < 2^64.
  have h_mul_le :
      (div128Quot_phase2b_q0' (algorithmQ1dV5 uHi uLo vTop)
        (algorithmRhatdV5 uHi uLo vTop) (divKTrialCallV5DLo vTop)
        (divKTrialCallV5Un1 uLo)).toNat * (divKTrialCallV5DLo vTop).toNat ≤
      (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat :=
    Nat.mul_le_mul_right _ h_phase2b_q1d
  have h_prod_bound :
      (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat <
        2^32 * 2^32 := Nat.mul_lt_mul'' h_q1d_lt h_dLo_lt
  calc (div128Quot_phase2b_q0' (algorithmQ1dV5 uHi uLo vTop)
      (algorithmRhatdV5 uHi uLo vTop) (divKTrialCallV5DLo vTop)
      (divKTrialCallV5Un1 uLo)).toNat * (divKTrialCallV5DLo vTop).toNat
      ≤ (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat :=
        h_mul_le
    _ < 2^32 * 2^32 := h_prod_bound
    _ = 2^64 := by norm_num

/-- Like `EvmWord.halfword_combine` but without the `a < 2^32` bound; the
    high word `a` is silently truncated to its low 32 bits. Used for the
    `Rhatdd <<< 32 ||| un1` combine when Rhatdd may be ≥ 2^32. -/
private theorem halfword_combine_truncated (a b : Word) (hb : b.toNat < 2^32) :
    (a <<< (32 : Nat) ||| b).toNat = (a.toNat % 2^32) * 2^32 + b.toNat := by
  have h_disj : a <<< (32 : Nat) &&& b = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases hi : (i : Nat) < 32
    · simp [hi]
    · simp only [hi, decide_false, Bool.not_false, Bool.true_and]
      have hbi : b[i] = false := by
        simp only [BitVec.getElem_eq_testBit_toNat]
        apply Nat.testBit_lt_two_pow
        calc b.toNat < 2 ^ 32 := hb
          _ ≤ 2 ^ (i : Nat) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hbi]
  rw [(BitVec.add_eq_or_of_and_eq_zero (a <<< (32 : Nat)) b h_disj).symm,
      BitVec.toNat_add_of_and_eq_zero h_disj, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  congr 1
  rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide, Nat.mul_mod_mul_right]

/-- **V5.4.3 headline**: the Phase-1 adjusted remainder `un21` satisfies
    `un21 < vTop` unconditionally (no `uHi < 2^63` exclusion). Proof via the
    algebraic identity `un21.toNat = (uHi*2^32 + un1) % vTop`. The `Rhatdd <<< 32`
    truncation is harmless: it shifts the BitVec result by a multiple of 2^64,
    which cancels in the final modular calculation. -/
theorem divKTrialCallV5Un21_lt_vTop
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Un21 uHi uLo vTop).toNat < vTop.toNat := by
  rw [divKTrialCallV5Un21_unfold]
  dsimp only []
  -- Name the irreducible pieces.
  set Q := divKTrialCallV5Q1dd uHi uLo vTop
  set R := divKTrialCallV5Rhatdd uHi uLo vTop
  set dL := divKTrialCallV5DLo vTop with hdL
  set U1 := divKTrialCallV5Un1 uLo
  -- Gather key lemmas.
  have h_Q_eq : Q.toNat = (uHi.toNat * 2^32 + U1.toNat) / vTop.toNat :=
    divKTrialCallV5Q1dd_eq_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_post : Q.toNat * (divKTrialCallV5DHi vTop).toNat + R.toNat = uHi.toNat :=
    divKTrialCallV5Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_dL_bound : Q.toNat * dL.toNat ≤ R.toNat * 2^32 + U1.toNat :=
    divKTrialCallV5_phase1b_dLo_bound uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_QdL_nw : (Q * dL).toNat = Q.toNat * dL.toNat :=
    divKTrialCallV5Q1dd_dLo_no_wrap uHi uLo vTop
  have h_vTop_eq : vTop.toNat = (divKTrialCallV5DHi vTop).toNat * 2^32 + dL.toNat := by
    rw [hdL]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  have h_U1_lt : U1.toNat < 2^32 := divKTrialCallV5Un1_lt_pow32 uLo
  have h_dL_lt : dL.toNat < 2^32 := divKTrialCallV5DLo_lt_pow32 vTop
  -- Q < 2^32.
  have h_Q_lt : Q.toNat < 2^32 := by
    have h_le := divKTrialCallV5Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
    have h_N_lt : uHi.toNat * 2^32 + U1.toNat < vTop.toNat * 2^32 := by nlinarith
    have h_qt_lt : (uHi.toNat * 2^32 + U1.toNat) / vTop.toNat < 2^32 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  have hvTop_pos : 0 < vTop.toNat := by omega
  -- Algebraic identity: R*2^32 + U1 = Q*dL + N%vTop.
  have h_alg : R.toNat * 2^32 + U1.toNat =
      Q.toNat * dL.toNat + (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat := by
    -- N = vTop * Q + rem (division algorithm), vTop * Q = Q * vTop
    have hd := Nat.div_add_mod (uHi.toNat * 2^32 + U1.toNat) vTop.toNat
    -- hd : vTop * (N/vTop) + N%vTop = N
    -- Expand N as Q*dH*2^32 + R*2^32 + U1 and Q*vTop as Q*dH*2^32 + Q*dL.
    have hUH : uHi.toNat * 2^32 =
        Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + R.toNat * 2^32 := by
      calc uHi.toNat * 2^32
          = (Q.toNat * (divKTrialCallV5DHi vTop).toNat + R.toNat) * 2^32 := by
            congr 1; linarith [h_post]
        _ = Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + R.toNat * 2^32 := by ring
    have hQVT : vTop.toNat * ((uHi.toNat * 2^32 + U1.toNat) / vTop.toNat) =
        Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + Q.toNat * dL.toNat := by
      rw [← h_Q_eq, h_vTop_eq]; ring
    linarith
  -- Combine formula: (R<<<32 ||| U1).toNat = (R%2^32)*2^32 + U1.
  have h_comb : ((R <<< (32 : BitVec 6).toNat) ||| U1).toNat =
      (R.toNat % 2^32) * 2^32 + U1.toNat := by
    have h32 : (32 : BitVec 6).toNat = 32 := by decide
    rw [h32]; exact halfword_combine_truncated R U1 h_U1_lt
  -- un21.toNat = ((R%2^32)*2^32 + U1 + 2^64 - Q*dL) % 2^64.
  have h_un21 : ((R <<< (32 : BitVec 6).toNat ||| U1) - Q * dL).toNat =
      ((R.toNat % 2^32) * 2^32 + U1.toNat + 2^64 - Q.toNat * dL.toNat) % 2^64 := by
    rw [BitVec.toNat_sub, h_comb, h_QdL_nw]; congr 1; omega
  rw [h_un21]
  -- Atom abbreviations for omega.
  set A := (R.toNat % 2^32) * 2^32 + U1.toNat with hA
  set B := Q.toNat * dL.toNat with hB
  set rem := (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat with hrem_def
  have hrem_lt : rem < vTop.toNat := Nat.mod_lt _ hvTop_pos
  -- A + k*2^64 = B + rem  (k = R/2^32, from Nat_mul_pow32_split + h_alg).
  have h_decomp : A + (R.toNat / 2^32) * 2^64 = B + rem := by
    have hkey : R.toNat * 2^32 = (R.toNat / 2^32) * 2^64 + (R.toNat % 2^32) * 2^32 :=
      Nat_mul_pow32_split
    linarith [hA, hB, hrem_def, h_alg]
  -- Bounds.
  have h_A_lt : A < 2^64 := by
    have hmod := Nat.mod_lt R.toNat (show 0 < 2^32 from by norm_num)
    nlinarith [hA, h_U1_lt, hmod]
  have h_B_lt : B < 2^64 := by nlinarith [hB, h_Q_lt, h_dL_lt]
  have hrem_lt64 : rem < 2^64 := lt_trans hrem_lt (by have := vTop.isLt; omega)
  -- k ≤ 1.
  have h_k_le_1 : R.toNat / 2^32 ≤ 1 := by omega
  -- Case split k = 0 / k = 1, both giving rem % 2^64 = rem.
  rcases Nat.eq_zero_or_pos (R.toNat / 2^32) with hk0 | hk1_pos
  · have hkB : A + 2^64 - B = rem + 2^64 := by omega
    rw [hkB, Nat.add_mod_right, Nat.mod_eq_of_lt hrem_lt64]
    exact hrem_lt
  · have hk1 : R.toNat / 2^32 = 1 := Nat.le_antisymm h_k_le_1 hk1_pos
    have hkB : A + 2^64 - B = rem := by omega
    rw [hkB, Nat.mod_eq_of_lt hrem_lt64]
    exact hrem_lt

/-- **V5 un21 = r1**: the Phase-1 remainder equals the first mathematical remainder
    `r1 = (uHi*2^32 + un1) % vTop`. Same proof structure as `divKTrialCallV5Un21_lt_vTop`
    ending with equality instead of strict inequality. -/
theorem divKTrialCallV5Un21_eq_r1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Un21 uHi uLo vTop).toNat =
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) % vTop.toNat := by
  rw [divKTrialCallV5Un21_unfold]; dsimp only
  set Q := divKTrialCallV5Q1dd uHi uLo vTop
  set R := divKTrialCallV5Rhatdd uHi uLo vTop
  set dL := divKTrialCallV5DLo vTop with hdL
  set U1 := divKTrialCallV5Un1 uLo
  have h_Q_eq : Q.toNat = (uHi.toNat * 2^32 + U1.toNat) / vTop.toNat :=
    divKTrialCallV5Q1dd_eq_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_post : Q.toNat * (divKTrialCallV5DHi vTop).toNat + R.toNat = uHi.toNat :=
    divKTrialCallV5Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_QdL_nw : (Q * dL).toNat = Q.toNat * dL.toNat :=
    divKTrialCallV5Q1dd_dLo_no_wrap uHi uLo vTop
  have h_vTop_eq : vTop.toNat = (divKTrialCallV5DHi vTop).toNat * 2^32 + dL.toNat := by
    rw [hdL]; unfold divKTrialCallV5DHi divKTrialCallV5DLo; exact div128Quot_vTop_decomp vTop
  have h_U1_lt : U1.toNat < 2^32 := divKTrialCallV5Un1_lt_pow32 uLo
  have hvTop_pos : 0 < vTop.toNat := by omega
  have hrem_lt : (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat < vTop.toNat :=
    Nat.mod_lt _ hvTop_pos
  have h_alg : R.toNat * 2^32 + U1.toNat =
      Q.toNat * dL.toNat + (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat := by
    have h_Ndm : uHi.toNat * 2^32 + U1.toNat =
        Q.toNat * vTop.toNat + (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat := by
      have hd := Nat.div_add_mod (uHi.toNat * 2^32 + U1.toNat) vTop.toNat
      have hQV : Q.toNat * vTop.toNat =
          vTop.toNat * ((uHi.toNat * 2^32 + U1.toNat) / vTop.toNat) := by
        rw [h_Q_eq]; ring
      linarith
    have h_uHi_exp : uHi.toNat * 2^32 =
        Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + R.toNat * 2^32 := by
      calc uHi.toNat * 2^32
          = (Q.toNat * (divKTrialCallV5DHi vTop).toNat + R.toNat) * 2^32 := by
            congr 1; linarith [h_post]
        _ = Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + R.toNat * 2^32 := by ring
    have h_Q_vTop : Q.toNat * vTop.toNat =
        Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + Q.toNat * dL.toNat := by
      rw [h_vTop_eq]; ring
    linarith
  have h_comb : ((R <<< (32 : BitVec 6).toNat) ||| U1).toNat =
      (R.toNat % 2^32) * 2^32 + U1.toNat := by
    have h32 : (32 : BitVec 6).toNat = 32 := by decide
    rw [h32]; exact halfword_combine_truncated R U1 h_U1_lt
  have h_un21 : ((R <<< (32 : BitVec 6).toNat ||| U1) - Q * dL).toNat =
      ((R.toNat % 2^32) * 2^32 + U1.toNat + 2^64 - Q.toNat * dL.toNat) % 2^64 := by
    rw [BitVec.toNat_sub, h_comb, h_QdL_nw]; congr 1; omega
  rw [h_un21]
  set A := (R.toNat % 2^32) * 2^32 + U1.toNat with hA
  set B := Q.toNat * dL.toNat with hB
  set rem := (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat
  have h_decomp : A + (R.toNat / 2^32) * 2^64 = B + rem := by
    have hkey : R.toNat * 2^32 = (R.toNat / 2^32) * 2^64 + (R.toNat % 2^32) * 2^32 :=
      Nat_mul_pow32_split
    linarith [hA, hB, h_alg]
  have h_A_lt : A < 2^64 := by
    have := Nat.mod_lt R.toNat (show 0 < 2^32 from by norm_num); nlinarith [hA, h_U1_lt]
  have h_B_lt : B < 2^64 := by
    have h_Q_lt : Q.toNat < 2^32 := by
      have h_le := divKTrialCallV5Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
      have h_N_lt : uHi.toNat * 2^32 + U1.toNat < vTop.toNat * 2^32 := by nlinarith
      have : (uHi.toNat * 2^32 + U1.toNat) / vTop.toNat < 2^32 :=
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
      omega
    have h_dL_lt : dL.toNat < 2^32 := divKTrialCallV5DLo_lt_pow32 vTop
    nlinarith [hB]
  have hrem_lt64 : rem < 2^64 := lt_trans hrem_lt (by have := vTop.isLt; omega)
  have h_k_le_1 : R.toNat / 2^32 ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos (R.toNat / 2^32) with hk0 | hk1_pos
  · have hkB : A + 2^64 - B = rem + 2^64 := by omega
    rw [hkB, Nat.add_mod_right, Nat.mod_eq_of_lt hrem_lt64]
  · have hk1 : R.toNat / 2^32 = 1 := Nat.le_antisymm h_k_le_1 hk1_pos
    have hkB : A + 2^64 - B = rem := by omega
    rw [hkB, Nat.mod_eq_of_lt hrem_lt64]

end EvmAsm.Evm64
