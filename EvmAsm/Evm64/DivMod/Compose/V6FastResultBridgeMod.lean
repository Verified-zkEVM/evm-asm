/-
  EvmAsm.Evm64.DivMod.Compose.V6FastResultBridgeMod

  MOD result reconciliation for the v6 fast arm.  The MOD fast path stores the
  denormalized single-limb remainder `v6chainR0 >>> s` at `sp+32` (and zeros at
  `sp+40/48/56`).  This file proves those four cells assemble into
  `evmWordIs (sp+32) (EvmWord.mod a b)`, via the chain-model remainder bridge
  `v6chainR0_eq_model` (body window `v6nU…` = v5 model normalized window) and the
  single-limb remainder correctness `fullDivN1V5_remainder_eq_mod_of_shape`
  (shift≠0) / `fullModN1RemainderWordShift0V5_eq_mod_of_shape` (shift=0).

  Brick 4 of the MOD v6 fast arm; mirror of `Compose/V6FastResultBridge.lean`
  (`fast_div_result_word_{shiftNz,shift0}`), reading the remainder where DIV reads
  the quotient.
-/

import EvmAsm.Evm64.DivMod.Compose.V6BodyModelBridge
import EvmAsm.Evm64.DivMod.Compose.V6Shift0ChainBridge
import EvmAsm.Evm64.DivMod.Spec.N1V5ModRemainder
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0ModRemainder

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

variable (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word)

-- ============================================================================
-- Body-window remainder R0 = v5 model remainder (shift≠0).
-- ============================================================================

/-- Body window final remainder `v6chainR0` = v5 model normalized remainder
    `(fullDivN1R0V5 …).2.1`.  Mirror of `v6chainQ0_v6n_eq_model`. -/
theorem v6chainR0_v6n_eq_model
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0)
              (v6nU0 a0 b0) (v6nD b0) =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 := by
  rw [v6nU4_eq_normU a0, v6nU3_eq_normU a0, v6nU2_eq_normU a0, v6nU1_eq_normU a0,
      v6nU0_eq_normU a0, v6nD_eq_normV (b1 := b1) (b2 := b2) (b3 := b3),
      v6chainR0_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz]

/-- `s % 64 = s` for the CLZ shift (it is `< 64`). -/
private theorem clz_shift_mod64 (b0 : Word) :
    (clzResult b0).1.toNat % 64 = (clzResult b0).1.toNat := by
  apply Nat.mod_eq_of_lt
  have := clzResult_fst_toNat_le b0
  omega

-- ============================================================================
-- Per-limb MOD remainder facts (shift≠0): fast-path stored remainder = mod limb.
-- ============================================================================

theorem v6n_mod_getLimbN_0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0)
                   (v6nU0 a0 b0) (v6nD b0)) >>> ((clzResult b0).1.toNat % 64) := by
  have hmodword := fullDivN1V5_remainder_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz
  have key : (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> (fullDivN1Shift b0).toNat :=
    ((congrArg (fun w => w.getLimbN 0) hmodword).symm).trans EvmWord.getLimbN_fromLimbs_0
  rw [key, v6chainR0_v6n_eq_model a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz,
      clz_shift_mod64]
  simp only [fullDivN1Shift]

theorem v6n_mod_getLimbN_high
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 1 = 0
    ∧ (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 2 = 0
    ∧ (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 3 = 0 := by
  have hmodword := fullDivN1V5_remainder_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz
  refine ⟨?_, ?_, ?_⟩
  · exact ((congrArg (fun w => w.getLimbN 1) hmodword).symm).trans EvmWord.getLimbN_fromLimbs_1
  · exact ((congrArg (fun w => w.getLimbN 2) hmodword).symm).trans EvmWord.getLimbN_fromLimbs_2
  · exact ((congrArg (fun w => w.getLimbN 3) hmodword).symm).trans EvmWord.getLimbN_fromLimbs_3

/-- **shift≠0 MOD result reconciliation.** The single denormalized remainder limb
    `v6chainR0 >>> s` at `sp+32` (high cells zero) forms
    `evmWordIs (sp+32) (EvmWord.mod a b)`. -/
theorem fast_mod_result_word_shiftNz
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    evmWordIs (sp + 32)
        (EvmWord.mod
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    = (((sp + 32) ↦ₘ (v6chainR0 (v6nU4 a3 b0) (v6nU3 a3 a2 b0) (v6nU2 a2 a1 b0) (v6nU1 a1 a0 b0)
                                (v6nU0 a0 b0) (v6nD b0)) >>> ((clzResult b0).1.toNat % 64)) **
       ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  obtain ⟨h1, h2, h3⟩ := v6n_mod_getLimbN_high a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  rw [evmWordIs_sp32_unfold]
  congr 1
  · exact congrArg (fun w => (sp + 32) ↦ₘ w)
      (v6n_mod_getLimbN_0 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  congr 1
  · exact congrArg (fun w => (sp + 40) ↦ₘ w) h1
  congr 1
  · exact congrArg (fun w => (sp + 48) ↦ₘ w) h2
  · exact congrArg (fun w => (sp + 56) ↦ₘ w) h3

-- ============================================================================
-- shift=0 arm.
-- ============================================================================

/-- Shift=0 body-window final remainder `v6chainR0` = v5 model remainder
    `(fullN1S0 …).2.1`.  Mirror of `v6chainR1_shift0_eq_model` at digit 0. -/
theorem v6chainR0_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainR0 0 a3 a2 a1 a0 b0 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1 := by
  have hnorm : b0.toNat ≥ 2^63 := b0_ge_pow63_of_clz_zero b0 hb0nz hclz
  obtain ⟨hz2, hz3, hz4⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ b0
    (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz)
  have hcall0 : (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1.toNat < b0.toNat := by
    have h := s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz
    rw [hz2, hz3, hz4] at h; simpa [val256] using h
  rw [v6chainR0, v6chainQ0_shift0_eq_model a0 a1 a2 a3 b0 hb0nz hclz]
  unfold fullN1S0
  simp only [← iterN1V5_true]
  rw [hz2, hz3, hz4, iterN1V5_true_quot_eq_div128_of_v0_norm_call b0 a0 _ hnorm hcall0,
      iterN1V5_true_rem_eq_of_v0_norm_call b0 a0 _ hnorm hcall0]

theorem v6n_mod_getLimbN_shift0_0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0)) >>> ((clzResult b0).1.toNat % 64) := by
  have hb0nz : b0 ≠ 0 := by rw [hb1z, hb2z, hb3z] at hbnz; simpa using hbnz
  have hmw := fullModN1RemainderWordShift0V5_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hclz
  have key : (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1 :=
    ((congrArg (fun w => w.getLimbN 0) hmw).symm).trans
      (by delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_0)
  rw [key, v6nD_eq_self_shift0 b0 hclz,
      v6chainR0_shift0_eq_model a0 a1 a2 a3 b0 hb0nz hclz, hclz]
  simp

theorem v6n_mod_getLimbN_shift0_high
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 1 = 0
    ∧ (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 2 = 0
    ∧ (EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 3 = 0 := by
  have hb0nz : b0 ≠ 0 := by rw [hb1z, hb2z, hb3z] at hbnz; simpa using hbnz
  have hmw := fullModN1RemainderWordShift0V5_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hclz
  obtain ⟨hc1, hc2, hc3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ b0
    (s0_rem_lt_shift0 a0 a1 a2 a3 b0 hb0nz hclz)
  refine ⟨?_, ?_, ?_⟩
  · refine (((congrArg (fun w => w.getLimbN 1) hmw).symm).trans
      (by delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_1)).trans hc1
  · refine (((congrArg (fun w => w.getLimbN 2) hmw).symm).trans
      (by delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_2)).trans hc2
  · refine (((congrArg (fun w => w.getLimbN 3) hmw).symm).trans
      (by delta fullModN1RemainderWordShift0V5; exact EvmWord.getLimbN_fromLimbs_3)).trans hc3

/-- **shift=0 MOD result reconciliation.** As `fast_mod_result_word_shiftNz`, for
    the already-normalized lane whose remainder cell holds `v6chainR0` of the
    `(0, a3, a2, a1, a0)` window (denorm by `s = 0` is the identity). -/
theorem fast_mod_result_word_shift0
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    evmWordIs (sp + 32)
        (EvmWord.mod
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3))
    = (((sp + 32) ↦ₘ (v6chainR0 (0 : Word) a3 a2 a1 a0 (v6nD b0)) >>> ((clzResult b0).1.toNat % 64)) **
       ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word))) := by
  obtain ⟨h1, h2, h3⟩ := v6n_mod_getLimbN_shift0_high a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz
  rw [evmWordIs_sp32_unfold]
  congr 1
  · exact congrArg (fun w => (sp + 32) ↦ₘ w)
      (v6n_mod_getLimbN_shift0_0 a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)
  congr 1
  · exact congrArg (fun w => (sp + 40) ↦ₘ w) h1
  congr 1
  · exact congrArg (fun w => (sp + 48) ↦ₘ w) h2
  · exact congrArg (fun w => (sp + 56) ↦ₘ w) h3

end EvmAsm.Evm64
