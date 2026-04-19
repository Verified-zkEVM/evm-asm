/-
  EvmAsm.Evm64.SignExtend.Spec

  Stack-level specification for EVM SIGNEXTEND.
  Main result: `evm_signextend_stack_spec` states that `evm_signextend` computes
  `EvmWord.signextend b x`.
-/

import EvmAsm.Evm64.SignExtend.Compose
import EvmAsm.Evm64.EvmWordArith
import EvmAsm.Evm64.SpAddr

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Helpers
-- ============================================================================

-- `regIs_to_regOwn` lives in `Rv64/SepLogic.lean` (shared).

/-- Helper: lift a no-change raw-limb spec to evmWordIs form (with x6 framing). -/
private theorem signext_nochange_lift (sp base : Word)
    (b x : EvmWord) (r5 r6 r10 : Word)
    (hmain : cpsTriple base (base + 192) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b.getLimbN 0) ** ((sp + 8) ↦ₘ b.getLimbN 1) **
       ((sp + 16) ↦ₘ b.getLimbN 2) ** ((sp + 24) ↦ₘ b.getLimbN 3) **
       ((sp + 32) ↦ₘ x.getLimbN 0) ** ((sp + 40) ↦ₘ x.getLimbN 1) **
       ((sp + 48) ↦ₘ x.getLimbN 2) ** ((sp + 56) ↦ₘ x.getLimbN 3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b.getLimbN 0) ** ((sp + 8) ↦ₘ b.getLimbN 1) **
       ((sp + 16) ↦ₘ b.getLimbN 2) ** ((sp + 24) ↦ₘ b.getLimbN 3) **
       ((sp + 32) ↦ₘ x.getLimbN 0) ** ((sp + 40) ↦ₘ x.getLimbN 1) **
       ((sp + 48) ↦ₘ x.getLimbN 2) ** ((sp + 56) ↦ₘ x.getLimbN 3)))
    (result : EvmWord) (hresult : result = x) :
    cpsTriple base (base + 192) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       evmWordIs sp b ** evmWordIs (sp + 32) x)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       evmWordIs sp b ** evmWordIs (sp + 32) result) := by
  subst hresult
  -- Frame x6 through the no-change spec, then weaken to regOwn
  have hmain_f := cpsTriple_frame_left _ _ _ _ _ (.x6 ↦ᵣ r6) (by pcFree) hmain
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      simp only [spAddr32_8, spAddr32_16, spAddr32_24] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      simp only [spAddr32_8, spAddr32_16, spAddr32_24]
      have w := sepConj_mono_right (regIs_to_regOwn .x6 _) h hq
      xperm_hyp w)
    hmain_f

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- **Main SIGNEXTEND theorem**: `evm_signextend` computes
    `EvmWord.signextend b x`. -/
theorem evm_signextend_stack_spec (sp base : Word)
    (b x : EvmWord) (r5 r6 r10 : Word) :
    let result := EvmWord.signextend b x
    cpsTriple base (base + 192) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       evmWordIs sp b ** evmWordIs (sp + 32) x)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       evmWordIs sp b ** evmWordIs (sp + 32) result) := by
  intro result
  by_cases hge : b.toNat ≥ 31
  · -- b >= 31: result = x (no change)
    have hresult : result = x := by simp [result, EvmWord.signextend_ge31 b x hge]
    by_cases hhigh : b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0
    · exact signext_nochange_lift sp base b x r5 r6 r10
        (signext_nochange_high_spec sp base _ _ _ _ _ _ _ _ r5 r10 hhigh)
        result hresult
    · have hhigh' : b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 = 0 :=
        Classical.byContradiction (fun h => hhigh h)
      have hlarge : BitVec.ult (b.getLimbN 0) (signExtend12 (31 : BitVec 12)) = false := by
        have h_toNat := EvmWord.toNat_eq_getLimb0_of_high_zero b hhigh'
        simp only [EvmWord.getLimb_as_getLimbN_0] at h_toNat
        rw [h_toNat] at hge
        have h31 : (signExtend12 (31 : BitVec 12)).toNat = 31 := by decide
        simp only [BitVec.ult, h31]
        cases h : decide ((b.getLimbN 0).toNat < 31)
        · rfl
        · simp at h; omega
      exact signext_nochange_lift sp base b x r5 r6 r10
        (signext_nochange_geq31_spec sp base _ _ _ _ _ _ _ _ r5 r10 hhigh' hlarge)
        result hresult
  · -- b < 31: body path
    push Not at hge
    have hhigh : b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 = 0 :=
      EvmWord.high_limbs_zero_of_toNat_lt b (by omega)
    have hsmall : BitVec.ult (b.getLimbN 0) (signExtend12 (31 : BitVec 12)) = true := by
      have hb_toNat := EvmWord.toNat_eq_getLimb0_of_high_zero b hhigh
      simp only [EvmWord.getLimb_as_getLimbN_0] at hb_toNat
      have h31 : (signExtend12 (31 : BitVec 12)).toNat = 31 := by decide
      simp only [BitVec.ult, h31]
      cases h : decide ((b.getLimbN 0).toNat < 31)
      · simp at h; omega
      · rfl
    -- Use the body path theorem from Compose, lifting to evmWordIs
    have h_raw := signext_body_spec sp base b x r5 r6 r10 hhigh hsmall
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        simp only [evmWordIs] at hp
        simp only [spAddr32_8, spAddr32_16, spAddr32_24] at hp
        simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                   EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3]
        xperm_hyp hp)
      (fun h hq => by
        simp only [evmWordIs]
        simp only [spAddr32_8, spAddr32_16, spAddr32_24]
        simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
                   EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at hq
        xperm_hyp hq)
      h_raw

end EvmAsm.Evm64
