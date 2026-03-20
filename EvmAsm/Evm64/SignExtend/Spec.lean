/-
  EvmAsm.Evm64.SignExtend.Spec

  Stack-level specification for EVM SIGNEXTEND.
  Main result: `evm_signextend_stack_spec` states that `evm_signextend` computes
  `EvmWord.signextend b x`.
-/

import EvmAsm.Evm64.SignExtend.Compose
import EvmAsm.Evm64.EvmWordArith

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Helpers
-- ============================================================================

private theorem regIs_to_regOwn'' (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Helper: lift a no-change raw-limb spec to evmWordIs form (with x6 framing). -/
private theorem signext_nochange_lift (sp base : Addr)
    (b x : EvmWord) (r5 r6 r10 : Word)
    (_hvalid : ValidMemRange sp 8)
    (hmain : cpsTriple base (base + 192) (signextCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ b.getLimb 0) ** ((sp + 8) ↦ₘ b.getLimb 1) **
       ((sp + 16) ↦ₘ b.getLimb 2) ** ((sp + 24) ↦ₘ b.getLimb 3) **
       ((sp + 32) ↦ₘ x.getLimb 0) ** ((sp + 40) ↦ₘ x.getLimb 1) **
       ((sp + 48) ↦ₘ x.getLimb 2) ** ((sp + 56) ↦ₘ x.getLimb 3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ b.getLimb 0) ** ((sp + 8) ↦ₘ b.getLimb 1) **
       ((sp + 16) ↦ₘ b.getLimb 2) ** ((sp + 24) ↦ₘ b.getLimb 3) **
       ((sp + 32) ↦ₘ x.getLimb 0) ** ((sp + 40) ↦ₘ x.getLimb 1) **
       ((sp + 48) ↦ₘ x.getLimb 2) ** ((sp + 56) ↦ₘ x.getLimb 3)))
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
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56]
      have w := sepConj_mono_right (regIs_to_regOwn'' .x6 _) h hq
      xperm_hyp w)
    hmain_f

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- **Main SIGNEXTEND theorem**: `evm_signextend` computes
    `EvmWord.signextend b x`. -/
theorem evm_signextend_stack_spec (sp base : Addr)
    (b x : EvmWord) (r5 r6 r10 : Word)
    (hvalid : ValidMemRange sp 8) :
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
    by_cases hhigh : b.getLimb 1 ||| b.getLimb 2 ||| b.getLimb 3 ≠ 0
    · exact signext_nochange_lift sp base b x r5 r6 r10 hvalid
        (signext_nochange_high_spec sp base _ _ _ _ _ _ _ _ r5 r10 hhigh hvalid)
        result hresult
    · have hhigh' : b.getLimb 1 ||| b.getLimb 2 ||| b.getLimb 3 = 0 :=
        Classical.byContradiction (fun h => hhigh h)
      have hlarge : BitVec.ult (b.getLimb 0) (signExtend12 (31 : BitVec 12)) = false := by
        have h_toNat := EvmWord.toNat_eq_getLimb0_of_high_zero b hhigh'
        rw [h_toNat] at hge
        have h31 : (signExtend12 (31 : BitVec 12)).toNat = 31 := by native_decide
        simp only [BitVec.ult, h31]
        cases h : decide ((b.getLimb 0).toNat < 31)
        · rfl
        · simp at h; omega
      exact signext_nochange_lift sp base b x r5 r6 r10 hvalid
        (signext_nochange_geq31_spec sp base _ _ _ _ _ _ _ _ r5 r10 hhigh' hlarge hvalid)
        result hresult
  · -- b < 31: body path
    push_neg at hge
    have hhigh : b.getLimb 1 ||| b.getLimb 2 ||| b.getLimb 3 = 0 :=
      EvmWord.high_limbs_zero_of_toNat_lt b (by omega)
    have hsmall : BitVec.ult (b.getLimb 0) (signExtend12 (31 : BitVec 12)) = true := by
      have hb_toNat := EvmWord.toNat_eq_getLimb0_of_high_zero b hhigh
      have h31 : (signExtend12 (31 : BitVec 12)).toNat = 31 := by native_decide
      simp only [BitVec.ult, h31]
      cases h : decide ((b.getLimb 0).toNat < 31)
      · simp at h; omega
      · rfl
    -- Use the body path theorem from Compose, lifting to evmWordIs
    have h_raw := signext_body_spec sp base b x r5 r6 r10 hvalid hhigh hsmall
    exact cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by
        simp only [evmWordIs] at hp
        have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
        have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
        have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
        simp only [ha40, ha48, ha56] at hp
        xperm_hyp hp)
      (fun h hq => by
        simp only [evmWordIs]
        have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
        have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
        have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
        simp only [ha40, ha48, ha56]
        xperm_hyp hq)
      h_raw

end EvmAsm.Rv64
