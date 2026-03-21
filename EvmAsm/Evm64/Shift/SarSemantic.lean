/-
  EvmAsm.Evm64.Shift.SarSemantic

  256-bit shift semantics: the main SAR theorem connecting the RISC-V
  implementation to EvmWord-level arithmetic shift right.

  Main result: `evm_sar_stack_spec` states that `evm_sar` computes
  `if shift.toNat ≥ 256 then fromLimbs (fun _ => sshiftRight (value.getLimb 3) 63)
   else sshiftRight value shift.toNat`.
-/

import EvmAsm.Evm64.Shift.SarCompose

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Helpers
-- ============================================================================

private theorem regIs_to_regOwn' (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Weaken: sign-fill result + frame regs → evmWordIs sign_fill + regOwn. -/
private theorem sar_sign_fill_evmWord_weaken (sp : Addr) (s0 s1 s2 s3 r6 r7 r11 sign_ext : Word) :
    ∀ h,
    ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ sign_ext) ** ((sp + 40) ↦ₘ sign_ext) **
     ((sp + 48) ↦ₘ sign_ext) ** ((sp + 56) ↦ₘ sign_ext) **
     (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) h →
    ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ sign_ext) ** ((sp + 40) ↦ₘ sign_ext) **
     ((sp + 48) ↦ₘ sign_ext) ** ((sp + 56) ↦ₘ sign_ext)) h := by
  intro h hp
  have hp' := (congrFun (show _ = ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 8) ↦ₘ s1) ** ((sp + 16) ↦ₘ s2) ** ((sp + 24) ↦ₘ s3) **
     ((sp + 32) ↦ₘ sign_ext) ** ((sp + 40) ↦ₘ sign_ext) **
     ((sp + 48) ↦ₘ sign_ext) ** ((sp + 56) ↦ₘ sign_ext)) from by xperm) h).mp hp
  have w1 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn' .x6 _))))) h hp'
  have w2 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn' .x7 _)))))) h w1
  have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (regIs_to_regOwn' .x11 _))))))) h w2
  exact w3

-- ============================================================================
-- Sign-fill helper: evmWordIs-level composition
-- ============================================================================

/-- Compose one sign-fill case into evmWordIs form.
    Shared proof structure for both high-limbs and s0≥256 cases. -/
private theorem sar_sign_fill_lift (sp base : Addr)
    (shift value : EvmWord) (r5 r6 r7 r10 r11 : Word)
    (_hvalid : ValidMemRange sp 8)
    (hmain : cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ value.getLimb 0) ** ((sp + 40) ↦ₘ value.getLimb 1) **
       ((sp + 48) ↦ₘ value.getLimb 2) ** ((sp + 56) ↦ₘ value.getLimb 3))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
       ((sp + 40) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
       ((sp + 48) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
       ((sp + 56) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63)))
    (result : EvmWord)
    (hresult : result = EvmWord.fromLimbs (fun _ => BitVec.sshiftRight (value.getLimb 3) 63)) :
    cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) value)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) result) := by
  subst hresult
  have hframed := cpsTriple_frame_left base (base + 380) _ _ _
    ((.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11))
    (by pcFree) hmain
  have hflat : cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ value.getLimb 0) ** ((sp + 40) ↦ₘ value.getLimb 1) **
       ((sp + 48) ↦ₘ value.getLimb 2) ** ((sp + 56) ↦ₘ value.getLimb 3) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
       ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
       ((sp + 32) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
       ((sp + 40) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
       ((sp + 48) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
       ((sp + 56) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      hframed
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, EvmWord.getLimb_fromLimbs_const]
      have ha40 : (sp + 32 : Addr) + 8 = sp + 40 := by bv_omega
      have ha48 : (sp + 32 : Addr) + 16 = sp + 48 := by bv_omega
      have ha56 : (sp + 32 : Addr) + 24 = sp + 56 := by bv_omega
      simp only [ha40, ha48, ha56]
      have hq' : ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
         (sp ↦ₘ shift.getLimb 0) ** ((sp + 8) ↦ₘ shift.getLimb 1) **
         ((sp + 16) ↦ₘ shift.getLimb 2) ** ((sp + 24) ↦ₘ shift.getLimb 3) **
         ((sp + 32) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
         ((sp + 40) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
         ((sp + 48) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
         ((sp + 56) ↦ₘ BitVec.sshiftRight (value.getLimb 3) 63) **
         (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11)) h := by xperm_hyp hq
      have hw := sar_sign_fill_evmWord_weaken sp _ _ _ _ r6 r7 r11 _ h hq'
      xperm_hyp hw)
    hflat

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- **Main SAR theorem**: `evm_sar` computes the 256-bit arithmetic right shift.
    Given shift and value as EvmWords on the stack, produces:
    - `fromLimbs (fun _ => sshiftRight (value.getLimb 3) 63)` when shift ≥ 256
    - `sshiftRight value shift.toNat` when shift < 256 -/
theorem evm_sar_stack_spec (sp base : Addr)
    (shift value : EvmWord) (r5 r6 r7 r10 r11 : Word)
    (hvalid : ValidMemRange sp 8) :
    let result := if shift.toNat ≥ 256
        then EvmWord.fromLimbs (fun _ => BitVec.sshiftRight (value.getLimb 3) 63)
        else BitVec.sshiftRight value shift.toNat
    cpsTriple base (base + 380) (sarCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) value)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (regOwn .x6) ** (regOwn .x7) ** (regOwn .x11) **
       evmWordIs sp shift ** evmWordIs (sp + 32) result) := by
  intro result
  -- Case split: shift ≥ 256 or shift < 256
  by_cases hge : shift.toNat ≥ 256
  · -- shift ≥ 256: result = sign extension
    have hresult : result = EvmWord.fromLimbs (fun _ => BitVec.sshiftRight (value.getLimb 3) 63) := by
      simp [result, hge]
    -- Sub-case: high limbs nonzero or s0 ≥ 256
    by_cases hhigh : shift.getLimb 1 ||| shift.getLimb 2 ||| shift.getLimb 3 ≠ 0
    · exact sar_sign_fill_lift sp base shift value r5 r6 r7 r10 r11 hvalid
        (evm_sar_sign_fill_high_spec sp base _ _ _ _ _ _ _ _ r5 r10 hhigh hvalid)
        result hresult
    · have hhigh' : shift.getLimb 1 ||| shift.getLimb 2 ||| shift.getLimb 3 = 0 :=
        Classical.byContradiction (fun h => hhigh h)
      -- High limbs = 0 but shift ≥ 256 → s0 ≥ 256
      have hlarge : BitVec.ult (shift.getLimb 0) (signExtend12 (256 : BitVec 12)) = false := by
        have h_toNat := EvmWord.toNat_eq_getLimb0_of_high_zero shift hhigh'
        rw [h_toNat] at hge
        have h256 : (signExtend12 (256 : BitVec 12)).toNat = 256 := by native_decide
        simp only [BitVec.ult, h256]
        cases h : decide ((shift.getLimb 0).toNat < 256)
        · rfl
        · simp at h; omega
      exact sar_sign_fill_lift sp base shift value r5 r6 r7 r10 r11 hvalid
        (evm_sar_sign_fill_large_spec sp base _ _ _ _ _ _ _ _ r5 r10 hhigh' hlarge hvalid)
        result hresult
  · -- shift < 256: result = sshiftRight value shift.toNat
    have hlt : shift.toNat < 256 := Nat.lt_of_not_le hge
    -- High limbs must be 0 when shift < 256
    have hhigh_zero : shift.getLimb 1 ||| shift.getLimb 2 ||| shift.getLimb 3 = 0 :=
      EvmWord.high_limbs_zero_of_toNat_lt shift (by omega)
    -- s0 < 256
    have hlt_s0 : BitVec.ult (shift.getLimb 0) (signExtend12 (256 : BitVec 12)) = true := by
      have h_toNat := EvmWord.toNat_eq_getLimb0_of_high_zero shift hhigh_zero
      rw [h_toNat] at hlt
      have h256 : (signExtend12 (256 : BitVec 12)).toNat = 256 := by native_decide
      simp only [BitVec.ult, h256]
      cases h : decide ((shift.getLimb 0).toNat < 256)
      · simp at h; omega
      · rfl
    rw [show result = BitVec.sshiftRight value shift.toNat from by
      simp [result, show ¬(shift.toNat ≥ 256) from hge]]
    exact evm_sar_body_evmWord_spec sp base shift value r5 r6 r7 r10 r11
      hvalid hhigh_zero hlt_s0 hlt

end EvmAsm.Rv64
