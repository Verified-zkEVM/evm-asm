/-
  EvmAsm.Evm64.DivMod.Spec

  Stack-level specs for the 256-bit EVM DIV and MOD programs using evmWordIs.

  Currently covers:
  - Zero divisor path (b = 0): evm_div_bzero_stack_spec, evm_mod_bzero_stack_spec
  - Normal path (b ≠ 0): TODO (needs semantic correctness bridge: EvmWord.div_correct / mod_correct)
    Limb-level combined specs done: evm_div_bnz_full_spec, evm_mod_bnz_full_spec
-/

import EvmAsm.Evm64.DivMod.Compose
import EvmAsm.Evm64.DivMod.Compose.DivCombined
import EvmAsm.Evm64.DivMod.Compose.ModCombined
import EvmAsm.Evm64.EvmWordArith

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- DIV: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Weaken concrete register to existential ownership. -/
private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

/-- Stack-level DIV spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_div_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 1064) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.div a b)) := by
  subst hbz
  -- Normalize (0 : EvmWord).getLimb k to (0 : Word)
  have hg0 : (0 : EvmWord).getLimbN 0 = (0 : Word) := by native_decide
  have hg1 : (0 : EvmWord).getLimbN 1 = (0 : Word) := by native_decide
  have hg2 : (0 : EvmWord).getLimbN 2 = (0 : Word) := by native_decide
  have hg3 : (0 : EvmWord).getLimbN 3 = (0 : Word) := by native_decide
  -- Get the limb-level zero-path spec
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by native_decide
  have h_raw := evm_div_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or hvalid
  simp only [hg0, hg1, hg2, hg3] at h_raw
  -- Bridge: div a 0 = 0, getLimb (div a 0) k = 0
  have hr0 : (EvmWord.div a 0).getLimbN 0 = 0 := EvmWord.div_getLimb_zero_right a 0
  have hr1 : (EvmWord.div a 0).getLimbN 1 = 0 := EvmWord.div_getLimb_zero_right a 1
  have hr2 : (EvmWord.div a 0).getLimbN 2 = 0 := EvmWord.div_getLimb_zero_right a 2
  have hr3 : (EvmWord.div a 0).getLimbN 3 = 0 := EvmWord.div_getLimb_zero_right a 3
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      unfold evmWordIs at hp
      simp only [show (sp + 32 : Word) + 8 = sp + 40 from by bv_addr,
                 show (sp + 32 : Word) + 16 = sp + 48 from by bv_addr,
                 show (sp + 32 : Word) + 24 = sp + 56 from by bv_addr,
                 hg0, hg1, hg2, hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      unfold evmWordIs
      simp only [show (sp + 32 : Word) + 8 = sp + 40 from by bv_addr,
                 show (sp + 32 : Word) + 16 = sp + 48 from by bv_addr,
                 show (sp + 32 : Word) + 24 = sp + 56 from by bv_addr,
                 hr0, hr1, hr2, hr3]
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

-- ============================================================================
-- MOD: Zero divisor stack spec (b = 0 → result = 0)
-- ============================================================================

/-- Stack-level MOD spec for the zero divisor path: when b = 0, result is 0.
    Uses evmWordIs for the b-operand at sp+32. The a-operand at sp is untouched. -/
theorem evm_mod_bzero_stack_spec (sp base : Word)
    (a b : EvmWord) (v5 v10 : Word)
    (hbz : b = 0)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 1064) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (EvmWord.mod a b)) := by
  subst hbz
  have hg0 : (0 : EvmWord).getLimbN 0 = (0 : Word) := by native_decide
  have hg1 : (0 : EvmWord).getLimbN 1 = (0 : Word) := by native_decide
  have hg2 : (0 : EvmWord).getLimbN 2 = (0 : Word) := by native_decide
  have hg3 : (0 : EvmWord).getLimbN 3 = (0 : Word) := by native_decide
  have hlimbs_or : (0 : EvmWord).getLimbN 0 ||| (0 : EvmWord).getLimbN 1 |||
      (0 : EvmWord).getLimbN 2 ||| (0 : EvmWord).getLimbN 3 = (0 : Word) := by native_decide
  have h_raw := evm_mod_bzero_spec sp base
    ((0 : EvmWord).getLimbN 0) ((0 : EvmWord).getLimbN 1)
    ((0 : EvmWord).getLimbN 2) ((0 : EvmWord).getLimbN 3)
    v5 v10 hlimbs_or hvalid
  simp only [hg0, hg1, hg2, hg3] at h_raw
  have hr0 : (EvmWord.mod a 0).getLimbN 0 = 0 := EvmWord.mod_getLimb_zero_right a 0
  have hr1 : (EvmWord.mod a 0).getLimbN 1 = 0 := EvmWord.mod_getLimb_zero_right a 1
  have hr2 : (EvmWord.mod a 0).getLimbN 2 = 0 := EvmWord.mod_getLimb_zero_right a 2
  have hr3 : (EvmWord.mod a 0).getLimbN 3 = 0 := EvmWord.mod_getLimb_zero_right a 3
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by
      unfold evmWordIs at hp
      simp only [show (sp + 32 : Word) + 8 = sp + 40 from by bv_addr,
                 show (sp + 32 : Word) + 16 = sp + 48 from by bv_addr,
                 show (sp + 32 : Word) + 24 = sp + 56 from by bv_addr,
                 hg0, hg1, hg2, hg3] at hp
      xperm_hyp hp)
    (fun h hq => by
      unfold evmWordIs
      simp only [show (sp + 32 : Word) + 8 = sp + 40 from by bv_addr,
                 show (sp + 32 : Word) + 16 = sp + 48 from by bv_addr,
                 show (sp + 32 : Word) + 24 = sp + 56 from by bv_addr,
                 hr0, hr1, hr2, hr3]
      have w0 := sepConj_mono_left (regIs_to_regOwn .x5 _) h
        ((congrFun (show _ =
          ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
           (.x12 ↦ᵣ (sp + 32)) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
           ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
          from by xperm) h).mp hq)
      have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x10 _)) h w0
      exact (congrFun (show _ =
        ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x10) ** (.x0 ↦ᵣ (0 : Word)) **
         ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) **
         ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)))
        from by xperm) h).mp w1)
    h_raw

end EvmAsm.Rv64
